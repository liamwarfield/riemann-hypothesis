module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelLessSecondOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKLt2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem lastRow_eq (hk : 1 ≤ k) (y : GA E k) (c : Fin k) :
    lastRow y c = y.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp only
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lastRow_mir (hk : 1 ≤ k) (p y : GA E k) (hp : Mir (k - 1) p) : lastRow (p * y) = lastRow y := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul, Matrix.mul_apply]
  have h1 : ∀ j, p.val ⟨k - 1, by omega⟩ j = (1 : Matrix (Fin k) (Fin k) (Ad E)) ⟨k - 1, by omega⟩ j :=
    fun j => hp _ _ (Or.inl le_rfl)
  simp only [h1, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp

omit [NumberField E] in
theorem isMir_emb {m : ℕ} (ιE : GL (Fin k) E →* GL (Fin m) E) (h : IsEmb ιE) (γ : GL (Fin k) E) :
    IsMir k (ιE γ) := by
  intro i c hic
  rw [h γ, embM, Matrix.of_apply, dite_eq_right (by omega)]

end PKLt2

theorem kernel_less_second_of : D0 → N0 → H0 → RowsInCompactSet → K1 → CornerEmbedding → TransformsEmbedding → FourierSeriesColumn → ShortRowsEmbedding → K6 → KLt2 := by
  intro hD0 hN0 hH0 hG5 hK1 hK5e hK5a hK5b hK5c hK6 E _ _ _ m k hk hkm ψ hψ S hS ι hι α α' φ' hsec U φ hprep
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -⟩ := hD0 E k
  obtain ⟨hFgood, hpT, -, -, hsupp, hbd⟩ := hK5a E m k hk hkm ψ hψ ι hι φ hprep.good
  obtain ⟨C6, hC6c, hC6⟩ := hK6 E m k hk hkm ψ hψ S hS ι hι α (m ^ 3) U φ hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, hNlast⟩ := hN0 E k k hk le_rfl
  obtain ⟨hhtpos, -, -, -, hB5, -, -⟩ := hH0 E k
  obtain ⟨-, hdminpos, -⟩ := hK1 E m (by omega)
  obtain ⟨hιc, -, -, -, -, -, hιrat, -⟩ := (hK5e E m k hkm.le).2 ι hι
  obtain ⟨ιE, hιE⟩ := (hK5e E m k hkm.le).1 E
  have hrow : ∀ (g : GA E k) (ξ : RowT E k k),
      pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 →
      lastRow (ratGL E k (gam ξ) * g) ∈ C6 := by
    intro g ξ hne
    obtain ⟨p, hp, hw⟩ := hsupp _ hne
    have := hC6 _ hw
    rwa [PKLt2.lastRow_mir hk _ _ hp] at this
  have hfin : ∀ g : GA E k,
      {ξ : RowT E k k | colT ψ k (pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ))
        (ι (ratGL E k (gam ξ) * g)) ≠ 0}.Finite := by
    intro g
    exact ((hG5 E k hk C6 hC6c).1 g).subset fun ξ hξ => hrow g ξ (by rw [hpT]; exact hξ)
  have hsumF : ∀ g, sumF (fun g => pT ψ k (m - k) (φ : GA E m → ℂ) (ι g)) g =
      pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) := by
    intro g
    rw [hpT]
    exact (hK5b E m k hk hkm ψ hψ ι hι _ hFgood g).2 (hfin g)
  have hFb : ∀ x, ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) x‖ ≤ ‖φ‖ := fun x =>
    hbd (k + 1) x ‖φ‖ (by omega) (by omega) fun u _ => φ.norm_coe_le_norm _
  have hcpow : ∀ g : GA E k, ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ = Dt g ^ (-(((m : ℝ) - k) / 2)) := by
    intro g
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hDpos g)]
    congr 1
    simp
  have hcont : Continuous fun g : GA E k => pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) *
      conj (φ' g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) := by
    refine ((hFgood.cont.comp hιc).mul (Complex.continuous_conj.comp φ'.continuous)).mul ?_
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  simp_rw [hsumF]
  refine ⟨hcont.measurable, measurable_zero, ?_, fun _ _ => rfl, fun _ _ => rfl, ⟨0, fun _ => by simp⟩, ?_, ?_⟩
  · intro γ g
    dsimp only
    rw [map_mul ι, hιrat ιE hιE γ, hFgood.left _ (PKLt2.isMir_emb ιE hιE γ), hsec.inv γ g, hDmul, hDrat, one_mul]
  · intro M
    obtain ⟨C₂, hC₂⟩ := hsec.dec (k * M)
    obtain ⟨B, hB⟩ := hB5 C6 hC6c
    refine ⟨‖φ‖ * max C₂ 0 * max B 0 ^ (k * M), fun g hg => ?_⟩
    have hD := hDpos g
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hnorm : ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖ ≤ 1 := by
      rw [hcpow]
      apply Real.rpow_le_one_of_one_le_of_nonpos hg
      have : (k : ℝ) < m := by exact_mod_cast hkm
      linarith
    have hnn : 0 ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by positivity
    by_cases hz : pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g) = 0
    · rw [hz, zero_mul, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _)) (by positivity))
        (by positivity)
    obtain ⟨ξ, hξ⟩ : ∃ ξ : RowT E k k, pT ψ k (m - k) (φ : GA E m → ℂ) (ι (ratGL E k (gam ξ) * g)) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      apply hz
      rw [← hsumF g, sumF]
      simp only [hcon, tsum_zero]
    have hlr := hrow g ξ hξ
    rw [hNlast ξ g] at hlr
    have hht := hB g ξ.1 ξ.2.1 hlr
    have hp := hhtpos g ξ.1 ξ.2.1
    have hht2 : ht g ξ.1 ≤ max B 0 / Dt g ^ ((k : ℝ)⁻¹) := by
      unfold ht
      gcongr
      exact hht.trans (le_max_left _ _)
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) = Dt g ^ M := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul,
        Real.rpow_natCast]
    have hpow : ht g ξ.1 ^ (k * M) ≤ max B 0 ^ (k * M) * (Dt g ^ M)⁻¹ := by
      calc ht g ξ.1 ^ (k * M) ≤ (max B 0 / Dt g ^ ((k : ℝ)⁻¹)) ^ (k * M) := pow_le_pow_left₀ hp.le hht2 _
        _ = _ := by rw [div_pow, hDk, div_eq_mul_inv]
    have hφ' : ‖φ' g‖ ≤ max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹) :=
      (hC₂ g ξ.1 ξ.2.1).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * ‖(Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))‖
        ≤ ‖φ‖ * (max C₂ 0 * (max B 0 ^ (k * M) * (Dt g ^ M)⁻¹)) * 1 :=
          mul_le_mul (mul_le_mul (hFb _) hφ' (norm_nonneg _) (norm_nonneg _)) hnorm (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hφ'))
      _ = _ := by ring
  · obtain ⟨C5, hC5⟩ := hK5c E m k hk hkm ι hι
    obtain ⟨Cφ, hCφ⟩ := hprep.dec
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    have hkm' : (k : ℝ) < m := by exact_mod_cast hkm
    have hm0 : (m : ℝ) ≠ 0 := by linarith
    have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
    have he : (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) = (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      push_cast
      field_simp
      ring
    have hmle : (m : ℝ) ≤ (m : ℝ) ^ 2 / ((m : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have hexp : 0 ≤ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ) + -(((m : ℝ) - k) / 2) := by
      rw [he]
      linarith
    refine ⟨max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖, fun g hg => ?_⟩
    have hD := hDpos g
    have hFs : ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) *
        Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) := by
      refine hbd (k + 1) (ι g) _ (by omega) (by omega) fun u hu => ?_
      have hdm := (hC5 g u).2 hu
      have hpos := hdminpos (u * ι g)
      have hw0 : 0 ≤ wt (m ^ 3) (u * ι g) := pow_nonneg (le_min zero_le_one hpos.le) _
      calc ‖φ (u * ι g)‖ ≤ Cφ * wt (m ^ 3) (u * ι g) := hCφ _
        _ ≤ max Cφ 0 * wt (m ^ 3) (u * ι g) := mul_le_mul_of_nonneg_right (le_max_left _ _) hw0
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          unfold wt
          calc min 1 (dmin (u * ι g)) ^ (m ^ 3)
              ≤ (max C5 0 * Dt g ^ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹)) ^ (m ^ 3) :=
                pow_le_pow_left₀ (le_min zero_le_one hpos.le) ((min_le_right _ _).trans (hdm.trans
                  (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hD.le _)))) _
            _ = _ := by rw [mul_pow, ← Real.rpow_natCast (Dt g ^ _), ← Real.rpow_mul hD.le]
    have hrp : Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) * Dt g ^ (-(((m : ℝ) - k) / 2)) ≤ 1 := by
      rw [← Real.rpow_add hD]
      exact Real.rpow_le_one hD.le hg.le hexp
    have hφ'b : ‖φ' g‖ ≤ ‖φ'‖ := φ'.norm_coe_le_norm g
    have hA : 0 ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ :=
      mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _)) (norm_nonneg _)
    rw [Pi.zero_apply, sub_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le, norm_mul, norm_mul,
      RCLike.norm_conj, hcpow, mul_comm _ (Dt g)]
    apply mul_le_mul_of_nonneg_left _ hD.le
    calc ‖pT ψ (k + 1) (m - (k + 1)) (φ : GA E m → ℂ) (ι g)‖ * ‖φ' g‖ * Dt g ^ (-(((m : ℝ) - k) / 2))
        ≤ max Cφ 0 * (max C5 0 ^ (m ^ 3) * Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ))) *
            ‖φ'‖ * Dt g ^ (-(((m : ℝ) - k) / 2)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hD.le _)
          exact mul_le_mul hFs hφ'b (norm_nonneg _) ((norm_nonneg _).trans hFs)
      _ = max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * (Dt g ^ ((((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹) * ((m ^ 3 : ℕ) : ℝ)) *
            Dt g ^ (-(((m : ℝ) - k) / 2))) := by ring
      _ ≤ max Cφ 0 * max C5 0 ^ (m ^ 3) * ‖φ'‖ * 1 := mul_le_mul_of_nonneg_left hrp hA
      _ = _ := mul_one _

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.KernelEqualitySecondOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKEq2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem continuous_lastRow : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  unfold lastRow
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Continuous.matrix_elem Units.continuous_val i c
  · exact continuous_const

theorem lastRow_mir (p : GL (Fin k) E) (hp : IsMir (k - 1) p) (g : GA E k) :
    lastRow (ratGL E k p * g) = lastRow g := by
  funext c
  unfold lastRow
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have hrow : ∀ j, (ratGL E k p).val i j = (1 : Matrix (Fin k) (Fin k) (Ad E)) i j := by
      intro j
      have := hp i j (Or.inl (by omega))
      simp only [ratGL] at *
      simp [this, Matrix.one_apply]
    rw [Units.val_mul, Matrix.mul_apply]
    simp_rw [hrow]
    simp [Matrix.one_apply]
  · rfl

theorem measurable_sumF [Countable (RowT E k k)] {f : GA E k → ℂ} (hf : Continuous f)
    (hfin : ∀ g, {ξ : RowT E k k | f (ratGL E k (gam ξ) * g) ≠ 0}.Finite) : Measurable (sumF f) := by
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (RowT E k k)))
    (f := fun T g => ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g)) (fun T => ?_) ?_
  · exact Finset.measurable_sum _ fun ξ _ => (hf.comp (continuous_const.mul continuous_id)).measurable
  · rw [tendsto_pi_nhds]
    intro g
    have e : ∀ T : Finset (RowT E k k), (hfin g).toFinset ⊆ T →
        ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g) = sumF f g := by
      intro T hT
      unfold sumF
      rw [tsum_eq_sum (s := T)]
      intro b hb
      by_contra h
      exact hb (hT ((hfin g).mem_toFinset.2 h))
    exact tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨_, fun T hT => (e T hT).symm⟩)

theorem fin_bd {X : ℂ} {B C x y : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : ‖X‖ₑ ≤ ENNReal.ofReal B * ENNReal.ofReal (C * x)) : ‖X‖ ≤ B * max C 0 * y := by
  rw [← ENNReal.ofReal_mul hB, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff'] at h
  have h0 : C * x ≤ max C 0 * y :=
    calc C * x ≤ max C 0 * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ max C 0 * y := mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
  have h1 : B * (C * x) ≤ B * max C 0 * y := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h0 hB
  have h2 : 0 ≤ B * max C 0 * y := mul_nonneg (mul_nonneg hB (le_max_right _ _)) (hx.trans hxy)
  rcases h with h | h <;> linarith [norm_nonneg X]

theorem enorm_conj' (z : ℂ) : ‖conj z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]

end PKEq2

open PKEq2 in
theorem kernel_equality_second_of : D0 → N0 → H0 → ThetaDecaying → RowsInCompactSet → PoissonCutoffFormula → KEq2 := by
  intro hD0 hN0 hH0 hG4t hG5t hK12 E _ _ _ k hk ψ hψ S α' φ' hφ' U φ η s hcut hinv hcen
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -, hDinv, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, -, -, hcount, -, hperm, -⟩ := hN0 E k k hk le_rfl
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hinv' : ∀ γ g, φ (ratGL E k γ * g) = φ g := hinv
  have hinv2 : ∀ γ g, φ' (ratGL E k γ * g) = φ' g := hφ'.inv
  have hp1 : ∀ g : GA E k, (Dt g : ℂ) ^ (-(((k : ℂ) - k) / 2)) = 1 := fun g => by simp
  set V : (Fin k → Ad E) → XB E k := fun y => (η y : ℂ) • Rt E k (s y)⁻¹ φ with hV
  set F : GA E k → ℂ := fun g => (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹) with hF
  have hVc : Continuous V := hcut.contV
  have hVcpt : HasCompactSupport V := by
    have h1 : HasCompactSupport (fun y => (η y : ℂ)) := hcut.cpt.comp_left (g := Complex.ofReal) (by simp)
    exact h1.smul_right (f' := fun y => Rt E k (s y)⁻¹ φ)
  have hFV : ∀ x, F x = V (lastRow x) x := fun x => by simp [hF, hV]
  have hFc : Continuous F := by
    have : F = fun x => (V (lastRow x), x).1 (V (lastRow x), x).2 := funext hFV
    rw [this]
    exact continuous_eval.comp ((hVc.comp continuous_lastRow).prodMk continuous_id)
  have hFmir : ∀ p, IsMir (k - 1) p → ∀ x, F (ratGL E k p * x) = F x := by
    intro p hp x
    simp only [hF, lastRow_mir p hp, mul_assoc, hinv']
  have hsumInv : ∀ γ g, sumF F (ratGL E k γ * g) = sumF F g := by
    intro γ g
    obtain ⟨e, he⟩ := hperm γ
    unfold sumF
    rw [← e.tsum_eq (fun ξ => F (ratGL E k (gam ξ) * g))]
    refine tsum_congr fun ξ => ?_
    obtain ⟨p, hp, hpe⟩ := he ξ
    rw [← mul_assoc, ← map_mul, hpe, map_mul, mul_assoc, hFmir p hp]
  have hcpt : IsCompact (tsupport η) := hcut.cpt
  have hFzero : ∀ x, lastRow x ∉ tsupport η → F x = 0 := by
    intro x hx
    simp [hF, image_eq_zero_of_notMem_tsupport hx]
  have hfin : ∀ g, {ξ : RowT E k k | F (ratGL E k (gam ξ) * g) ≠ 0}.Finite := by
    intro g
    refine ((hG5t E k hk (tsupport η) hcpt).1 g).subset fun ξ hξ => ?_
    by_contra h
    exact hξ (hFzero _ h)
  have hSmeas : Measurable (sumF F) := measurable_sumF hFc hfin

  have hint : Integrable V (vecMeasure E (Fin k)) := hVc.integrable_of_hasCompactSupport hVcpt
  set W : XB E k := ∫ y, V y ∂vecMeasure E (Fin k) with hW
  have hI : ∀ g, (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k)) = W g := by
    intro g
    have := ContinuousLinearMap.integral_comp_comm (BoundedContinuousFunction.evalCLM ℂ g) hint
    rw [hW, ← BoundedContinuousFunction.evalCLM_apply (𝕜 := ℂ), ← this]
    simp [hV]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hp1, mul_one]
    exact hSmeas.mul (Complex.continuous_conj.comp φ'.continuous).measurable
  · simp only [hI]
    exact (W.continuous.mul (Complex.continuous_conj.comp φ'.continuous)).measurable
  · intro γ g
    simp only [hp1, mul_one]
    rw [hsumInv γ g, hinv2]
  · intro γ g
    simp only [mul_assoc, hinv', hinv2]
  · intro t g
    simp only [mul_assoc, hcen, hφ'.cen]
  · refine ⟨‖W‖ * ‖φ'‖, fun g => ?_⟩
    rw [hI, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (W.norm_coe_le_norm g) (φ'.norm_coe_le_norm g) (norm_nonneg _) (norm_nonneg _)
  · intro M
    obtain ⟨B, hB⟩ := hVc.bounded_above_of_compact_support hVcpt
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    obtain ⟨C, hC⟩ := (hG4t E k hk φ' hφ'.dec).2 (tsupport η) hcpt (k * M + k) (by nlinarith)
    refine ⟨B * max C 0, fun g hg => ?_⟩
    have hFbd : ∀ x, ‖F x‖ₑ ≤ ENNReal.ofReal B * (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow x) := by
      intro x
      by_cases hx : lastRow x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by rw [hFV]; exact ((V (lastRow x)).norm_coe_le_norm x).trans (hB _))
      · rw [Set.indicator_of_notMem hx, hFzero x hx]; simp
    set θ := ∑' ξ : RowT E k k, (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) with hθ
    have hS : ‖sumF F g‖ₑ ≤ ENNReal.ofReal B * θ :=
      enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hFbd _).trans_eq ENNReal.tsum_mul_left)
    have hx : Dt g ^ (-((k * M + k : ℕ) : ℝ) / k) ≤ (Dt g ^ M)⁻¹ := by
      have e : (-((k * M + k : ℕ) : ℝ) / k) = -(((M + 1 : ℕ) : ℝ)) := by push_cast; field_simp
      rw [e, Real.rpow_neg (hDpos g).le, Real.rpow_natCast]
      exact inv_anti₀ (pow_pos (hDpos g) _) (pow_le_pow_right₀ hg (by omega))
    refine fin_bd hB0 (Real.rpow_nonneg (hDpos g).le _) hx ?_
    simp only [hp1, mul_one]
    rw [enorm_mul, enorm_conj']
    calc ‖sumF F g‖ₑ * ‖φ' g‖ₑ ≤ (ENNReal.ofReal B * θ) * ‖φ' g‖ₑ := by gcongr
      _ = ENNReal.ofReal B * (θ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr; exact hC g
  · obtain ⟨Cf, hCf, hft⟩ := hcut.ft
    obtain ⟨M, C, hC⟩ := (hG4t E k hk (fun x => φ' (invT x)) hφ'.dec').1 Cf hCf k le_rfl
    obtain ⟨C', hC'⟩ := hft M
    refine ⟨max C' 0 * max C 0, fun g _ => ?_⟩
    have hJ : ∀ (z : Fin k → Ad E), ‖∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * z i) ∂vecMeasure E (Fin k)‖ₑ ≤
        ENNReal.ofReal (max C' 0) * ENNReal.ofReal (Cf.indicator (fun _ => ((1 + ‖fun i => pInf E (z i)‖) ^ M)⁻¹)
          fun i => pFin E (z i)) := by
      intro z
      have h := hC' z g
      by_cases hz : (fun i => pFin E (z i)) ∈ Cf
      · rw [Set.indicator_of_mem hz] at h ⊢
        rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      · rw [Set.indicator_of_notMem hz] at h ⊢
        rw [← ofReal_norm, le_antisymm h (norm_nonneg _)]
        simp
    have hgg : invT (invT g) = g := ((hH0 E k).2.2.2.2.2.2 g g).2
    have hCg := hC (invT g)
    simp only [hgg, hDinv] at hCg
    have e1 : ((Dt g)⁻¹) ^ (-(k : ℝ) / k) = Dt g := by
      rw [neg_div, div_self hk0, Real.rpow_neg_one, inv_inv]
    rw [e1] at hCg
    have hK : (Dt g : ℂ) * sumF F g = _ := hK12 E k hk ψ hψ S U φ η s hcut hinv g
    rw [hp1, mul_one, ← mul_assoc, hK, add_mul, add_sub_cancel_left]
    refine fin_bd (le_max_right _ _) (hDpos g).le le_rfl ?_
    rw [enorm_mul, enorm_conj']
    calc _ ≤ (ENNReal.ofReal (max C' 0) * ∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i))) * ‖φ' g‖ₑ := by
          gcongr
          exact enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hJ _).trans_eq ENNReal.tsum_mul_left)
      _ = ENNReal.ofReal (max C' 0) * (_ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TorusPowerExponential
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace TorusPowerExponential

section Loc

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)

theorem torusPow_add (x y : Fin n → ℤ) :
    Iwasawa.torusPow F n (x + y) = Iwasawa.torusPow F n x * Iwasawa.torusPow F n y := by
  simp only [Iwasawa.torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem conj_mem (x : Fin n → ℤ) {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹ ∈ Iwasawa.unipotent F n :=
  Iwasawa.diagGL_mul_mul_inv_mem_unipotent F n hu _

theorem exp_torus_mul (x : Fin n → ℤ) (h : GL (Fin n) F) :
    Iwasawa.iwasawaExponent F n (Iwasawa.torusPow F n x * h) = x + Iwasawa.iwasawaExponent F n h := by
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent F n h
  have key : Iwasawa.torusPow F n x * h = (Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹) *
      Iwasawa.torusPow F n (x + Iwasawa.iwasawaExponent F n h) * κ := by
    rw [torusPow_add]
    conv_lhs => rw [e]
    group
  rw [key, Iwasawa.iwasawaExponent_eq F n (conj_mem F n x hu) hκ]

theorem torusPow_zero : Iwasawa.torusPow F n 0 = 1 := by
  simpa using torusPow_add F n 0 0

end Loc

section Glob

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countable_pl : Countable (Pl E) := by
  classical
  haveI : Countable (𝓞 E) := (RingOfIntegers.basis E).repr.toEquiv.injective.countable
  let f : Pl E → Finset (𝓞 E) := fun v ↦ (IsNoetherian.noetherian v.asIdeal).choose
  refine Function.Injective.countable (f := f) fun v w h ↦ ?_
  have hv := (IsNoetherian.noetherian v.asIdeal).choose_spec
  have hw := (IsNoetherian.noetherian w.asIdeal).choose_spec
  ext1
  rw [← hv, ← hw]
  exact congrArg (fun s : Finset (𝓞 E) ↦ Submodule.span (𝓞 E) (s : Set (𝓞 E))) h

def A (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) : Set (GA E k) :=
  {g | ∀ w : Off E S, Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w}

theorem A_zero (S : Finset (Pl E)) : A (k := k) S 0 = G0 S := by
  ext g
  simp only [A, G0, Set.mem_setOf_eq, Finsupp.coe_zero, Pi.zero_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

theorem A_cover (S : Finset (Pl E))
    (hfin : ∀ g : GA E k, {w | Iwasawa.iwasawaExponent _ k (cLoc w g) ≠ 0}.Finite) (g : GA E k) :
    ∃ l, g ∈ A S l :=
  ⟨Finsupp.ofSupportFinite (fun w : Off E S => Iwasawa.iwasawaExponent _ k (cLoc w.1 g))
    ((hfin g).preimage Subtype.val_injective.injOn), fun w => rfl⟩

theorem A_disj (S : Finset (Pl E)) : Pairwise (Function.onFun Disjoint (A (k := k) S)) := by
  intro l l' hne
  exact Set.disjoint_left.2 fun g h h' => hne (Finsupp.ext fun w => (h w).symm.trans (h' w))

theorem A_closed (S : Finset (Pl E))
    (hcl : ∀ (w : Pl E) (l : Fin k → ℤ), IsClopen {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w g) = l})
    (l : Off E S →₀ (Fin k → ℤ)) : IsClosed (A S l) := by
  have : A S l = ⋂ w : Off E S, {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w} := by
    ext; simp [A]
  rw [this]
  exact isClosed_iInter fun w => (hcl w.1 (l w)).isClosed

theorem cLoc_unip (u : GA E k) (hu : UU 0 u) (w : Pl E) : cLoc w u ∈ Iwasawa.unipotent _ k := by
  refine ⟨fun i c hci => ?_, fun i => ?_⟩
  · change ((pLoc E w).comp (pFin E)) (u.val i c) = 0
    rw [hu.1 i c hci, map_zero]
  · change ((pLoc E w).comp (pFin E)) (u.val i i) = 1
    rw [hu.2.1 i, map_one]

theorem A_mul (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) (u g : GA E k) (hu : UU 0 u) :
    u * g ∈ A S l ↔ g ∈ A S l := by
  have h := fun w : Pl E => Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ k (cLoc_unip u hu w) (cLoc w g)
  simp only [A, Set.mem_setOf_eq, map_mul, h]

theorem A_tr (S : Finset (Pl E))
    (hloc : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), cLoc w (fl k w u : GA E k) = u)
    (hoff : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → cLoc v (fl k w u : GA E k) = 1)
    (l : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (hw : l w = 0) (x : Fin k → ℤ) (g : GA E k) :
    fl k w.1 (Iwasawa.torusPow _ k x) * g ∈ A S (Finsupp.single w x + l) ↔ g ∈ A S l := by
  simp only [A, Set.mem_setOf_eq, map_mul]
  have key : ∀ v : Off E S, (Iwasawa.iwasawaExponent _ k (cLoc v.1 (fl k w.1 (Iwasawa.torusPow _ k x)) *
      cLoc v.1 g) = (Finsupp.single w x + l) v ↔ Iwasawa.iwasawaExponent _ k (cLoc v.1 g) = l v) := by
    intro v
    by_cases hv : v = w
    · subst hv
      rw [hloc, exp_torus_mul, Finsupp.add_apply, Finsupp.single_eq_same, hw, add_zero]
      constructor
      · intro h; simpa using h
      · intro h; rw [h, add_zero]
    · have e1 : (Finsupp.single w x + l) v = l v := by simp [Finsupp.single_apply, Ne.symm hv]
      rw [hoff w.1 v.1 _ (fun h => hv (Subtype.ext h)), one_mul, e1]
  exact forall_congr' key

theorem Phi_tr (S : Finset (Pl E)) (Φ : GA E k → ℂ) (a : Off E S → (Fin k → ℤ) → ℂ) (hlaw : LawOff S Φ a)
    (ha0 : ∀ w, a w 0 = 1)
    (hcomm : ∀ (w : Pl E) (g : GA E k), cLoc w g = 1 → ∀ u, g * fl k w u = fl k w u * g)
    (hdec : ∀ (w : Pl E) (g : GA E k), ∃ g' : GA E k, cLoc w g' = 1 ∧ g = g' * fl k w (cLoc w g))
    (w : Off E S) (x : Fin k → ℤ) (g : GA E k) (hg : Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = 0) :
    Φ (fl k w.1 (Iwasawa.torusPow _ k x) * g) = a w x * Φ g := by
  obtain ⟨g', h1, hg'⟩ := hdec w.1 g
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent _ k (cLoc w.1 g)
  rw [hg] at e
  have h0 : Φ g = Φ g' := by
    rw [hg', e, hlaw w g' h1 u hu κ hκ 0, ha0, mul_one]
  have h2 : fl k w.1 (Iwasawa.torusPow _ k x) * g = g' * fl k w.1
      ((Iwasawa.torusPow _ k x * u * (Iwasawa.torusPow _ k x)⁻¹) * Iwasawa.torusPow _ k x * κ) := by
    conv_lhs => rw [hg', e]
    rw [← mul_assoc, ← hcomm w.1 g' h1, mul_assoc, ← map_mul, torusPow_zero, mul_one]
    congr 2
    group
  rw [h2, hlaw w g' h1 _ (conj_mem _ k x hu) κ hκ x, h0, mul_comm]

end Glob

end TorusPowerExponential

theorem torus_exponential_of_open : jumpWindows.G0 → C0 → C1 → C2 := by
  intro hG hC0 hC1 E _ _ _ k μ _ hk β hβ S Φ a hΦm hΦu hlaw ha0 hint
  obtain ⟨-, -, -, hloc, hoff, -, -, hcomm, -⟩ := hG E k
  obtain ⟨-, -, -, -, hfin, hcl, hdec⟩ := hC0 E k S
  haveI := TorusPowerExponential.countable_pl (E := E)
  have hmeas : ∀ l, MeasurableSet (TorusPowerExponential.A (k := k) S l) := fun l => (TorusPowerExponential.A_closed S hcl l).measurableSet
  let c : Off E S → (Fin k → ℤ) → ℂ := fun w x => (nq w : ℂ) ^ rhoPair x * a w x
  have hc0 : ∀ w, c w 0 = 1 := fun w => by simp [c, rhoPair, ha0]
  have hstep : ∀ (f : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (x : Fin k → ℤ), f w = 0 →
      ∫ g in TorusPowerExponential.A S (Finsupp.single w x + f), Φ g ∂μ.withDensity β =
        c w x * ∫ g in TorusPowerExponential.A S f, Φ g ∂μ.withDensity β := by
    intro f w x hw
    have hUU : ∀ u, UU 0 u → ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ (u * g) =
        (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ g := by
      intro u hu g
      by_cases hg : g ∈ TorusPowerExponential.A S (Finsupp.single w x + f)
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_mul S _ u g hu).2 hg), Set.indicator_of_mem hg, hΦu u hu g]
      · rw [Set.indicator_of_notMem (mt (TorusPowerExponential.A_mul S _ u g hu).1 hg), Set.indicator_of_notMem hg]
    obtain ⟨-, hE⟩ := hC1 E k μ hk β hβ w.1 x ((TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ)
      (hΦm.indicator (hmeas _))
      hUU
      (hint.indicator (hmeas _))
    rw [← integral_indicator (hmeas _), hE, ← integral_indicator (hmeas _)]
    have hpt : ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ
        (fl k w.1 (Iwasawa.torusPow (w.1.adicCompletion E) k x) * g) =
        a w x * (TorusPowerExponential.A S f).indicator Φ g := by
      intro g
      by_cases hg : g ∈ TorusPowerExponential.A S f
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).2 hg), Set.indicator_of_mem hg,
          TorusPowerExponential.Phi_tr S Φ a hlaw ha0 hcomm (fun w g => (hdec w g).imp fun g' h => ⟨h.1, h.2.1⟩) w x g
            ((hg w).trans hw)]
      · rw [Set.indicator_of_notMem (fun h => hg ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).1 h)),
          Set.indicator_of_notMem hg, mul_zero]
    simp only [hpt, c, nq]
    rw [integral_const_mul, mul_assoc]
  have hclaim : ∀ l : Off E S →₀ (Fin k → ℤ), ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β =
      (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β := by
    intro l
    induction l using Finsupp.induction with
    | zero => simp [TorusPowerExponential.A_zero]
    | single_add w x f hwf hx ih =>
      have hfw : f w = 0 := Finsupp.notMem_support_iff.1 hwf
      change _ = Finsupp.prod (Finsupp.single w x + f) c * _
      change _ = Finsupp.prod f c * _ at ih
      have hdisj : Disjoint (Finsupp.single w x).support f.support := by
        refine Finset.disjoint_left.2 fun v hv hv' => hwf ?_
        rw [Finsupp.support_single_ne_zero _ hx, Finset.mem_singleton] at hv
        exact hv ▸ hv'
      rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (hc0 w), hstep f w x hfw, ih]
      simp only [c]
      ring
  have hU : ⋃ l, TorusPowerExponential.A (k := k) S l = Set.univ := Set.iUnion_eq_univ_iff.2 (TorusPowerExponential.A_cover S hfin)
  have hs := hasSum_integral_iUnion hmeas (TorusPowerExponential.A_disj S) hint.integrableOn
  rw [hU, setIntegral_univ] at hs
  have hfun : (fun l => ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β) =
      fun l : Off E S →₀ (Fin k → ℤ) => (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β :=
    funext hclaim
  rw [hfun] at hs
  exact hs

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.VolumeShellOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ShellSummation

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem map_wd (μ : Measure (GA E k)) [μ.IsMulLeftInvariant] (β : GA E k → ℝ≥0∞) (z : GA E k) :
    Measure.map (fun g => z * g) (μ.withDensity β) = μ.withDensity (fun g => β (z⁻¹ * g)) := by
  ext s hs
  have key := lintegral_mul_left_eq_self (μ := μ) (s.indicator fun g => β (z⁻¹ * g)) z
  rw [Measure.map_apply (measurable_const_mul z) hs, withDensity_apply _ (measurable_const_mul z hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_const_mul z hs), ← lintegral_indicator hs, ← key]
  refine lintegral_congr fun x => ?_
  by_cases hx : z * x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun g => z * g) ⁻¹' s from hx),
      inv_mul_cancel_left]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun g => z * g) ⁻¹' s from hx)]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem wt_shift {ν : Measure (GA E k)} (β : GA E k → ℝ≥0∞) (hβ : IsWt ν β) (z : GA E k)
    (hz : ∀ g, z * g = g * z) : IsWt ν (fun g => β (z⁻¹ * g)) := by
  refine ⟨hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
  have hc : ∀ h : GA E k, z⁻¹ * (h * g) = h * (z⁻¹ * g) := fun h => by
    have : z⁻¹ * h = h * z⁻¹ := ((Commute.inv_left (hz h))).eq
    rw [← mul_assoc, this, mul_assoc]
  simp only [hc]
  exact hβ.2 _


omit [_root_.NumberField.IsTotallyComplex E] [NumberField E] in
variable (E k) in
def shell (a : ℝ) (j : ℤ) : Set (GA E k) :=
  {g | Real.exp (a * j) ≤ Dt g ∧ Dt g < Real.exp (a * j) * Real.exp a}

theorem exists_shell (a D : ℝ) (ha : 0 < a) (hD : 0 < D) :
    ∃ j : ℤ, Real.exp (a * j) ≤ D ∧ D < Real.exp (a * j) * Real.exp a := by
  refine ⟨⌊Real.log D / a⌋, ?_, ?_⟩
  · have h := Int.floor_le (Real.log D / a)
    rw [le_div_iff₀ ha] at h
    calc Real.exp (a * ⌊Real.log D / a⌋) ≤ Real.exp (Real.log D) :=
          Real.exp_le_exp.mpr (by linarith [mul_comm a (⌊Real.log D / a⌋ : ℝ)])
      _ = D := Real.exp_log hD
  · have h := Int.lt_floor_add_one (Real.log D / a)
    rw [div_lt_iff₀ ha] at h
    rw [← Real.exp_add]
    calc D = Real.exp (Real.log D) := (Real.exp_log hD).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith [mul_comm a (⌊Real.log D / a⌋ : ℝ)])

theorem min_le_bnd (a ε D : ℝ) (ha : 0 < a) (hε : 0 < ε) (hD : 0 < D) (j : ℤ)
    (h1 : Real.exp (a * j) ≤ D) (h2 : D < Real.exp (a * j) * Real.exp a) :
    min D D⁻¹ ^ ε ≤ Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|) := by
  have key : min D D⁻¹ ≤ Real.exp (a - a * |(j : ℝ)|) := by
    rcases le_or_gt 0 (j : ℝ) with hj | hj
    · rw [abs_of_nonneg hj]
      calc min D D⁻¹ ≤ D⁻¹ := min_le_right _ _
        _ ≤ (Real.exp (a * j))⁻¹ := inv_anti₀ (Real.exp_pos _) h1
        _ = Real.exp (-(a * j)) := (Real.exp_neg _).symm
        _ ≤ Real.exp (a - a * j) := Real.exp_le_exp.mpr (by linarith)
    · rw [abs_of_neg hj]
      calc min D D⁻¹ ≤ D := min_le_left _ _
        _ ≤ Real.exp (a * j) * Real.exp a := h2.le
        _ = Real.exp (a - a * -(j : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  calc min D D⁻¹ ^ ε ≤ Real.exp (a - a * |(j : ℝ)|) ^ ε :=
        Real.rpow_le_rpow (le_min hD.le (inv_nonneg.mpr hD.le)) key hε.le
    _ = Real.exp ((a - a * |(j : ℝ)|) * ε) := (Real.exp_mul _ _).symm
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem summ (c : ℝ) (hc : 0 < c) : Summable fun j : ℤ => Real.exp (-c * |(j : ℝ)|) := by
  have hr : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hg : Summable fun n : ℕ => Real.exp (-c * n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr).congr fun n => by
      rw [← Real.exp_nat_mul, mul_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hg
  · simpa using hg

end ShellSummation

open ShellSummation in
set_option synthInstance.maxHeartbeats 400000 in
theorem volume_shell_of : Q1 → Q2 → D0 → N3 → W0 → V1 := by
  intro hQ1 hQ2 hD0 hN3 hW0 E _ _ _ k μ _ hk β hβ
  obtain ⟨hpos, hmul, hcont, hrat, -, -, hcen, hcomm, -⟩ := hD0 E k
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).2.1 k le_rfl
  have hH : ∀ᵐ h ∂nuB E k k, h ∈ {x : GA E k | ∃ γ, ratGL E k γ = x} := by
    filter_upwards [hae] with h hh'
    obtain ⟨γ, u, -, hu, hh⟩ := hh'
    rw [hh, uu_eq_one le_rfl hu, mul_one]
    exact ⟨γ, rfl⟩
  have T1 : ∀ β₁, IsWt (nuB E k k) β₁ → ∀ Φ : GA E k → ℝ≥0∞, Measurable Φ → RatInv Φ →
      ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, Φ g ∂μ.withDensity β₁ := by
    intro β₁ hβ₁ Φ hΦ hΦi
    have := hQ1 (GA E k) μ (nuB E k k) (Measure.dirac 1) {x : GA E k | ∃ γ, ratGL E k γ = x} β β₁ hinv hH hβ
      hβ₁.1 (fun g => by simp only [lintegral_dirac, inv_one, one_mul]; exact hβ₁.2 g) Φ hΦ
      (by rintro _ ⟨γ, rfl⟩ g; exact hΦi γ g)
    rw [this]
    simp only [lintegral_dirac, one_mul]
  have T2 : ∀ β₁, IsWt (nuB E k k) β₁ → ∀ Φ : GA E k → ℂ, Measurable Φ → RatInv Φ →
      Integrable Φ (μ.withDensity β) → ∫ g, Φ g ∂μ.withDensity β = ∫ g, Φ g ∂μ.withDensity β₁ := by
    intro β₁ hβ₁ Φ hΦ hΦi hint
    have := (hQ2 (GA E k) μ (nuB E k k) (Measure.dirac 1) {x : GA E k | ∃ γ, ratGL E k γ = x} β β₁ hinv hH hβ
      hβ₁.1 (fun g => by simp only [lintegral_dirac, inv_one, one_mul]; exact hβ₁.2 g) Φ hΦ
      (by rintro _ ⟨γ, rfl⟩ g; exact hΦi γ g) hint).2
    rw [this]
    simp only [integral_dirac, one_mul]
  have hshift : ∀ t, IsWt (nuB E k k) (fun g => β ((splitCentre E k t)⁻¹ * g)) := fun t =>
    wt_shift β hβ _ (hcomm t)
  have P1 : ∀ (t : ℝ) (Φ : GA E k → ℝ≥0∞), Measurable Φ → RatInv Φ →
      ∫⁻ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫⁻ g, Φ g ∂μ.withDensity β := by
    intro t Φ hΦ hΦi
    rw [T1 _ (hshift t) Φ hΦ hΦi, ← map_wd μ β (splitCentre E k t),
      lintegral_map hΦ (measurable_const_mul _)]
  have P2 : ∀ (t : ℝ) (Φ : GA E k → ℂ), Measurable Φ → RatInv Φ → Integrable Φ (μ.withDensity β) →
      ∫ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫ g, Φ g ∂μ.withDensity β := by
    intro t Φ hΦ hΦi hint
    rw [T2 _ (hshift t) Φ hΦ hΦi hint, ← map_wd μ β (splitCentre E k t),
      integral_map (measurable_const_mul _).aemeasurable hΦ.aestronglyMeasurable]
  refine ⟨P1, P2, fun ε hε => ?_⟩
  obtain ⟨a, ha, hcen'⟩ : ∃ a : ℝ, 0 < a ∧ ∀ t, Dt (splitCentre E k t) = Real.exp (a * t) :=
    ⟨_, mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr Module.finrank_pos), hcen⟩
  have hD : Measurable (Dt : GA E k → ℝ) := hcont.measurable
  have hz : ∀ t g, Dt (splitCentre E k t * g) = Real.exp (a * t) * Dt g := fun t g => by
    rw [hmul, hcen']
  have hband : MeasurableSet (band E k) := by
    rw [show band E k = {g | 1 ≤ Dt g} ∩ {g | Dt g < Dt (splitCentre E k 1)} from rfl]
    exact (measurableSet_le measurable_const hD).inter (measurableSet_lt hD measurable_const)
  have hS : ∀ j, MeasurableSet (shell E k a j) := fun j => by
    rw [show shell E k a j = {g | Real.exp (a * j) ≤ Dt g} ∩ {g | Dt g < Real.exp (a * j) * Real.exp a} from rfl]
    exact (measurableSet_le measurable_const hD).inter (measurableSet_lt hD measurable_const)
  have hBfin : μ.withDensity β (band E k) < ∞ := (hW0 E k μ hk).2 β hβ
  have hSμ : ∀ j, μ.withDensity β (shell E k a j) ≤ μ.withDensity β (band E k) := by
    intro j
    have hP := P1 (-(j : ℝ)) ((band E k).indicator 1) (measurable_one.indicator hband) (by
      intro γ g
      have hmem : ratGL E k γ * g ∈ band E k ↔ g ∈ band E k := by
        simp only [band, Set.mem_ofPred_eq, hmul, hrat, one_mul]
      by_cases hg : g ∈ band E k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]; rfl
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.1 h))])
    rw [lintegral_indicator_one hband] at hP
    rw [← hP, ← lintegral_indicator_one (hS j)]
    refine lintegral_mono fun g => ?_
    refine Set.indicator_le (g := fun g => (band E k).indicator 1 (splitCentre E k (-(j : ℝ)) * g))
      (fun g hg => ?_) g
    simp only [shell, Set.mem_ofPred_eq] at hg
    obtain ⟨h1, h2⟩ := hg
    have e1 : Real.exp (a * -(j : ℝ)) * Real.exp (a * j) = 1 := by
      rw [← Real.exp_add, show a * -(j : ℝ) + a * j = 0 by ring, Real.exp_zero]
    have e0 : 0 < Real.exp (a * -(j : ℝ)) := Real.exp_pos _
    have hmem : splitCentre E k (-(j : ℝ)) * g ∈ band E k := by
      show 1 ≤ Dt _ ∧ Dt _ < Dt (splitCentre E k 1)
      rw [hz, hcen', mul_one]
      constructor
      · have := mul_le_mul_of_nonneg_left h1 e0.le
        linarith
      · have := mul_lt_mul_of_pos_left h2 e0
        rw [← mul_assoc, e1, one_mul] at this
        exact this
    rw [Set.indicator_of_mem hmem]
    exact le_rfl
  have hf : Measurable fun g : GA E k => min (Dt g) (Dt g)⁻¹ ^ ε := (hD.min hD.inv).pow_const ε
  have hsum := (summ (a * ε) (mul_pos ha hε)).mul_left (Real.exp (a * ε))
  have hnn : ∀ j : ℤ, 0 ≤ Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|) := fun j => by positivity
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ g, ‖min (Dt g) (Dt g)⁻¹ ^ ε‖ₑ ∂μ.withDensity β
      ≤ ∫⁻ g, ∑' j : ℤ, (shell E k a j).indicator
          (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g ∂μ.withDensity β := by
        refine lintegral_mono fun g => ?_
        obtain ⟨j, h1, h2⟩ := exists_shell a (Dt g) ha (hpos g)
        have hmem : g ∈ shell E k a j := by simp only [shell, Set.mem_ofPred_eq]; exact ⟨h1, h2⟩
        calc ‖min (Dt g) (Dt g)⁻¹ ^ ε‖ₑ = ENNReal.ofReal (min (Dt g) (Dt g)⁻¹ ^ ε) :=
              Real.enorm_eq_ofReal (Real.rpow_nonneg (le_min (hpos g).le (inv_nonneg.mpr (hpos g).le)) ε)
          _ ≤ ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) :=
              ENNReal.ofReal_le_ofReal (min_le_bnd a ε (Dt g) ha hε (hpos g) j h1 h2)
          _ = (shell E k a j).indicator
                (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g :=
              by rw [Set.indicator_of_mem hmem]
          _ ≤ _ := ENNReal.le_tsum (f := fun j : ℤ => (shell E k a j).indicator
                (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g) j
    _ = ∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) *
          μ.withDensity β (shell E k a j) := by
        rw [lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable]
        exact tsum_congr fun j => lintegral_indicator_const (hS j) _
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) *
          μ.withDensity β (band E k) := ENNReal.tsum_le_tsum fun j => by exact mul_le_mul_of_nonneg_left (hSμ j) (zero_le)
    _ = (∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) *
          μ.withDensity β (band E k) := ENNReal.tsum_mul_right
    _ < ∞ := by
        refine ENNReal.mul_lt_top ?_ hBfin
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
        exact ENNReal.ofReal_lt_top

end PositivityTheory.AdelicQuotientData

end
end
