module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
noncomputable section

open GlobalTheory.K5 GlobalTheory.Glue

namespace GlobalTheory.GeoFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def InR (ψ : O0 p →+* Ω) (y : Ω) : Prop :=
  ∃ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p),
    (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) ∧
    y = ∑ t, e t * ψ (b t)

variable (p Ω) in
abbrev zpAlg : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra

theorem isAlgZp_iff (x : Ω) : IsAlgZp (p := p) x ↔ @IsAlgebraic ℤ_[p] Ω _ _ (zpAlg p Ω) x := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold IsAlgZp IsAlgebraic
  simp only [Polynomial.aeval_map_algebraMap]

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_one : IsAlgZp (p := p) (1 : Ω) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff]
  exact isAlgebraic_one

theorem isInt_psi {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (b : O0 p) :
    IsInt (p := p) (ψ b) := by
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C (qO p),
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Basic.qq_pow, sub_self]
  have hb : ψ b ∈ ψ.range := ⟨b, rfl⟩
  rw [h.rng] at hb
  exact adjoin_le_integralClosure hq hb

theorem inR_zero (ψ : O0 p →+* Ω) : InR ψ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun t => t.elim0, by simp⟩

theorem inR_psi (ψ : O0 p →+* Ω) (b : O0 p) : InR ψ (ψ b) :=
  ⟨1, fun _ => 1, fun _ => b, fun _ => ⟨isIntegral_one, isAlgZp_one⟩, by simp⟩

theorem inR_add {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x + y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  refine ⟨d + d', Fin.append e e', Fin.append b b', fun t => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) t
    · simpa using he i
    · simpa using he' i
  · rw [Fin.sum_univ_add]
    simp

theorem inR_sum {ψ : O0 p →+* Ω} {ι : Type*} (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, InR ψ (f i)) :
    InR ψ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inR_zero ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inR_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem inR_mul {ψ : O0 p →+* Ω} {x y : Ω} (hx : InR ψ x) (hy : InR ψ y) : InR ψ (x * y) := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  obtain ⟨d', e', b', he', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine inR_sum _ _ fun i _ => inR_sum _ _ fun j _ => ?_
  refine ⟨1, fun _ => e i * e' j, fun _ => b i * b' j,
    fun _ => ⟨IsIntegral.mul (he i).1 (he' j).1, isAlgZp_mul (he i).2 (he' j).2⟩, ?_⟩
  simp only [Finset.univ_unique, Finset.sum_singleton, map_mul]
  ring

theorem inR_neg {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) : InR ψ (-x) := by
  have := inR_mul (inR_psi ψ (-1)) hx
  simpa using this

theorem InR.isInt {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω} (hx : InR ψ x) :
    IsInt (p := p) x := by
  obtain ⟨d, e, b, he, rfl⟩ := hx
  exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (isInt_psi h (b t))

theorem algebraMap_zp_injective : Function.Injective (algebraMap ℤ_[p] (O0 p)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : algebraMap ℤ_[p] (O0 p) ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (algebraMap ℤ_[p] (O0 p))).ne_zero
  have hp0 : (p : O0 p) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

theorem exists_inR_of_isAlgZp (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) {x : Ω}
    (hx : IsAlgZp (p := p) x) : ∃ D : O0 p, D ≠ 0 ∧ InR ψ (x * ψ D) := by
  letI := zpAlg p Ω
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx' := (isAlgZp_iff x).1 hx
  obtain ⟨y, hy0, hyi⟩ := hx'.exists_integral_multiple
  set c : O0 p := algebraMap ℤ_[p] (O0 p) y with hcdef
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  obtain ⟨D, hD⟩ := hmem
  have hc0 : c ≠ 0 := fun h0 => hy0 (algebraMap_zp_injective (by rw [← hcdef, h0, map_zero]))
  refine ⟨D, ?_, 1, fun _ => y • x, fun _ => 1, fun _ => ⟨?_, ?_⟩, ?_⟩
  · rintro rfl
    rw [map_zero] at hD
    exact hc0 (hc.inj (by rw [← hD, map_zero]))
  · exact hyi.tower_top
  · rw [isAlgZp_iff, Algebra.smul_def]
    exact (isAlgebraic_algebraMap y).mul hx'
  · simp only [Finset.univ_unique, Finset.sum_singleton, map_one, mul_one]
    rw [hD, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω, mul_comm]

theorem algebraMap_zp_eq (m : ℤ_[p]) :
    algebraMap ℤ_[p] (O0 p) m = algebraMap (Lau p) (O0 p) (HahnSeries.C m) := by
  have hH := (o0_isAdicComplete_span_p p).toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun K => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hs := PadicInt.appr_spec K m
  rw [Ideal.mem_span_singleton] at hs
  obtain ⟨u, hu⟩ := hs
  have hm : m = (m.appr K : ℤ_[p]) + (p : ℤ_[p]) ^ K * u := by rw [← hu]; ring
  refine ⟨algebraMap ℤ_[p] (O0 p) u - algebraMap (Lau p) (O0 p) (HahnSeries.C u), ?_⟩
  conv_lhs => rw [hm]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem isAlgZp_zp (m : ℤ_[p]) : IsAlgZp (p := p) (zp Ω m) := by
  refine ⟨Polynomial.X - Polynomial.C m, Polynomial.X_sub_C_ne_zero m, ?_⟩
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    zp, algebraMap_zp_eq, HahnSeries.C_apply, sub_self]

theorem isAlgZp_add {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x + y) := by
  letI := zpAlg p Ω
  rw [isAlgZp_iff] at hx hy ⊢
  exact hx.add hy

end GlobalTheory.GeoFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEval
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMemStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω),
        (∀ t, IsInt (p := p) (E t) ∧ IsAlgZp (p := p) (E t)) →
        ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω),
          (∀ j, IsInt (p := p) (f j) ∧ IsAlgZp (p := p) (f j)) ∧
          ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt (p := p) y →
            (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t →
            ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  intro p _ Ω _ _ hc d E hE v
  let : Algebra ℤ_[p] Ω := zpAlg (p := p) (Ω := Ω)
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hAlg (x : Ω) : IsAlgZp (p := p) x ↔ IsAlgebraic ℤ_[p] x := by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hsmul (c : ℤ_[p]) (x : Ω) : c • x = zp Ω c * x := by
    rw [Algebra.smul_def]
    congr 1
    change algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) c) = zp Ω c
    rw [zp, algebraMap_zp_eq, HahnSeries.C_apply]
  have hpv : ((p : Ω) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  let S' : Submodule ℤ_[p] Ω :=
    { carrier := {y | IsInt (p := p) y ∧ (p : Ω) ^ v * y ∈ S}
      add_mem' := by
        rintro x y ⟨hxInt, hxS⟩ ⟨hyInt, hyS⟩
        exact ⟨IsIntegral.add hxInt hyInt, by rw [mul_add]; exact S.add_mem hxS hyS⟩
      zero_mem' := ⟨isIntegral_zero, by simp⟩
      smul_mem' := by
        rintro c x ⟨hxInt, hxS⟩
        refine ⟨?_, ?_⟩
        · change IsIntegral (O0 p) (c • x)
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]
          exact IsIntegral.mul isIntegral_algebraMap hxInt
        · change (p : Ω) ^ v * (c • x) ∈ S
          rw [mul_smul_comm]
          exact S.smul_mem c hxS }
  let U := Submodule.span ℤ_[p] (Set.range fun t => E t / (p : Ω) ^ v)
  have hle : S' ≤ U := by
    rintro y ⟨_, hy⟩
    change (p : Ω) ^ v * y ∈ Submodule.span ℤ_[p] (Set.range E) at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy
    apply (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).2
    refine ⟨c, ?_⟩
    calc
      ∑ t, c t • (E t / (p : Ω) ^ v) = (∑ t, c t • E t) / (p : Ω) ^ v := by
        simp only [Finset.sum_div, smul_div_assoc]
      _ = y := (div_eq_iff hpv).2 (hc.trans (mul_comm _ _))
  have hnoeth : IsNoetherian ℤ_[p] U :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  have hfg : S'.FG := isNoetherian_submodule.1 hnoeth S' hle
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hfmem (j : Fin m) : IsInt (p := p) (f j) ∧ (p : Ω) ^ v * f j ∈ S := by
    change f j ∈ S'
    rw [← hf]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hAlgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x := by
    intro x hx
    change x ∈ Submodule.span ℤ_[p] (Set.range E) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact (hAlg _).1 (hE t).2
    | zero => exact isAlgebraic_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact (isAlgebraic_algebraMap c).mul hx
  refine ⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩
  · apply (hAlg _).2
    have hInv : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹) :=
      ((isAlgebraic_natCast p : IsAlgebraic ℤ_[p] (p : Ω)).pow v).inv
    have h := hInv.mul (hAlgS _ (hfmem j).2)
    rwa [← mul_assoc, inv_mul_cancel₀ hpv, one_mul] at h
  · intro l y hy hyl
    have hyS : y ∈ S' := by
      refine ⟨hy, ?_⟩
      rw [hyl]
      refine S.sum_mem fun t _ => ?_
      rw [← hsmul]
      exact S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [← hf] at hyS
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS
    exact ⟨μ, by simpa only [hsmul] using hμ.symm⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEval
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix.Divide

theorem divide_ev : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
    (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o →
    ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  intro p _ Ω _ _ hc T n ψ h d e a he v o ho hsum
  classical
  haveI := Basic.charZero_of_isClo hc
  set c : ℤ → Ω := fun r => ∑ t, e t * zp Ω ((a t).coeff r) with hcdef
  have hev : Ev ψ c (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
      (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) :=
    ⟨d, e, a, he, fun r => rfl, rfl, rfl⟩
  have hcong : Cong (p := p) v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) 0 :=
    ⟨o, ho, by rw [sub_zero, hsum]⟩
  have hcr := ((GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ω hc T n ψ h v c _ _ hev).1.1 hcong)
  choose y hy hcy using hcr
  obtain ⟨m, f, hf, hlat⟩ := GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem p Ω hc d e he v
  have hμ : ∀ r, ∃ μ : Fin m → ℤ_[p], y r = ∑ j, zp Ω (μ j) * f j := by
    intro r
    refine hlat (fun t => (a t).coeff r) (y r) (hy r) ?_
    have := hcy r
    rw [sub_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  choose μ hμ using hμ
  let μ' : ℤ → Fin m → ℤ_[p] := fun r => if ∀ t, (a t).coeff r = 0 then 0 else μ r
  have hsupp : ∀ j, (Function.support fun r => μ' r j) ⊆ ⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support := by
    intro j r hr
    simp only [Function.mem_support] at hr
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · exact absurd (by simp [μ', h0]) hr
    · push_neg at h0
      obtain ⟨t, ht⟩ := h0
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ t)) ht
  have hpwo : (⋃ t ∈ (Finset.univ : Finset (Fin d)), (a t).support).IsPWO :=
    (Finset.univ.isPWO_bUnion).2 fun t _ => (a t).isPWO_support
  let Λ : Fin m → Lau p := fun j => ⟨fun r => μ' r j, hpwo.mono (hsupp j)⟩
  have hΛ : ∀ j r, (Λ j).coeff r = μ' r j := fun _ _ => rfl

  let Λp : Fin m → Lau p := fun j => HahnSeries.C ((p : ℤ_[p]) ^ v) * Λ j
  have hzpp : zp Ω ((p : ℤ_[p]) ^ v) = (p : Ω) ^ v := by
    rw [← GlobalTheory.EvUniq.zpHom_apply, map_pow, map_natCast]
  have hcoef : ∀ r, c r = ∑ j, f j * zp Ω ((Λp j).coeff r) := by
    intro r
    have hc1 : ∀ j, zp Ω ((Λp j).coeff r) = (p : Ω) ^ v * zp Ω (μ' r j) := by
      intro j
      simp only [Λp, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hΛ]
      rw [← GlobalTheory.EvUniq.zpHom_apply, map_mul, GlobalTheory.EvUniq.zpHom_apply, GlobalTheory.EvUniq.zpHom_apply, hzpp]
    simp only [hc1]
    by_cases h0 : ∀ t, (a t).coeff r = 0
    · have hμ0 : μ' r = 0 := by simp [μ', h0]
      have hz : zp Ω (0 : ℤ_[p]) = 0 := by rw [← GlobalTheory.EvUniq.zpHom_apply, map_zero]
      simp [hcdef, h0, hμ0, hz]
    · have hμr : μ' r = μ r := by simp [μ', h0]
      have := hcy r
      rw [sub_zero] at this
      rw [this, hμ r, hμr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hev2 : Ev ψ c (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)))
      (∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (thL (Λp j)))) :=
    ⟨m, f, Λp, hf, hcoef, rfl, rfl⟩
  have heq := (GlobalTheory.EvUniq.ev_unique p Ω hc T n ψ h c _ _ _ _ hev hev2).1
  have hval : ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λp j)) =
      (p : Ω) ^ v * ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Λp, map_mul, GlobalTheory.EvUniq.psi_C h, hzpp]
    ring
  have hp0 : (p : Ω) ^ v ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have ho' : o = ∑ j, f j * ψ (algebraMap (Lau p) (O0 p) (Λ j)) := by
    rw [hsum, hval] at heq
    exact mul_left_cancel₀ hp0 heq
  exact ⟨fun r => ∑ j, f j * zp Ω ((Λ j).coeff r), _, m, f, Λ, hf, fun r => rfl, ho', rfl⟩

end GlobalTheory.GeoFix.Divide
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEvalStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o → ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  first | exact @GlobalTheory.GeoFix.Divide.divide_ev | exact GlobalTheory.GeoFix.Divide.divide_ev | (intros; apply GlobalTheory.GeoFix.Divide.divide_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSubfieldOfFixedByGeometricTowerGaloisStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) → (∀ x : Ω, IsAlgZp (p := p) x → x ∈ F) → T.qq n ∈ F → ∀ o : Ω, (∀ g ∈ Ggeo (p := p) Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  intro p hp Ω _ _ hc T n F hO hA hq o ho
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have : IsAlgClosed Ω := hc.clo
  let f : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  let : Algebra (O0 p) F := f.toAlgebra
  have : IsScalarTower (O0 p) F Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hf : Function.Injective (algebraMap (O0 p) F) :=
    fun _ _ h => hc.inj (congrArg Subtype.val h)
  have : Algebra.IsAlgebraic (O0 p) Ω := hc.alg
  have : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.extendScalars (R := O0 p) hf
  have : IsAlgClosure F Ω := ⟨hc.clo, inferInstance⟩
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hζ : IsAlgZp (p := p) (T.ζ n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow_sub_C (1 : ℤ_[p]) (pow_ne_zero _ hp.out.ne_zero)).ne_zero
    · simp [(T.prim n).pow_eq_one]
  have ho' : o ∈ Set.range (algebraMap F Ω) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed o).2 fun σ => ?_
    let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes (f c)
    have hg : g ∈ Ggeo (p := p) Ω ⊓ Gn T n := by
      refine ⟨fun x hx => σ.commutes ⟨x, hA x hx⟩, ?_, ?_⟩
      · show g • T.ζ n = T.ζ n
        exact σ.commutes ⟨T.ζ n, hA _ hζ⟩
      · show g • T.qq n = T.qq n
        exact σ.commutes ⟨T.qq n, hq⟩
    exact ho g hg
  obtain ⟨x, rfl⟩ := ho'
  exact x.2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPow
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

noncomputable section

namespace GlobalTheory.GeoFix

theorem exists_lau_approx (p : ℕ) [Fact p.Prime] (K : ℕ) (x : O0 p) :
    ∃ (a : Lau p) (c : O0 p), x = algebraMap (Lau p) (O0 p) a + (p : O0 p) ^ K * c := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (pI p) K x)
  have hker : RingHom.ker (AdicCompletion.evalₐ (pI p) K) = (pI p ^ K).map (algebraMap (Lau p) (O0 p)) := by
    ext y
    rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem (Lau p), ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    have hle : (pI p ^ K • ⊤ : Ideal (Lau p)) ≤ pI p ^ K := by intro z hz; simpa using hz
    rw [← AdicCompletion.factor_eval_eq_evalₐ (pI p) y hle]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (pI p) (Lau p) K y)
      rw [← hb] at h ⊢
      have : b ∈ pI p ^ K := Ideal.Quotient.eq_zero_iff_mem.mp h
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
    · intro h; rw [h, map_zero]
  have hmem : x - algebraMap (Lau p) (O0 p) a ∈ RingHom.ker (AdicCompletion.evalₐ (pI p) K) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha, sub_self]
  rw [hker, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨a, c, by rw [mul_comm, hc]; ring⟩

theorem exists_cong_lau :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
      (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
      ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt (p := p) (e t)) →
      ∀ K : ℕ, ∃ a : Fin d → Lau p,
        Cong (p := p) K (∑ t, e t * ψ (b t))
          (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  intro p hp Ω _ _ T n ψ h d e b he K
  choose a c hac using fun t => exists_lau_approx p K (b t)
  have hq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (pow_pos hp.out.pos n) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hψ (x : O0 p) : IsIntegral (O0 p) (ψ x) := by
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [h.rng] at hx
    exact adjoin_le_integralClosure hq hx
  refine ⟨a, ∑ t, e t * ψ (c t), IsIntegral.sum _ fun t _ => IsIntegral.mul (he t) (hψ (c t)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hac t, map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.GeoFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPowStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
      (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
    ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt (p := p) (e t)) →
    ∀ K : ℕ, ∃ a : Fin d → Lau p,
      Cong (p := p) K (∑ t, e t * ψ (b t))
        (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  exact @_root_.GlobalTheory.GeoFix.exists_cong_lau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImage
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImage
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem inR_algebraMap {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (c : O0 p) :
    ∃ c' : O0 p, ψ c' = algebraMap (O0 p) Ω c := by
  have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
    rw [h.rng]
    exact Subalgebra.algebraMap_mem _ c
  exact hmem

theorem inR_pow {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    {ψ : O0 p →+* Ω} {x : Ω} (hx : InR ψ x) (k : ℕ) : InR ψ (x ^ k) := by
  induction k with
  | zero => simpa using inR_psi ψ 1
  | succ k ih => rw [pow_succ]; exact inR_mul ih hx

theorem exists_inR_mul_eq_psi : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 →
    ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  intro p _ Ω _ _ hc T n ψ h N hN hN0
  obtain ⟨f, hfm, hf⟩ : IsIntegral (O0 p) N := hN.isInt h
  have key : ∀ k : ℕ, ∀ f : Polynomial (O0 p), f.natDegree = k → f.Monic → Polynomial.eval₂ (algebraMap (O0 p) Ω) N f = 0 →
      ∃ (N' : Ω) (D : O0 p), InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro f hk hfm hf
      by_cases h0 : f.coeff 0 = 0
      · obtain ⟨g, rfl⟩ := Polynomial.X_dvd_iff.2 h0
        have hgm : g.Monic := Polynomial.Monic.of_mul_monic_left Polynomial.monic_X hfm
        have hgdeg : g.natDegree < k := by
          rw [← hk, Polynomial.natDegree_X_mul hgm.ne_zero]; omega
        refine ih _ hgdeg g rfl hgm ?_
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hf
        exact (mul_eq_zero.1 hf).resolve_left hN0
      · obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.2 (show (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 by simp)
        obtain ⟨D, hD⟩ := inR_algebraMap h (-f.coeff 0)
        refine ⟨Polynomial.eval₂ (algebraMap (O0 p) Ω) N g, D, ?_, ?_, ?_⟩
        · rw [Polynomial.eval₂_eq_sum_range]
          refine inR_sum _ _ fun i _ => ?_
          obtain ⟨c', hc'⟩ := inR_algebraMap h (g.coeff i)
          rw [← hc']
          exact inR_mul (inR_psi ψ c') (inR_pow hN i)
        · rintro rfl
          rw [map_zero, map_neg] at hD
          apply h0
          apply hc.inj
          rw [map_zero (algebraMap (O0 p) Ω)]
          exact neg_eq_zero.mp hD.symm
        · have hf' : f = Polynomial.X * g + Polynomial.C (f.coeff 0) := by
            rw [← hg]; ring
          rw [hf', Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C] at hf
          rw [hD, map_neg]
          linear_combination hf
  exact key _ f rfl hfm hf

end GlobalTheory.GeoFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCombinationMulEqReparametrizationImageStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combination_mul_eq_reparametrization_image : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ N : Ω, GlobalTheory.GeoFix.InR ψ N → N ≠ 0 → ∃ (N' : Ω) (D : O0 p), GlobalTheory.GeoFix.InR ψ N' ∧ D ≠ 0 ∧ N * N' = ψ D := by
  first | exact @GlobalTheory.GeoFix.exists_inR_mul_eq_psi | exact GlobalTheory.GeoFix.exists_inR_mul_eq_psi | (intros; apply GlobalTheory.GeoFix.exists_inR_mul_eq_psi <;> assumption)
end
end

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem geofix : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (k : ℕ) (o : Ω), IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T n), g o = o) → ∃ (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' ∧ Cong (p := p) k o x := by
  intro p _ Ω _ _ hc T n ψ h k o ho hfix

  let F : Subfield Ω :=
    { carrier := {y | ∃ (N : Ω) (D : O0 p), InR ψ N ∧ D ≠ 0 ∧ y * ψ D = N}
      zero_mem' := ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
      one_mem' := ⟨ψ 1, 1, inR_psi ψ 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * ψ D' + N' * ψ D, D * D', inR_add (inR_mul hN (inR_psi ψ D')) (inR_mul hN' (inR_psi ψ D)),
          mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      mul_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * N', D * D', inR_mul hN hN', mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      neg_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        exact ⟨-N, D, inR_neg hN, hD, by rw [neg_mul, ha]⟩
      inv_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero]
          exact ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
        · have hψD : ψ D ≠ 0 := fun h0 => hD (h.inj (by rw [h0, map_zero]))
          have hN0 : N ≠ 0 := by rw [← ha]; exact mul_ne_zero ha0 hψD
          obtain ⟨N', D', hN', hD', hNN⟩ := GlobalTheory.T.exists_combination_mul_eq_reparametrization_image p Ω hc T n ψ h N hN hN0
          refine ⟨ψ D * N', D', inR_mul (inR_psi ψ D) hN', hD', ?_⟩
          rw [← hNN, ← ha]
          field_simp }
  have hF1 : ∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F := by
    intro c
    have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
      rw [h.rng]; exact Subalgebra.algebraMap_mem _ c
    obtain ⟨c', hc'⟩ := hmem
    exact ⟨ψ c', 1, inR_psi ψ c', one_ne_zero, by rw [map_one, mul_one, hc']⟩
  have hF2 : ∀ x : Ω, IsAlgZp p x → x ∈ F := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := exists_inR_of_isAlgZp hc h hx
    exact ⟨x * ψ D, D, hxD, hD, rfl⟩
  have hF3 : T.qq n ∈ F := ⟨ψ (qO p), 1, inR_psi ψ _, one_ne_zero, by rw [map_one, mul_one, h.par]⟩
  obtain ⟨N, D, hN, hD, hoD⟩ := GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois p Ω hc T n F hF1 hF2 hF3 o hfix

  obtain ⟨_, hdvr, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD hirr
  have hN1 : InR ψ (N * ψ (↑u⁻¹ : O0 p)) := inR_mul hN (inR_psi ψ _)
  have hpo : (p : Ω) ^ v * o = N * ψ (↑u⁻¹ : O0 p) := by
    rw [← hoD, hu, map_mul, map_pow, map_natCast]
    have : ψ (↑u : O0 p) * ψ (↑u⁻¹ : O0 p) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (-(↑p ^ v * o)) * this
  obtain ⟨d, e, b, he, hNe⟩ := hN1
  obtain ⟨a, z, hz, hza⟩ := GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow p Ω T n ψ h d e b (fun t => (he t).1) (v + k)
  have hsum : ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * (o - (p : Ω) ^ k * z) := by
    rw [← hNe] at hza
    rw [pow_add] at hza
    linear_combination -hpo - hza
  have hpi : IsInt (p := p) ((p : Ω) ^ k) := by
    rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω), ← map_pow]; exact isIntegral_algebraMap
  have ho' : IsInt (p := p) (o - (p : Ω) ^ k * z) := IsIntegral.sub ho (IsIntegral.mul hpi hz)
  obtain ⟨c, x', hEv⟩ := GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval p Ω hc T n ψ h d e a he v _ ho' hsum
  exact ⟨c, _, x', hEv, z, hz, by ring⟩

end GlobalTheory.GeoFix
