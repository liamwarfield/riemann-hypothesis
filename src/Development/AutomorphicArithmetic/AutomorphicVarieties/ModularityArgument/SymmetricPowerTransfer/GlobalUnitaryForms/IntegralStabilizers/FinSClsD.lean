module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc
public import GroundTheory.GlobalFields.Adele.Approximation

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSStab
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

variable {F : Type} [Field F] [NumberField F]

private theorem fin_box [IsTotallyReal F] (c : F) (hc : c ≠ 0) (A : F) :
    {x : F | IsIntegral ℤ (c * x) ∧ ∀ σ : F →+* ℝ, σ x ^ 2 ≤ σ A}.Finite := by
  have h := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, ‖φ c‖ * (‖φ A‖ + 1))
  refine (h.preimage (f := fun x : F => c * x) (mul_right_injective₀ hc).injOn).subset ?_
  rintro x ⟨hx, hA⟩
  refine ⟨hx, fun φ => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ c‖ * (‖φ A‖ + 1)) (fun _ _ => by positivity)
    (Finset.mem_univ φ))
  have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have e : ∀ y, ‖φ y‖ = |hr.embedding y| := fun y => by
    rw [← hr.coe_embedding_apply, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hA hr.embedding
  simp only [map_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [e, e]
  nlinarith [le_abs_self (hr.embedding A), sq_abs (hr.embedding x), abs_nonneg (hr.embedding x),
    sq_nonneg (|hr.embedding x| - 1)]

variable {Δ : F}

theorem coords_glob {a : Lsq F Δ} (h : ∀ v : Pl F, IsIntegral (Ov v) (lmap (cv v) Δ a)) {m : ℕ} (hm : IsIntegral ℤ ((m : F) * Δ)) :
    IsIntegral ℤ (2 * m * Δ * a.re) ∧ IsIntegral ℤ (2 * m * Δ * a.im) := by
  have := fun v : Pl F => isIntegral_coords (h v) (m := (m : Kv v)) (isIntegral_natCast _)
    (by simpa using isIntegral_glob.1 hm v)
  refine ⟨isIntegral_glob.2 fun v => ?_, isIntegral_glob.2 fun v => ?_⟩
  · simpa [lmap, map_ofNat] using (this v).1
  · simpa [lmap, map_ofNat] using (this v).2

theorem ne_zero_of_neg [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) : Δ ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  intro h
  simpa [h] using hneg (IsTotallyReal.complexEmbedding_isReal φ).embedding

theorem fin_SU [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (n : ℕ) (hn : n ≠ 0) :
    {γ : SU Δ | ∀ (v : Pl F) i j, IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * lmap (cv v) Δ (mt (γ : DX Δ) i j))}.Finite := by
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul Δ
  have hΔ := ne_zero_of_neg hneg
  have hc : (2 * m * Δ * n : F) ≠ 0 := by simp [hΔ, hm0, hn]
  have h1 := fin_box _ hc 1
  have h2 := fin_box _ hc (-Δ⁻¹)
  refine (((h1.prod h2).prod (h1.prod h2)).preimage (f := fun γ : SU Δ =>
    (((mt (γ : DX Δ) 0 0).re, (mt (γ : DX Δ) 0 0).im), ((mt (γ : DX Δ) 0 1).re, (mt (γ : DX Δ) 0 1).im))) ?_).subset ?_
  · intro γ _ γ' _ h
    simp only [Prod.mk.injEq] at h
    have e0 : mt (γ : DX Δ) 0 0 = mt (γ' : DX Δ) 0 0 := QuadraticAlgebra.ext h.1.1 h.1.2
    have e1 : mt (γ : DX Δ) 0 1 = mt (γ' : DX Δ) 0 1 := QuadraticAlgebra.ext h.2.1 h.2.2
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    change mt (γ : DX Δ) = mt (γ' : DX Δ)
    ext i j : 1
    fin_cases i <;> fin_cases j
    · exact e0
    · exact e1
    · exact (mt_mem _).2.trans (e1 ▸ (mt_mem _).2.symm)
    · exact (mt_mem _).1.trans (e0 ▸ (mt_mem _).1.symm)
  · intro γ hγ
    have hi := fun i j => coords_glob (a := (n : Lsq F Δ) * mt (γ : DX Δ) i j) (fun v => by
      rw [map_mul, map_natCast]; exact hγ v i j) hm
    have hd : (mt (γ : DX Δ)).det = 1 := congrArg Units.val γ.2
    rw [det_Dm (mt_mem _)] at hd
    have hd' := congrArg QuadraticAlgebra.re hd
    rw [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_one] at hd'
    have hs := fun σ : F →+* ℝ => congrArg σ hd'
    simp only [map_sub, map_add (f := _), map_mul, map_pow, map_one] at hs
    have key : ∀ (σ : F →+* ℝ) (x : ℝ), -σ Δ * x ^ 2 ≤ 1 → x ^ 2 ≤ σ (-Δ⁻¹) := fun σ x h => by
      rw [map_neg, map_inv₀, ← inv_neg, inv_eq_one_div, le_div_iff₀ (neg_pos.2 (hneg σ))]
      linarith
    have pos : ∀ (σ : F →+* ℝ) (x : ℝ), σ Δ * x ^ 2 ≤ 0 := fun σ x => mul_nonpos_of_nonpos_of_nonneg (hneg σ).le (sq_nonneg _)
    refine ⟨⟨⟨by simpa [mul_assoc] using (hi 0 0).1, fun σ => ?_⟩, by simpa [mul_assoc] using (hi 0 0).2, fun σ => key σ _ ?_⟩,
      ⟨by simpa [mul_assoc] using (hi 0 1).1, fun σ => ?_⟩, by simpa [mul_assoc] using (hi 0 1).2, fun σ => key σ _ ?_⟩
    all_goals
      have := hs σ
      have := pos σ (σ (mt (γ : DX Δ) 0 0).im)
      have := pos σ (σ (mt (γ : DX Δ) 0 1).im)
      have := sq_nonneg (σ (mt (γ : DX Δ) 0 0).re)
      have := sq_nonneg (σ (mt (γ : DX Δ) 0 1).re)
      simp only [map_one]
      linarith

theorem int_conj (y k : DA Δ) (hk : ∀ v, k.1 v ∈ KD (cv v Δ) (Ov v)) {n n' : ℕ}
    (h : ∀ v i j, IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * mt (y.1 v) i j))
    (h' : ∀ v i j, IsIntegral (Ov v) ((n' : Lsq (Kv v) (cv v Δ)) * mt (y⁻¹.1 v) i j)) (v : Pl F) (i j : Fin 2) :
    IsIntegral (Ov v) (((n * n' : ℕ) : Lsq (Kv v) (cv v Δ)) * mt ((y * k * y⁻¹).1 v) i j) := by
  have e : mt ((y * k * y⁻¹).1 v) = mt (y.1 v) * mt (k.1 v) * mt (y⁻¹.1 v) := rfl
  have hk' := (mem_KD.1 (hk v)).1
  have := (((h v i 0).mul (hk' 0 0)).add ((h v i 1).mul (hk' 1 0))).mul (h' v 0 j) |>.add
    ((((h v i 0).mul (hk' 0 1)).add ((h v i 1).mul (hk' 1 1))).mul (h' v 1 j))
  convert this using 1
  rw [e]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_mul]
  ring

theorem finS_stab (D : Dat Δ) (h : D.Ok) (hU : D.U2 ≤ (rpg _ _).box fun v : Pl F => KD (cv v Δ) (Ov v))
    {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {x : DA Δ} {B : Base (SU Δ) (SA Δ) V} (hB : D.IsBS ch x B)
    (g : SA Δ) : B.Γ₀.relIndex ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) ≠ 0 := by
  have := h.real
  obtain ⟨n, hn, h1⟩ := den_DA ((g : DA Δ) * x)
  obtain ⟨n', hn', h2⟩ := den_DA ((g : DA Δ) * x)⁻¹
  rw [hB.Γ₀, Subgroup.relIndex_bot_left]
  refine Nat.card_ne_zero.2 ⟨inferInstance, ?_⟩
  refine ((fin_SU h.neg (n * n') (mul_ne_zero hn hn')).subset ?_).to_subtype
  rintro γ ⟨u, hu, e⟩ v i j
  have hk := Subgroup.mem_iInf.1 (hU ((hB.U u).1 hu))
  have := int_conj _ (x⁻¹ * (u : DA Δ) * x) hk h1 h2 v i j
  have e2 : (g : DA Δ) * x * (x⁻¹ * u * x) * ((g : DA Δ) * x)⁻¹ = (B.ι γ : DA Δ) := by
    rw [← e]
    change _ = (g : DA Δ) * u * (g : DA Δ)⁻¹
    group
  rw [e2, hB.ι] at this
  exact this

end UpperTheory.V.Z.Sym.Glob
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSApx
open NumberField IsDedekindDomain

namespace UpperTheory.V.Z.Sym.Glob

theorem apx {F : Type} [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (y : ∀ v : Pl F, Kv v)
    (hy : ∀ v, cv v d * y v ∈ v.adicCompletionIntegers F) : ∃ x : F, ∀ v, y v - cv v x ∈ v.adicCompletionIntegers F := by
  classical
  have hinv : ∀ᶠ v in Filter.cofinite, cv v d⁻¹ ∈ (v : Pl F).adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹).2
  have hev : ∀ᶠ v in Filter.cofinite, y v ∈ (v : Pl F).adicCompletionIntegers F := by
    refine hinv.mono fun v hv => ?_
    have e : y v = cv v d⁻¹ * (cv v d * y v) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul]
    rw [e]
    exact mul_mem hv (hy v)
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) (K := F)
    (RestrictedProduct.mk y hev : FiniteAdeleRing (𝓞 F) F)
  exact ⟨k, fun v => GroundTheory.Global.mem_integralFiniteAdeles.mp hk v⟩

end UpperTheory.V.Z.Sym.Glob
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSAbs
namespace UpperTheory.V.Z.Sym.Glob

private theorem exists_int_eq_mul_of_ne_zero_lattice {Λ : Type} [Ring Λ] [IsDomain Λ] [Module.Finite ℤ Λ]
    (y : Λ) (hy : y ≠ 0) : ∃ m : ℤ, m ≠ 0 ∧ ∃ t : Λ, y * t = (m : Λ) := by
  have hint : IsIntegral ℤ y := Algebra.IsIntegral.isIntegral y
  obtain ⟨p, hpm, hp⟩ := hint
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h0
    apply hq
    rw [map_zero, sub_zero]
    exact Polynomial.X_dvd_iff.mpr h0
  have hqy : Polynomial.aeval y q = 0 := by
    have h1 : Polynomial.aeval y p = 0 := hp
    rw [hpq, map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_zero, sub_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hy)
  have hcomm : Polynomial.aeval y q.divX * y = y * Polynomial.aeval y q.divX := by
    have e1 : Polynomial.aeval y (q.divX * Polynomial.X) = Polynomial.aeval y (Polynomial.X * q.divX) := by
      rw [mul_comm]
    simpa only [map_mul, Polynomial.aeval_X] using e1
  refine ⟨q.coeff 0, hq0, -Polynomial.aeval y q.divX, ?_⟩
  have e2 := congrArg (Polynomial.aeval y) (Polynomial.divX_mul_X_add q)
  rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hqy, hcomm, algebraMap_int_eq,
    eq_intCast] at e2
  rw [mul_neg]
  exact (eq_neg_of_add_eq_zero_right e2).symm

private theorem index_range_mulLeft_ne_zero {Λ : Type} [Ring Λ] [IsDomain Λ] [Module.Finite ℤ Λ]
    (y : Λ) (hy : y ≠ 0) : (AddMonoidHom.mulLeft y).range.index ≠ 0 := by
  obtain ⟨m, hm, t, ht⟩ := exists_int_eq_mul_of_ne_zero_lattice y hy
  show Nat.card (Λ ⧸ (AddMonoidHom.mulLeft y).range.toIntSubmodule) ≠ 0
  haveI : Finite (Λ ⧸ (AddMonoidHom.mulLeft y).range.toIntSubmodule) := by
    apply Module.finite_of_fg_torsion
    intro q
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submonoid.smul_def]
      show m • (Submodule.Quotient.mk z : Λ ⧸ (AddMonoidHom.mulLeft y).range.toIntSubmodule) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨t * z, ?_⟩
      show y * (t * z) = m • z
      rw [← mul_assoc, ht, zsmul_eq_mul]
  exact Nat.card_pos.ne'

private theorem index_range_mulLeft_eq_natAbs_det {Λ : Type} [Ring Λ] [IsDomain Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (y : Λ) (hy : y ≠ 0) : (AddMonoidHom.mulLeft y).range.index =
      (LinearMap.det (AddMonoidHom.mulLeft y).toIntLinearMap).natAbs := by
  set f := (AddMonoidHom.mulLeft y).toIntLinearMap with hf
  have hinj : Function.Injective f := fun a b hab => mul_left_cancel₀ hy hab
  have := Submodule.natAbs_det_equiv (LinearMap.range f) (LinearEquiv.ofInjective f hinj)
  have key : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      ((LinearEquiv.ofInjective f hinj : Λ →+ LinearMap.range f)).toIntLinearMap) = LinearMap.det f := by
    congr 1
  rw [key] at this
  rw [this]
  rfl

open Module in
private theorem short_lattice (Λ : Type) [Ring Λ] [IsDomain Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] :
    ∃ C : ℕ, ∀ I : AddSubgroup Λ, I.index ≠ 0 → ∃ y ∈ I, y ≠ 0 ∧
      (AddMonoidHom.mulLeft y).range.index ≠ 0 ∧ (AddMonoidHom.mulLeft y).range.index ≤ C * I.index := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ Λ) := b.index_nonempty
  have hr0 : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) ≠ 0 := Fintype.card_ne_zero
  let T : Module.Free.ChooseBasisIndex ℤ Λ → Module.Free.ChooseBasisIndex ℤ Λ →
      Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i k l => b.repr (b i * b l) k
  let B : ℕ := ∑ i, ∑ k, ∑ l, (T i k l).natAbs
  refine ⟨(Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ)).factorial *
    B ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ), fun I hI => ?_⟩
  have hex : ∃ m : ℕ, I.index < (m + 1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) :=
    ⟨I.index, lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_self_pow hr0 _)⟩
  obtain ⟨m, hmd, hmle⟩ : ∃ m : ℕ, I.index < (m + 1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) ∧
      m ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) ≤ I.index := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, zero_pow hr0]
      exact Nat.zero_le _
    · have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      have h2 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [h2] at h1
      exact not_lt.mp h1
  haveI : I.FiniteIndex := ⟨hI⟩
  letI : Fintype (Λ ⧸ I) := Fintype.ofFinite _
  let φ : (Module.Free.ChooseBasisIndex ℤ Λ → Fin (m + 1)) → Λ ⧸ I :=
    fun c => QuotientAddGroup.mk (∑ i, ((c i : ℕ) : ℤ) • b i)
  have hcard : Fintype.card (Λ ⧸ I) < Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ → Fin (m + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card]
    exact hmd
  obtain ⟨c, c', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hcard
  let g : Module.Free.ChooseBasisIndex ℤ Λ → ℤ := fun i => ((c' i : ℕ) : ℤ) - ((c i : ℕ) : ℤ)
  set y := ∑ i, g i • b i with hy
  have hyI : y ∈ I := by
    have := (QuotientAddGroup.eq).1 heq
    convert this using 1
    simp only [y, g, sub_smul, Finset.sum_sub_distrib]
    abel
  have hg : ∀ i, |g i| ≤ m := by
    intro i
    have h1 := (c i).is_lt
    have h2 := (c' i).is_lt
    simp only [g]
    rw [abs_le]
    constructor <;> omega
  have hy0 : y ≠ 0 := by
    intro h0
    apply hne
    funext i
    have := (Fintype.linearIndependent_iff.mp b.linearIndependent) g h0 i
    simp only [g, sub_eq_zero] at this
    exact Fin.ext (by exact_mod_cast this.symm)
  refine ⟨y, hyI, hy0, index_range_mulLeft_ne_zero y hy0, ?_⟩
  rw [index_range_mulLeft_eq_natAbs_det y hy0, ← LinearMap.det_toMatrix b]
  have hentry : ∀ k l, |LinearMap.toMatrix b b (AddMonoidHom.mulLeft y).toIntLinearMap k l| ≤ (m : ℤ) * B := by
    intro k l
    rw [LinearMap.toMatrix_apply]
    have e : b.repr ((AddMonoidHom.mulLeft y).toIntLinearMap (b l)) k = ∑ i, g i * T i k l := by
      show b.repr (y * b l) k = _
      rw [hy, Finset.sum_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [smul_mul_assoc, map_sum, map_zsmul, T]
      change (Finsupp.applyAddHom k) (∑ i, g i • b.repr (b i * b l)) = _
      rw [map_sum]
      simp only [Finsupp.applyAddHom_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [e]
    calc |∑ i, g i * T i k l| ≤ ∑ i, |g i * T i k l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (m : ℤ) * ((T i k l).natAbs : ℤ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul, Int.abs_eq_natAbs (T i k l)]
          exact mul_le_mul_of_nonneg_right (hg i) (by positivity)
      _ = (m : ℤ) * ∑ i, ((T i k l).natAbs : ℤ) := by rw [Finset.mul_sum]
      _ ≤ (m : ℤ) * B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simp only [B, Nat.cast_sum]
          apply Finset.sum_le_sum
          intro i _
          calc ((T i k l).natAbs : ℤ) ≤ ∑ l', ((T i k l').natAbs : ℤ) :=
                Finset.single_le_sum (f := fun l' => ((T i k l').natAbs : ℤ))
                  (fun _ _ => by positivity) (Finset.mem_univ l)
            _ ≤ ∑ k', ∑ l', ((T i k' l').natAbs : ℤ) :=
                Finset.single_le_sum (f := fun k' => ∑ l', ((T i k' l').natAbs : ℤ))
                  (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (Finset.mem_univ k)
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs) (fun k l => hentry k l)
  have key : (((LinearMap.toMatrix b b (AddMonoidHom.mulLeft y).toIntLinearMap).det.natAbs : ℕ) : ℤ) ≤
      (((Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ)).factorial *
        B ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) * I.index : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    calc |(LinearMap.toMatrix b b (AddMonoidHom.mulLeft y).toIntLinearMap).det|
        ≤ (Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ)).factorial •
            ((m : ℤ) * B) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) := hdet
      _ = ((Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ)).factorial : ℤ) *
            (B : ℤ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) *
            ((m ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) : ℕ) : ℤ) := by
          rw [nsmul_eq_mul, mul_pow]
          push_cast
          ring
      _ ≤ ((Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ)).factorial : ℤ) *
            (B : ℤ) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) * (I.index : ℤ) := by
          gcongr
      _ = _ := by push_cast; ring
  exact_mod_cast key

private theorem short_abs {D M Γ G : Type} [Ring D] [IsDomain D] [CharZero D] [Ring M] [Group Γ] [Group G] (j : D →+* M) (R : Subring M)
    [Module.Finite ℤ (R.comap j)] (ψ : G →* Mˣ) (ι : Γ →* G)
    (hΓ : ∀ x : D, x ≠ 0 → ∃ γ, (ψ (ι γ) : M) = j x) (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ψ g ∈ R)
    (hdense : ∀ r ∈ R, ∀ n : ℕ, n ≠ 0 → ∃ x : D, ∃ r' ∈ R, r = j x + n * r') :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ g : G, ∃ γ : Γ, (ψ (g⁻¹ * ι γ) : M) ∈ R ∧ (N : M) * ψ ((ι γ)⁻¹ * g) ∈ R := by
  classical
  haveI : Module.Free ℤ (R.comap j) := Module.free_of_finite_type_torsion_free'
  obtain ⟨C, hC⟩ := short_lattice (R.comap j)
  refine ⟨C.factorial, Nat.factorial_ne_zero C, ?_⟩
  have core : ∀ h : G, (ψ h : M) ∈ R → ∀ k : ℕ, k ≠ 0 → (k : M) * (ψ h⁻¹ : M) ∈ R →
      ∃ γ : Γ, (ψ (h⁻¹ * ι γ) : M) ∈ R ∧ (C.factorial : M) * ψ ((ι γ)⁻¹ * h) ∈ R := by
    intro h hu k hk hk'
    set w : M := ((ψ h⁻¹ : Mˣ) : M) with hw
    have hwu : w * (ψ h : M) = 1 := by
      rw [hw, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    let J : AddSubgroup (R.comap j) :=
      { carrier := {x | w * j (x : D) ∈ R}
        add_mem' := fun {a b} ha hb => by
          show w * j ((a : D) + b) ∈ R
          rw [map_add (f := _), mul_add]
          exact R.add_mem ha hb
        zero_mem' := by
          show w * j 0 ∈ R
          rw [map_zero, mul_zero]
          exact R.zero_mem
        neg_mem' := fun {a} ha => by
          show w * j (-(a : D)) ∈ R
          rw [map_neg, mul_neg]
          exact R.neg_mem ha }
    have hJmem : ∀ x : R.comap j, x ∈ J ↔ w * j (x : D) ∈ R := fun x => Iff.rfl
    have hkJ : ∀ s : R.comap j, k • s ∈ J := by
      intro s
      rw [hJmem]
      show w * j (k • (s : D)) ∈ R
      rw [map_nsmul, nsmul_eq_mul, ← mul_assoc, ← (Nat.cast_commute k w).eq]
      exact R.mul_mem hk' s.2
    have hJidx : J.index ≠ 0 := by
      show Nat.card ((R.comap j) ⧸ J.toIntSubmodule) ≠ 0
      haveI : Finite ((R.comap j) ⧸ J.toIntSubmodule) := by
        apply Module.finite_of_fg_torsion
        intro q
        refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk)⟩, ?_⟩
        induction q using Submodule.Quotient.induction_on with
        | H z =>
          rw [Submonoid.smul_def]
          show (k : ℤ) • (Submodule.Quotient.mk z : (R.comap j) ⧸ J.toIntSubmodule) = 0
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, natCast_zsmul]
          exact hkJ z
      exact Nat.card_pos.ne'
    obtain ⟨y, hyJ, hy0, hyi0, hyC⟩ := hC J hJidx
    set H := (AddMonoidHom.mulLeft y).range with hH
    have hHJ : H ≤ J := by
      rintro _ ⟨s, rfl⟩
      show w * j ((y : D) * s) ∈ R
      rw [map_mul, ← mul_assoc]
      exact R.mul_mem hyJ s.2
    have hrel := AddSubgroup.relIndex_mul_index hHJ
    have hd0 : H.relIndex J ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hrel
      exact hyi0 hrel.symm
    have hdC : H.relIndex J ≤ C := by
      have h1 : H.relIndex J * J.index ≤ C * J.index := by rw [hrel]; exact hyC
      exact Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hJidx)
    obtain ⟨e, he⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hd0) hdC
    set d := H.relIndex J with hd
    have hmem : ∀ x ∈ J, d • x ∈ H := by
      intro x hx
      have := AddSubgroup.nsmul_index_mem (H.addSubgroupOf J) ⟨x, hx⟩
      rw [AddSubgroup.mem_addSubgroupOf] at this
      simpa [hd, AddSubgroup.relIndex] using this
    obtain ⟨x₀, r', hr', hx₀⟩ := hdense _ hu k hk
    have hx₀S : j x₀ ∈ R := by
      have e0 : j x₀ = (ψ h : M) - (k : M) * r' := by rw [hx₀]; abel
      rw [e0]
      exact R.sub_mem hu (R.mul_mem (natCast_mem R k) hr')
    have hX₀J : (⟨x₀, hx₀S⟩ : R.comap j) ∈ J := by
      show w * j x₀ ∈ R
      have e0 : w * j x₀ = 1 - ((k : M) * w) * r' := by
        rw [(Nat.cast_commute k w).eq]
        have : j x₀ = (ψ h : M) - (k : M) * r' := by rw [hx₀]; abel
        rw [this, mul_sub, hwu, mul_assoc]
      rw [e0]
      exact R.sub_mem R.one_mem (R.mul_mem hk' hr')
    have hKJ : (k : R.comap j) ∈ J := by
      have := hkJ 1
      rwa [nsmul_eq_mul, mul_one] at this
    obtain ⟨s₁, hs₁⟩ := hmem _ hX₀J
    obtain ⟨s₂, hs₂⟩ := hmem _ hKJ
    have c1 : j (y : D) * j (s₁ : D) = d • j x₀ := by
      rw [← map_mul, ← map_nsmul]
      exact congrArg (fun v : R.comap j => j (v : D)) hs₁
    have c2 : j (y : D) * j (s₂ : D) = d • (k : M) := by
      have := congrArg (fun v : R.comap j => j (v : D)) hs₂
      simpa [map_nsmul] using this
    have hy0' : (y : D) ≠ 0 := fun h0 => hy0 (Subtype.ext h0)
    obtain ⟨γ, hγ⟩ := hΓ (y : D) hy0'
    refine ⟨γ, ?_, ?_⟩
    · rw [map_mul, Units.val_mul, hγ]
      exact hyJ
    · have hvy : ((ψ (ι γ))⁻¹ : Mˣ) * j (y : D) = (1 : M) := by
        rw [← hγ, Units.inv_mul]
      have e1 : d • (ψ h : M) = j (y : D) * j (s₁ : D) + j (y : D) * j (s₂ : D) * r' := by
        rw [hx₀, smul_add, ← smul_mul_assoc, c1, c2]
      rw [map_mul, map_inv, Units.val_mul, ← nsmul_eq_mul, he, mul_comm, mul_smul,
        ← mul_smul_comm, e1]
      simp only [mul_add, ← mul_assoc, hvy, one_mul]
      exact nsmul_mem (R.add_mem s₁.2 (R.mul_mem s₂.2 hr')) e
  intro g
  obtain ⟨n, hn, hnR⟩ := hden g
  obtain ⟨n', hn', hn'R⟩ := hden g⁻¹
  obtain ⟨γn, hγn⟩ := hΓ (n : D) (by exact_mod_cast hn)
  have hv : ((ψ (ι γn) : Mˣ) : M) = (n : M) := by rw [hγn, map_natCast]
  have hu : (ψ (ι γn * g) : M) ∈ R := by
    rw [map_mul, Units.val_mul, hv]
    exact hnR
  have hk : ((n' * n : ℕ) : M) * (ψ (ι γn * g)⁻¹ : M) ∈ R := by
    have hc : (n : M) * (ψ g⁻¹ : M) = (ψ g⁻¹ : M) * n := Nat.cast_commute n _
    have eq : ((n' * n : ℕ) : M) * (ψ (ι γn * g)⁻¹ : M) = (n' : M) * ψ g⁻¹ := by
      rw [mul_inv_rev, map_mul, map_inv ψ (ι γn), Units.val_mul, Nat.cast_mul, mul_assoc,
        ← mul_assoc (n : M), hc, mul_assoc, ← hv, Units.mul_inv, mul_one]
    rw [eq]
    exact hn'R
  obtain ⟨γ', h1, h2⟩ := core _ hu (n' * n) (Nat.mul_ne_zero hn' hn) hk
  refine ⟨γn⁻¹ * γ', ?_, ?_⟩
  · have e : g⁻¹ * ι (γn⁻¹ * γ') = (ι γn * g)⁻¹ * ι γ' := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact h1
  · have e : (ι (γn⁻¹ * γ'))⁻¹ * g = (ι γ')⁻¹ * (ι γn * g) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact h2

theorem cls_abs_unit {D M Γ G : Type} [Ring D] [IsDomain D] [CharZero D] [Ring M] [Group Γ] [Group G] (j : D →+* M) (R : Subring M)
    [Module.Finite ℤ (R.comap j)] (ψ : G →* Mˣ) (ι : Γ →* G) (K : Subgroup G)
    (hK : ∀ k, (ψ k : M) ∈ R → (ψ k⁻¹ : M) ∈ R → k ∈ K)
    (hΓ : ∀ x : D, x ≠ 0 → ∃ γ, (ψ (ι γ) : M) = j x) (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ψ g ∈ R)
    (hdense : ∀ r ∈ R, ∀ n : ℕ, n ≠ 0 → ∃ x : D, ∃ r' ∈ R, r = j x + n * r') :
    ∃ Y : Finset G, ∀ g, ∃ γ, ∃ y ∈ Y, ∃ k ∈ K, g = ι γ * y * k := by
  classical
  obtain ⟨N, hN0, hN⟩ := short_abs j R ψ ι hΓ hden hdense
  choose γf hγ1 hγ2 using hN
  have hx : ∀ g, ∃ x : R.comap j, ∃ r' ∈ R,
      (ψ (g⁻¹ * ι (γf g)) : M) = j x + (N : M) * r' := by
    intro g
    obtain ⟨x, r', hr', he⟩ := hdense _ (hγ1 g) N hN0
    refine ⟨⟨x, ?_⟩, r', hr', he⟩
    have hjx : j x = (ψ (g⁻¹ * ι (γf g)) : M) - (N : M) * r' := by rw [he]; abel
    show j x ∈ R
    rw [hjx]
    exact R.sub_mem (hγ1 g) (R.mul_mem (natCast_mem R N) hr')
  choose xf rf hrf hxf using hx
  let P : Submodule ℤ (R.comap j) := LinearMap.range ((N : ℤ) • LinearMap.id)
  haveI hfin : Finite ((R.comap j) ⧸ P) := by
    apply Module.finite_of_fg_torsion
    intro q
    refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0)⟩, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submonoid.smul_def]
      show (N : ℤ) • (Submodule.Quotient.mk z : (R.comap j) ⧸ P) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨z, rfl⟩
  letI := Fintype.ofFinite ((R.comap j) ⧸ P)
  let qf : G → (R.comap j) ⧸ P := fun g => Submodule.Quotient.mk (xf g)
  let rep : (R.comap j) ⧸ P → G := fun q =>
    if h : ∃ g, qf g = q then (ι (γf h.choose))⁻¹ * h.choose else 1
  refine ⟨Finset.univ.image rep, fun g => ?_⟩
  have hex : ∃ g', qf g' = qf g := ⟨g, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g', g' = hex.choose := ⟨_, rfl⟩
  have hq : qf g' = qf g := hg' ▸ hex.choose_spec
  have hrep : rep (qf g) = (ι (γf g'))⁻¹ * g' := by
    simp only [rep, dif_pos hex, hg']
  refine ⟨γf g, rep (qf g), Finset.mem_image_of_mem _ (Finset.mem_univ _),
    (rep (qf g))⁻¹ * ((ι (γf g))⁻¹ * g), ?_, by group⟩
  rw [hrep]
  obtain ⟨z, hz⟩ : xf g' - xf g ∈ P := (Submodule.Quotient.eq P).1 hq
  have hz' : j (xf g' : D) = j (xf g : D) + (N : M) * j (z : D) := by
    have h1 : ((xf g' : R.comap j) : D) = (xf g : D) + (N : D) * (z : D) := by
      have := congrArg (fun w : R.comap j => (w : D)) hz
      have h2 : (N : D) * (z : D) = (xf g' : D) - (xf g : D) := by
        simpa [zsmul_eq_mul] using this
      rw [h2]
      abel
    rw [h1, map_add (f := _), map_mul, map_natCast]
  set a : M := (ψ (g⁻¹ * ι (γf g)) : M) with ha
  set a' : M := (ψ (g'⁻¹ * ι (γf g')) : M) with ha'
  set b : M := (ψ ((ι (γf g))⁻¹ * g) : M) with hb
  set b' : M := (ψ ((ι (γf g'))⁻¹ * g') : M) with hb'
  set t : M := j (z : D) + rf g' - rf g with ht
  have htR : t ∈ R := R.sub_mem (R.add_mem z.2 (hrf g')) (hrf g)
  have haa : a' = a + (N : M) * t := by
    rw [ha', hxf g', ha, hxf g, hz', ht]
    noncomm_ring
  have hab : a * b = 1 := by
    rw [ha, hb, ← Units.val_mul, ← map_mul]
    have : (g⁻¹ * ι (γf g)) * ((ι (γf g))⁻¹ * g) = 1 := by group
    rw [this, map_one, Units.val_one]
  have hab' : a' * b' = 1 := by
    rw [ha', hb', ← Units.val_mul, ← map_mul]
    have : (g'⁻¹ * ι (γf g')) * ((ι (γf g'))⁻¹ * g') = 1 := by group
    rw [this, map_one, Units.val_one]
  have hNt : (N : M) * t = t * (N : M) := (Nat.cast_commute N t)
  apply hK
  · have e : ((ι (γf g'))⁻¹ * g')⁻¹ * ((ι (γf g))⁻¹ * g) =
        (g'⁻¹ * ι (γf g')) * ((ι (γf g))⁻¹ * g) := by group
    rw [e, map_mul, Units.val_mul, ← ha', ← hb, haa, add_mul, hab, hNt, mul_assoc]
    exact R.add_mem R.one_mem (R.mul_mem htR (hγ2 g))
  · have e : (((ι (γf g'))⁻¹ * g')⁻¹ * ((ι (γf g))⁻¹ * g))⁻¹ =
        (g⁻¹ * ι (γf g)) * ((ι (γf g'))⁻¹ * g') := by group
    have haa2 : a = a' - (N : M) * t := by rw [haa]; abel
    rw [e, map_mul, Units.val_mul, ← ha, ← hb', haa2, sub_mul, hab', hNt, mul_assoc]
    exact R.sub_mem R.one_mem (R.mul_mem htR (hγ2 g'))

end UpperTheory.V.Z.Sym.Glob
end

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

variable {F : Type} [Field F] [NumberField F] {Δ : F}

private abbrev MA (Δ : F) : Type := ∀ v : Pl F, Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v Δ))

private def RA (Δ : F) : Subring (MA Δ) where
  carrier := {m | ∀ v, m v ∈ Dm (cv v Δ) ∧ ∀ i j, IsIntegral (Ov v) (m v i j)}
  mul_mem' {a b} ha hb v := ⟨mul_mem (ha v).1 (hb v).1, fun i j => by
    rw [Pi.mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    exact (((ha v).2 _ _).mul ((hb v).2 _ _)).add (((ha v).2 _ _).mul ((hb v).2 _ _))⟩
  one_mem' v := ⟨one_mem _, fun i j => by
    by_cases h : i = j <;> simp [Matrix.one_apply, h, isIntegral_one, isIntegral_zero]⟩
  add_mem' {a b} ha hb v := ⟨add_mem (ha v).1 (hb v).1, fun i j => ((ha v).2 i j).add ((hb v).2 i j)⟩
  zero_mem' v := ⟨zero_mem _, fun _ _ => isIntegral_zero⟩
  neg_mem' {a} ha v := ⟨neg_mem (ha v).1, fun i j => ((ha v).2 i j).neg⟩

private def jA (Δ : F) : Dm Δ →+* MA Δ := RingHom.pi fun v => (lmap (cv v) Δ).mapMatrix.comp (Dm Δ).subtype

private def psiA (Δ : F) : DA Δ →* (MA Δ)ˣ :=
  MonoidHom.toHomUnits (MonoidHom.pi fun v : Pl F =>
    (Units.coeHom _).comp ((DX (cv v Δ)).subtype.comp ((rpg _ fun v : Pl F => KD (cv v Δ) (Ov v)).p v)))

private theorem psiA_apply (g : DA Δ) (v : Pl F) : (psiA Δ g : MA Δ) v = mt (g.1 v) := rfl

theorem Dm_unit [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (x : Dm Δ) (hx : x ≠ 0) :
    IsUnit (x : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_Dm x.2]
  refine IsUnit.map _ (Ne.isUnit fun h => hx ?_)
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  set σ := (IsTotallyReal.complexEmbedding_isReal φ).embedding
  have hs := congrArg σ h
  simp only [map_sub, map_add (f := _), map_mul, map_pow, map_zero] at hs
  have hn := neg_pos.2 (hneg σ)
  have p1 := mul_nonneg hn.le (sq_nonneg (σ (x.1 0 0).im))
  have p2 := mul_nonneg hn.le (sq_nonneg (σ (x.1 0 1).im))
  have p3 := sq_nonneg (σ (x.1 0 0).re)
  have p4 := sq_nonneg (σ (x.1 0 1).re)
  have z : ∀ t : F, σ t ^ 2 = 0 → t = 0 := fun t ht => by simpa using ht
  have z' : ∀ t : F, -σ Δ * σ t ^ 2 = 0 → t = 0 := fun t ht => z t ((mul_eq_zero.1 ht).resolve_left hn.ne')
  have e0 : x.1 0 0 = 0 := QuadraticAlgebra.ext (z _ (by linarith)) (z' _ (by linarith))
  have e1 : x.1 0 1 = 0 := QuadraticAlgebra.ext (z _ (by linarith)) (z' _ (by linarith))
  refine Subtype.ext ?_
  ext i j : 1
  fin_cases i <;> fin_cases j
  · exact e0
  · exact e1
  · exact x.2.2.trans (by simp [e1])
  · exact x.2.1.trans (by simp [e0])

private theorem finite_lat (hΔ : Δ ≠ 0) : Module.Finite ℤ ((RA Δ).comap (jA Δ)) := by
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul Δ
  have hc : (2 * m * Δ : F) ≠ 0 := by simp [hΔ, hm0]
  have hi := fun (y : (RA Δ).comap (jA Δ)) i => coords_glob (a := y.1.1 0 i) (fun v => (y.2 v).2 0 i) hm
  let ψ : (RA Δ).comap (jA Δ) →+ (Fin 2 → 𝓞 F × 𝓞 F) :=
    { toFun := fun y i => (⟨_, (hi y i).1⟩, ⟨_, (hi y i).2⟩)
      map_zero' := funext fun i => Prod.ext (Subtype.ext (mul_zero _)) (Subtype.ext (mul_zero _))
      map_add' := fun x y => funext fun i => Prod.ext (Subtype.ext (mul_add _ _ _)) (Subtype.ext (mul_add _ _ _)) }
  refine Module.Finite.of_injective ψ.toIntLinearMap fun x y h => Subtype.ext (Subtype.ext ?_)
  have e : ∀ i, x.1.1 0 i = y.1.1 0 i := fun i => QuadraticAlgebra.ext
    (mul_left_cancel₀ hc (congrArg (fun p : 𝓞 F × 𝓞 F => (p.1 : F)) (congrFun h i)))
    (mul_left_cancel₀ hc (congrArg (fun p : 𝓞 F × 𝓞 F => (p.2 : F)) (congrFun h i)))
  ext i j : 1
  fin_cases i <;> fin_cases j
  · exact e 0
  · exact e 1
  · exact x.1.2.2.trans (e 1 ▸ y.1.2.2.symm)
  · exact x.1.2.1.trans (e 0 ▸ y.1.2.1.symm)

private theorem apx_alg {K K' O : Type} [Field K] [Field K'] [CommRing O] [Algebra O K'] (f : K →+* K') (Δ : K) (a : Lsq K' (f Δ))
    (n m : ℕ) (x1 x2 : K) (h : f ((n : K) * m) ≠ 0) (hm : IsIntegral O (f ((m : K) * Δ)))
    (h1 : IsIntegral O ((f ((n : K) * m))⁻¹ * a.re - f x1)) (h2 : IsIntegral O ((f ((n : K) * m))⁻¹ * a.im - f x2)) :
    ∃ r : Lsq K' (f Δ), IsIntegral O r ∧ a = lmap f Δ ⟨n * m * x1, n * m * x2⟩ + n * r := by
  simp only [map_mul, map_natCast] at h hm h1 h2
  refine ⟨_, isIntegral_of_coords (a := ⟨((n : K') * m)⁻¹ * a.re - f x1, ((n : K') * m)⁻¹ * a.im - f x2⟩)
    (isIntegral_natCast m) hm h1 h2, ?_⟩
  have hn := left_ne_zero_of_mul h
  have hm' := right_ne_zero_of_mul h
  ext <;> simp [lmap] <;> field_simp <;> ring

private theorem apx_den {K K' O : Type} [Field K] [Field K'] [CommRing O] [Algebra O K'] (f : K →+* K') (Δ : K) (a : Lsq K' (f Δ))
    (ha : IsIntegral O a) (m : ℕ) (c : K) (h : f c ≠ 0) (hm : IsIntegral O (f ((m : K) * Δ))) :
    IsIntegral O (f (2 * m * Δ * c) * ((f c)⁻¹ * a.re)) ∧ IsIntegral O (f (2 * m * Δ * c) * ((f c)⁻¹ * a.im)) := by
  simp only [map_mul, map_natCast, map_ofNat, mul_assoc _ (f c), mul_inv_cancel_left₀ h] at hm ⊢
  exact isIntegral_coords ha (isIntegral_natCast m) hm

theorem apx_L (hΔ : Δ ≠ 0) (a : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)) (ha : ∀ v, IsIntegral (Ov v) (a v)) (n : ℕ) (hn : n ≠ 0) :
    ∃ (x : Lsq F Δ) (r : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)), ∀ v, IsIntegral (Ov v) (r v) ∧ a v = lmap (cv v) Δ x + n * r v := by
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul Δ
  have hc : (2 * m * Δ * (n * m) : F) ≠ 0 := by simp [hΔ, hm0, hn]
  have hmv := isIntegral_glob.1 hm
  have hnm : ∀ v : Pl F, cv v ((n : F) * m) ≠ 0 := fun v => (_root_.map_ne_zero _).2 (by simp [hm0, hn])
  have hi := fun v => apx_den (cv v) Δ (a v) (ha v) m _ (hnm v) (hmv v)
  obtain ⟨x1, h1⟩ := apx _ hc _ fun v => isIntegral_Ov.1 (hi v).1
  obtain ⟨x2, h2⟩ := apx _ hc _ fun v => isIntegral_Ov.1 (hi v).2
  choose r hr using fun v => apx_alg (O := Ov v) (cv v) Δ (a v) n m x1 x2 (hnm v) (hmv v) (isIntegral_Ov.2 (h1 v))
    (isIntegral_Ov.2 (h2 v))
  exact ⟨_, r, hr⟩

private theorem dense_lat (hΔ : Δ ≠ 0) (r : MA Δ) (hr : r ∈ RA Δ) (n : ℕ) (hn : n ≠ 0) :
    ∃ x : Dm Δ, ∃ r' ∈ RA Δ, r = jA Δ x + n * r' := by
  choose x s h using fun i => apx_L hΔ (fun v => r v 0 i) (fun v => (hr v).2 0 i) n hn
  refine ⟨⟨!![x 0, x 1; -star (x 1), star (x 0)], rfl, rfl⟩, fun v => !![s 0 v, s 1 v; -star (s 1 v), star (s 0 v)],
    fun v => ⟨⟨rfl, rfl⟩, fun i j => ?_⟩, funext fun v => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact (h 0 v).1
    · exact (h 1 v).1
    · exact (isIntegral_star (h 1 v).1).neg
    · exact isIntegral_star (h 0 v).1
  · have e : ∀ y : Lsq F Δ, lmap (cv v) Δ (star y) = star (lmap (cv v) Δ y) := fun y => by ext <;> simp [lmap]
    rw [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, ← nsmul_eq_mul]
    ext i j : 1
    fin_cases i <;> fin_cases j
    · simpa [jA] using (h 0 v).2
    · simpa [jA] using (h 1 v).2
    · refine (hr v).1.2.trans ?_
      rw [(h 1 v).2]
      simp [jA, e, add_comm]
    · refine (hr v).1.1.trans ?_
      rw [(h 0 v).2]
      simp [jA, e]

theorem clsD [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    ∃ Y : Finset (DA Δ), ∀ g, ∃ γ, ∃ y ∈ Y, ∃ k ∈ (rpg _ _).box (fun v : Pl F => KD (cv v Δ) (Ov v)), g = ι γ * y * k := by
  have hΔ := ne_zero_of_neg hneg
  have := finite_lat hΔ
  have : CharZero (Dm Δ) := ⟨fun a b h => by
    have h1 := congrArg (fun x : Dm Δ => (x.1 0 0).re) h
    simpa [Matrix.natCast_apply] using h1⟩
  have : NoZeroDivisors (Dm Δ) := ⟨fun {a b} h => or_iff_not_imp_left.2 fun ha =>
    Subtype.ext ((Dm_unit hneg a ha).mul_right_eq_zero.1 (congrArg Subtype.val h))⟩
  have : IsDomain (Dm Δ) := NoZeroDivisors.to_isDomain _
  refine cls_abs_unit (jA Δ) (RA Δ) (psiA Δ) ι _ (fun k h1 h2 => Subgroup.mem_iInf.2 fun v => mem_KD.2 ⟨(h1 v).2, (h2 v).2⟩)
    (fun x hx => ?_) (fun g => ?_) (dense_lat hΔ)
  · refine ⟨⟨(Dm_unit hneg x hx).unit, mem_DX.2 x.2⟩, funext fun v => ?_⟩
    rw [psiA_apply, hι]
    rfl
  · obtain ⟨n, hn, h⟩ := den_DA g
    refine ⟨n, hn, fun v => ⟨mul_mem (natCast_mem _ n) (mt_mem _), fun i j => ?_⟩⟩
    rw [Pi.mul_apply, Pi.natCast_apply, ← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul]
    exact h v i j

end UpperTheory.V.Z.Sym.Glob
