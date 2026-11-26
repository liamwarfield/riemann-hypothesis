module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowFMul
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IwasawaDecompositionFiniteAdeles
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DRepsP

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATransP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aTrans : ATrans := by
  intro F _ _ _
  classical
  let b := mixedEmbedding.latticeBasis F
  refine ⟨(∑ i, ‖b i‖) + 1, by positivity, fun x => ?_⟩
  let p : mixedEmbedding.mixedSpace F := (fun w => x w.1, 0)
  have hm : (ZSpan.floor b p : mixedEmbedding.mixedSpace F) ∈
      Submodule.span ℤ (Set.range b) := (ZSpan.floor b p).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨s, hs⟩ := hm
  refine ⟨-(s : F), (RingOfIntegers.isIntegral_coe s).neg, fun v => ?_⟩
  have h1 := ZSpan.norm_fract_le b p
  have h2 : (ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩ = x v + sg v (-(s : F)) := by
    rw [ZSpan.fract_apply, ← hs]
    simp [p, sg, sub_eq_add_neg]
  have h3 : ‖(ZSpan.fract b p).1 ⟨v, IsTotallyReal.isReal v⟩‖ ≤ ‖ZSpan.fract b p‖ :=
    (norm_le_pi_norm _ _).trans (norm_fst_le _)
  rw [h2, Real.norm_eq_abs] at h3
  linarith

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DGoodP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.GoodOperatorConjugation

variable {F : Type} [Field F] [NumberField F]

theorem v_lt_of_max {w : Pl F} {y : w.adicCompletionIntegers F}
    (hy : y ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F)) : Valued.v (y : w.adicCompletion F) < 1 := by
  refine lt_of_le_of_ne y.2 fun h1 => mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hy) ?_
  have h0 : (y : w.adicCompletion F) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have hi : (y : w.adicCompletion F)⁻¹ ∈ w.adicCompletionIntegers F := by
    show Valued.v ((y : w.adicCompletion F)⁻¹) ≤ 1
    rw [map_inv₀, h1, inv_one]
  exact ⟨⟨y, ⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

theorem congruence_subgroup_entry_valuations_alt {w : Pl F} {c : ℕ} (hc : c ≠ 0) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w c) :
    (∀ a b, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) a b) ≤ 1) ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) < 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) < 1 := by
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := Subgroup.mem_comap.1 hk
  change ![(0 : (w.adicCompletionIntegers F) ⧸ (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)), 1] ᵥ* _ =
    ![0, 1] at hk'
  rw [funext_iff, Fin.forall_fin_two] at hk'
  simp [Matrix.vecMul, dotProduct] at hk'
  obtain ⟨h1, h2⟩ := hk'
  have hle : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.pow_le_self hc
  refine ⟨fun a b => (k a b).2, v_lt_of_max (hle ?_), ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  · have : k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) :=
      hle (Ideal.Quotient.eq.1 (by rw [h2, map_one]))
    have h3 := v_lt_of_max this
    simpa using h3

theorem tr_conj {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.trace T := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem det_conj' {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.det (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.det T := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]

variable [IsTotallyReal F]

theorem good_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) : (mkDat c χ).Good a := by
  intro f hf x h
  have hf' : ∀ g (h : Hc c), f (g * h) = χ h * f g := hf
  have hzc : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  have hχz : ∀ z, χ ⟨zc F z, hzc z⟩ = ω.1 (finId F z) := fun z =>
    (hχ ⟨zc F z, hzc z⟩).2 1 (Subgroup.one_mem _) z (one_mul _).symm
  have hK : f ∈ Hi.fixd (Hi.rtr ℂ (GF F) ℂ) (Kc c) := by
    intro u hu
    funext g
    have hu' : u ∈ Hc c := Subgroup.mem_sup_left hu
    have h1 : χ ⟨u, hu'⟩ = 1 := by
      rw [(hχ ⟨u, hu'⟩).2 u hu 1 (by rw [map_one, mul_one]), map_one, map_one]
    rw [Hi.rtr_apply, hf' g ⟨u, hu'⟩, h1, Units.val_one, one_mul]
  have hs := (ha.act (GF F → ℂ) (Hi.rtr ℂ (GF F) ℂ) f hK).1
  obtain ⟨k, hk, z, hz⟩ := (hχ h).1
  have hfix := congrFun (hs k hk) x
  simp only [Hi.rtr_apply, Finset.sum_apply] at hfix
  change ∑ i, f (x * (h : GF F) * a i) = (χ h : ℂ) * ∑ i, f (x * a i)
  rw [(hχ h).2 k hk z hz, ← hχz z, ← hfix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hz, ← hf' (x * k * a i) ⟨zc F z, hzc z⟩]
  have hc := Subgroup.mem_center_iff.1 (zc_center z) (a i)
  congr 1
  simp only [mul_assoc]
  rw [hc]

theorem reg_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) {w : Pl F} (hw : w ∈ W) (hc : c w ≠ 0) : (mkDat c χ).Reg a := by
  classical
  intro γ x i hmem
  obtain ⟨k, hk, z, hz⟩ := (hχ ⟨_, hmem⟩).1
  have hz' : (a i)⁻¹ * (x⁻¹ * jF F γ * x) = k * zc F z := hz
  have e : x⁻¹ * jF F γ * x = a i * (k * zc F z) := by rw [← hz', mul_inv_cancel_left]
  obtain ⟨u, hu⟩ := ha.loc i w hc
  let φ : GF F →* GL (Fin 2) (w.adicCompletion F) := Matrix.GeneralLinearGroup.map (pLoc F w)
  let ψ : F →+* w.adicCompletion F := (pLoc F w).comp (algebraMap F (Af F))
  let r : ℕ := W.count w
  have hr : 0 < r := List.count_pos_iff.2 hw
  let p : w.adicCompletion F := ((atFin w (unif w) ^ r : (w.adicCompletion F)ˣ) : w.adicCompletion F)
  let zw : w.adicCompletion F := pLoc F w (z : Af F)
  have e2 := congrArg (fun g => ((φ g : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) e
  simp only [map_mul, map_inv, Units.val_mul] at e2
  obtain ⟨M, hMk⟩ : ∃ M : Matrix (Fin 2) (Fin 2) (w.adicCompletion F),
      ((φ k : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) = M := ⟨_, rfl⟩
  rw [hMk] at e2
  have hA : ((φ (a i) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![p, (u : w.adicCompletion F); 0, 1] := by
    rw [show φ (a i) = _ from hu]; rfl
  have hZ : ((φ (zc F z) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![zw, 0; 0, zw] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, zw, zc, Matrix.GeneralLinearGroup.map]
  have hT : ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![ψ (γ 0 0), ψ (γ 0 1); ψ (γ 1 0), ψ (γ 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have htr : ψ (γ.val.trace) = zw * (p * M 0 0 + u * M 1 0 + M 1 1) := by
    have := tr_conj (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of,
      Matrix.trace_fin_two_of] at this
    rw [Matrix.trace_fin_two, map_add (f := _)]
    change ψ (γ 0 0) + ψ (γ 1 1) = _
    rw [← this]; ring
  have hdet : ψ (γ.val.det) = zw ^ 2 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
    have := det_conj' (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.det_fin_two_of,
      Matrix.det_fin_two_of] at this
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
    change ψ (γ 0 0) * ψ (γ 1 1) - ψ (γ 0 1) * ψ (γ 1 0) = _
    rw [← this]; ring

  have hkl : φ k ∈ K1 w (c w) := Subgroup.mem_iInf.1 hk w
  obtain ⟨hM, hM10, hM11⟩ := congruence_subgroup_entry_valuations_alt hc hkl
  simp only [hMk] at hM hM10 hM11
  have hp : Valued.v p < 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    have h2 : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    show Valued.v (((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ^ r) < 1
    rw [map_pow, h1]
    exact pow_lt_one₀ zero_le h2 hr.ne'
  have hu1 : Valued.v (u : w.adicCompletion F) ≤ 1 := u.2
  have ht : Valued.v (p * M 0 0 + u * M 1 0 + M 1 1) = 1 := by
    have h1 : Valued.v (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) < 1 := by
      refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) hM11
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' (hM 0 0)) hp
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hu1) hM10
    rw [show p * M 0 0 + u * M 1 0 + M 1 1 = 1 + (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) by ring]
    exact Valuation.map_one_add_of_lt _ h1
  have hzw : zw ≠ 0 := (Units.map (pLoc F w).toMonoidHom z).ne_zero
  have ht0 : p * M 0 0 + u * M 1 0 + M 1 1 ≠ 0 := fun e => by rw [e, map_zero] at ht; exact zero_ne_one ht
  refine ⟨fun h0 => ?_, fun h4 => ?_⟩
  · rw [h0, map_zero] at htr
    exact mul_ne_zero hzw ht0 htr.symm
  · have h5 := congrArg ψ h4
    rw [map_pow, map_mul, htr, hdet, map_ofNat] at h5
    have h6 : (p * M 0 0 + u * M 1 0 + M 1 1) ^ 2 = 4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hzw)
      linear_combination h5
    have h7 := congrArg Valued.v h6
    rw [map_pow, ht, one_pow] at h7
    have h4v : Valued.v (4 : w.adicCompletion F) ≤ 1 := by
      have := natCast_mem (w.adicCompletionIntegers F) 4
      rw [Nat.cast_ofNat] at this
      exact this
    have hd : Valued.v (M 0 0 * M 1 1 - M 0 1 * M 1 0) ≤ 1 := by
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hM _ _) (hM _ _)
    have : Valued.v (4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0))) < 1 := by
      rw [map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h4v) (lt_of_le_of_lt (mul_le_of_le_one_right' hd) hp)
    exact absurd h7 (ne_of_gt this)

end UpperTheory.Esk.GoodOperatorConjugation

namespace UpperTheory.Esk

theorem dGood : AMem → DGood := by
  intro _ F _ _ _ c ω χ hχ W n a ha
  exact ⟨GoodOperatorConjugation.good_of hχ ha, fun ⟨w, hw, hc⟩ => GoodOperatorConjugation.reg_of hχ ha hw hc⟩

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DNormalP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

namespace UnipotentNormalization

def up {F : Type} [Field F] (u t : F) (hu : u ≠ 0) : GL (Fin 2) F :=
  ⟨!![u, t; 0, 1], !![u⁻¹, -t * u⁻¹; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring⟩

theorem up_mem (hM : AMem) {F : Type} [Field F] [NumberField F] (u t : F) (hu : u ≠ 0)
    (h1 : IsIntegral ℤ u) (h2 : IsIntegral ℤ u⁻¹) (h3 : IsIntegral ℤ t) : jF F (up u t hu) ∈ K0 F := by
  have hI : ∀ g : GL (Fin 2) F, (∀ i j, IsIntegral ℤ (g.val i j)) → ∀ i j, (jF F g).val i j ∈ Ohat F := by
    intro g hg i j
    change algebraMap F (Af F) (g.val i j) ∈ Ohat F
    exact ((hM F).2.2.2.2.2.1 _).1 (hg i j)
  refine ((hM F).1 _).2 ⟨hI _ ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [up, h1, h3, isIntegral_zero, isIntegral_one]
  · rw [← map_inv]
    refine hI _ ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp [up, h2, isIntegral_zero, isIntegral_one, h3.mul h2]

theorem ht01 {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem ht_inv {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (h2 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ γ x, D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x)
    (h3 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ a : F, a ≠ 0 → ∀ x, D.hf (a • s) x = D.hf s x * ∏ v, D.σ v a ^ 2)
    (b : GL (Fin 2) F) (hb : b 1 0 = 0) (z : X I) (x : Gf) :
    D.Ht ![0, 1] (D.act b z) (D.j b * x) = D.Ht ![0, 1] z x := by
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  have hdb : b.val.det = b 0 0 * b 1 1 := by
    rw [Matrix.det_fin_two]; simp [hb]
  have hdet : b.val.det ≠ 0 := b.det_ne_zero
  have hd : b 1 1 ≠ 0 := fun e => hdet (by rw [hdb, e, mul_zero])
  have hv : (![0, 1] : Fin 2 → F) ᵥ* b.val = b 1 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb]
  have key := h2 _ hs b x
  rw [hv, h3 _ hs _ hd] at key
  have him : ∀ v, ((D.act b z v).1).im = D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im := by
    intro v
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    simp only [Dat.act, coe_smul]
    rw [im_div, det_eq]
    simp [den, Dat.r, hb, Complex.normSq_ofReal]
    field_simp
  rw [ht01, ht01]
  simp_rw [him]
  have hpd : ∏ v, |D.σ v b.val.det| ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => abs_ne_zero.2 ((map_ne_zero _).2 hdet)
  apply mul_right_cancel₀ hpd
  have e : (∏ v, |D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im|) * ∏ v, D.σ v (b 1 1) ^ 2 =
      (∏ v, |(z v).1.im|) * ∏ v, |D.σ v b.val.det| := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    rw [hdb, map_mul, abs_mul, abs_mul, abs_div, ← sq_abs (D.σ v (b 1 1))]
    have : |D.σ v (b 1 1)| ≠ 0 := abs_ne_zero.2 hσ
    field_simp
  rw [mul_assoc, key]
  linear_combination D.hf ![0, 1] x * e

theorem act_up {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ) (χ : Hc c →* ℂˣ)
    (u t : F) (hu : u ≠ 0) (z : X (InfinitePlace F)) (v : InfinitePlace F) :
    (((mkDat c χ).act (up u t hu) z) v).1 = (sg v u : ℂ) * (z v).1 + (sg v t : ℂ) := by
  simp [Dat.act, coe_smul, num, den, Dat.r, up, mkDat]

theorem low {ι : Type} [Fintype ι] (y : ι → ℝ) {C c₀ M : ℝ} (hC : 0 < C) (hM : 0 < M)
    (hy : ∀ v v', |y v| ≤ C * |y v'|) (h : c₀ ≤ (∏ v, |y v|) * M) (v : ι) : min 1 (c₀ / M) / C ≤ |y v| := by
  rw [div_le_iff₀ hC, mul_comm]
  have ha : 0 ≤ C * |y v| := by positivity
  rcases le_or_gt 1 (C * |y v|) with h1 | h1
  · exact (min_le_left _ _).trans h1
  · have : Nonempty ι := ⟨v⟩
    have hp : ∏ v', |y v'| ≤ (C * |y v|) ^ Fintype.card ι := by
      rw [← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun v' _ => hy v' v
    have hpow := pow_le_of_le_one ha h1.le (Fintype.card_ne_zero (α := ι))
    have hcm : c₀ / M ≤ C * |y v| := by
      rw [div_le_iff₀ hM]
      exact h.trans (mul_le_mul_of_nonneg_right (hp.trans hpow) hM.le)
    exact (min_le_right _ _).trans hcm

end UnipotentNormalization

open UnipotentNormalization in
theorem dNormal : AMem → ABnfH → AOrb → AUnit → ATrans → DHt → DMul → DNormal := by
  intro hM hB hO hU hT hH hMu F _ _ _ c hc χ c₀ hc₀
  classical
  obtain ⟨S0, hS0⟩ := hB F c hc
  choose S' hS' using fun x1 : GF F => hO F c hc x1
  obtain ⟨CU, hCU, hU'⟩ := hU F
  obtain ⟨CT, hCT, hT'⟩ := hT F
  obtain ⟨-, h2, h3⟩ := hH F c hc χ
  obtain ⟨hm, -⟩ := hMu F c hc χ
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  set S := S0.biUnion S' with hSdef
  set M : ℝ := 1 + ∑ x' ∈ S, |(mkDat c χ).hf ![0, 1] x'| with hMdef
  have hM0 : 0 < M := by positivity
  have hMS : ∀ x' ∈ S, (mkDat c χ).hf ![0, 1] x' ≤ M := fun x' hx' =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun x' => |(mkDat c χ).hf ![0, 1] x'|)
      (fun _ _ => abs_nonneg _) hx').trans (le_add_of_nonneg_left zero_le_one))
  refine ⟨S, max CU CT, min 1 (c₀ / M) / CU, by positivity, fun z x hz => ?_⟩
  obtain ⟨b1, hb1, x1, hx1, h1, hh1, e1⟩ := hS0 x
  obtain ⟨u, hu0, hui, hui', hu⟩ := hU' (fun v => (((mkDat c χ).act b1 z) v).1.im) (fun v => (((mkDat c χ).act b1 z) v).2)
  obtain ⟨t, hti, ht⟩ := hT' (fun v => sg v u * (((mkDat c χ).act b1 z) v).1.re)
  obtain ⟨x', hx', h2', hh2, e2⟩ := hS' x1 _ (up_mem hM u t hu0 hui hui' hti)
  have hb : (up u t hu0 * b1) 1 0 = 0 := by
    simp [up, Matrix.mul_apply, Fin.sum_univ_two, hb1]
  have hact : (mkDat c χ).act (up u t hu0 * b1) z = (mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z) := by
    funext v; simp only [Dat.act, map_mul, mul_smul]
  have hj : (mkDat c χ).j (up u t hu0 * b1) * x = x' * (h2' * h1) := by
    change jF F (up u t hu0 * b1) * x = _
    rw [map_mul, mul_assoc, e1, ← mul_assoc, e2, mul_assoc]
  have hH' : h2' * h1 ∈ (mkDat c χ).H := Subgroup.mem_sup_left (mul_mem hh2 hh1)
  have hx'S : x' ∈ S := Finset.mem_biUnion.2 ⟨x1, hx1, hx'⟩
  refine ⟨up u t hu0 * b1, hb, ⟨x', hx'S, h2' * h1, hH', hj⟩, ?_⟩
  have e := ht_inv (mkDat c χ) h2 h3 _ hb z x
  rw [← e, hj, hact, ht01, hm _ hs _ _ hH'] at hz
  rw [hact]
  have hre : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.re =
      sg v u * (((mkDat c χ).act b1 z) v).1.re + sg v t := by
    intro v; rw [act_up]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im =
      sg v u * (((mkDat c χ).act b1 z) v).1.im := by
    intro v; rw [act_up]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hy : ∀ v v', |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im| ≤
      CU * |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v').1.im| := by
    intro v v'; rw [him, him]; exact hu v v'
  have hprod : c₀ ≤ (∏ v, |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im|) * M :=
    hz.trans (mul_le_mul_of_nonneg_left (hMS x' hx'S) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
  intro v
  refine ⟨?_, low _ hCU hM0 hy hprod v, fun v' => ?_⟩
  · rw [hre]; exact (ht v).trans (le_max_right _ _)
  · exact (hy v v').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AMinkP
open NumberField MeasureTheory Module Finset

namespace UpperTheory.Esk.MinkowskiBoundLemmas

open scoped Classical

abbrev Ix (F : Type) [Field F] [NumberField F] := Free.ChooseBasisIndex ℤ (𝓞 F)

abbrev Rp (F : Type) [Field F] [NumberField F] := {w : InfinitePlace F // w.IsReal}

instance instHaarRp (F : Type) [Field F] [NumberField F] :
    Measure.IsAddHaarMeasure ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ))) :=
  Measure.prod.instIsAddHaarMeasure _ _

noncomputable def B (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (Ix F → ℝ) ≃ₗ[ℝ] (Rp F → ℝ) :=
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal _) w.2⟩
  (mixedEmbedding.latticeBasis F).equivFun.symm.trans LinearEquiv.prodUnique

lemma B_apply (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (m : Ix F → ℝ) (w : Rp F) :
    B F m w = ∑ i, m i * InfinitePlace.embedding_of_isReal w.2 (integralBasis F i) := by
  simp [B, Basis.equivFun_symm_apply, mixedEmbedding.mixedEmbedding_apply_isReal]

noncomputable def Phi (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (Ix F ⊕ Ix F → ℝ) ≃ₗ[ℝ] (Rp F → ℝ) × (Rp F → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans ((B F).prodCongr (B F))

lemma Phi_apply (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : Ix F ⊕ Ix F → ℝ) :
    Phi F y = (B F (fun i => y (Sum.inl i)), B F (fun i => y (Sum.inr i))) := rfl

noncomputable def cst (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : NNReal :=
  Measure.addHaarScalarFactor
    (Measure.map (Phi F).toContinuousLinearEquiv (volume : Measure (Ix F ⊕ Ix F → ℝ)))
    ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ)))

lemma map_eq (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Measure.map (Phi F).toContinuousLinearEquiv (volume : Measure (Ix F ⊕ Ix F → ℝ))
      = cst F • ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ))) := by
  unfold cst; exact Measure.isAddLeftInvariant_eq_smul _ _

lemma cst_pos (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : 0 < cst F := by
  unfold cst; exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

lemma vol_S {κ : Type} [Fintype κ] (α β x : κ → ℝ) (hβ : ∀ w, 0 ≤ β w) :
    ((volume : Measure (κ → ℝ)).prod (volume : Measure (κ → ℝ)))
      {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w}
      = ∏ w, ENNReal.ofReal (4 * (α w * β w)) := by
  have hS : MeasurableSet
      {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w} := by
    have : IsClosed
        {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w} := by
      simp only [Set.ofPred_forall, Set.ofPred_and]
      exact isClosed_iInter fun w =>
        (isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const)
    exact this.measurableSet
  rw [Measure.prod_apply hS]
  have hslice : (fun p1 : κ → ℝ => volume (Prod.mk p1 ⁻¹'
      {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w}))
      = (Set.Icc (-α) α).indicator (fun _ => ∏ w, ENNReal.ofReal (2 * β w)) := by
    funext p1
    by_cases h : p1 ∈ Set.Icc (-α) α
    · rw [Set.indicator_of_mem h]
      rw [Set.mem_Icc, Pi.le_def, Pi.le_def] at h
      have hA : ∀ w, |p1 w| ≤ α w := fun w => abs_le.2 ⟨by simpa using h.1 w, h.2 w⟩
      have e : Prod.mk p1 ⁻¹'
          {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w}
          = Set.Icc (fun w => -β w - p1 w * x w) (fun w => β w - p1 w * x w) := by
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
        constructor
        · intro hq
          refine ⟨fun w => ?_, fun w => ?_⟩
          · have := abs_le.1 (hq w).2; linarith [this.1]
          · have := abs_le.1 (hq w).2; linarith [this.2]
        · rintro ⟨h1, h2⟩ w
          exact ⟨hA w, abs_le.2 ⟨by linarith [h1 w], by linarith [h2 w]⟩⟩
      rw [e, Real.volume_Icc_pi]
      congr 1; funext w; congr 1; ring
    · rw [Set.indicator_of_notMem h]
      have e : Prod.mk p1 ⁻¹'
          {p : (κ → ℝ) × (κ → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * x w + p.2 w| ≤ β w} = ∅ := by
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hq
        apply h
        rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
        exact ⟨fun w => by simpa using (abs_le.1 (hq w).1).1, fun w => (abs_le.1 (hq w).1).2⟩
      rw [e, measure_empty]
  rw [hslice, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc_pi,
    ← Finset.prod_mul_distrib]
  congr 1; funext w
  rw [← ENNReal.ofReal_mul (by linarith [hβ w])]
  congr 1; simp only [Pi.neg_apply]; ring

lemma sum_integral (F : Type) [Field F] [NumberField F] (u : Ix F → ℤ) :
    IsIntegral ℤ (∑ i, (u i : F) * integralBasis F i) := by
  have : (∑ i, (u i : F) * integralBasis F i) ∈ integralClosure ℤ F :=
    Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _)
      (by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
  exact this

lemma emb_sum (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (u : Ix F → ℤ) (w : Rp F) :
    InfinitePlace.embedding_of_isReal w.2 (∑ i, (u i : F) * integralBasis F i)
      = B F (fun i => (u i : ℝ)) w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [B_apply]; simp [map_sum, map_mul, map_intCast]

theorem core (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : ∃ C : ℝ, 0 < C ∧
    ∀ z : InfinitePlace F → ℂ, (∀ v, (z v).im ≠ 0) →
    ∃ s : Fin 2 → F, s ≠ 0 ∧ (∀ i, IsIntegral ℤ (s i)) ∧ ∀ v,
      ‖((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (s 0) : ℝ) : ℂ) * z v +
        ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (s 1) : ℝ) : ℂ)‖ ^ 2
        ≤ C * |(z v).im| := by
  classical
  set c : ℝ := (cst F : ℝ) with hc_def
  have hc : 0 < c := cst_pos F
  set t : ℝ := 1 + 1 / c with ht_def
  have ht1 : 1 ≤ t := by have := one_div_pos.2 hc; linarith
  refine ⟨2 * t ^ 2, by positivity, fun z hz => ?_⟩
  set d := Fintype.card (Rp F) with hd_def
  have hne : Nonempty (Rp F) :=
    ⟨⟨Classical.arbitrary (InfinitePlace F), IsTotallyReal.isReal _⟩⟩
  have hd : d ≠ 0 := Fintype.card_ne_zero
  have hcard : Fintype.card (Ix F) = d := by
    have := (B F).finrank_eq
    rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at this
  let r : Rp F → ℝ := fun w => Real.sqrt |(z w.1).im|
  have hr : ∀ w, 0 < r w := fun w => Real.sqrt_pos.2 (abs_pos.2 (hz w.1))
  have hr2 : ∀ w, r w ^ 2 = |(z w.1).im| := fun w => Real.sq_sqrt (abs_nonneg _)
  let α : Rp F → ℝ := fun w => t / r w
  let β : Rp F → ℝ := fun w => t * r w
  let xx : Rp F → ℝ := fun w => (z w.1).re
  let S := {p : (Rp F → ℝ) × (Rp F → ℝ) | ∀ w, |p.1 w| ≤ α w ∧ |p.1 w * xx w + p.2 w| ≤ β w}
  have hSm : MeasurableSet S := by
    have : IsClosed S := by
      simp only [S, Set.ofPred_forall, Set.ofPred_and]
      exact isClosed_iInter fun w =>
        (isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const)
    exact this.measurableSet
  have hαβ : ∀ w, α w * β w = t ^ 2 := fun w => by
    simp only [α, β]; field_simp [(hr w).ne']
  have hvS : ((volume : Measure (Rp F → ℝ)).prod (volume : Measure (Rp F → ℝ))) S = ENNReal.ofReal ((4 * t ^ 2) ^ d) := by
    rw [vol_S α β xx (fun w => by positivity)]
    simp only [hαβ, Finset.prod_const, Finset.card_univ]
    rw [ENNReal.ofReal_pow (by positivity)]
  have hvs : volume ((Phi F) ⁻¹' S) = ENNReal.ofReal (c * (4 * t ^ 2) ^ d) := by
    have e1 : volume ((Phi F) ⁻¹' S) =
        Measure.map (Phi F).toContinuousLinearEquiv (volume : Measure (Ix F ⊕ Ix F → ℝ)) S := by
      rw [Measure.map_apply (Phi F).toContinuousLinearEquiv.continuous.measurable hSm]; rfl
    rw [e1, map_eq, Measure.smul_apply, hvS, ENNReal.smul_def, smul_eq_mul,
      ENNReal.ofReal_mul hc.le, hc_def, ENNReal.ofReal_coe_nnreal]
  have hsymm : ∀ y ∈ (Phi F) ⁻¹' S, -y ∈ (Phi F) ⁻¹' S := by
    intro y hy
    simp only [S, Set.mem_preimage, Set.mem_ofPred_eq, map_neg] at hy ⊢
    intro w
    obtain ⟨h1, h2⟩ := hy w
    refine ⟨by simpa using h1, ?_⟩
    have e : (-(Phi F y)).1 w * xx w + (-(Phi F y)).2 w = -((Phi F y).1 w * xx w + (Phi F y).2 w) := by
      simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]; ring
    rw [e, abs_neg]; exact h2
  have hconvS : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    simp only [S, Set.mem_ofPred_eq] at hp hq ⊢
    intro w
    obtain ⟨h1, h2⟩ := hp w
    obtain ⟨h3, h4⟩ := hq w
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    constructor
    · calc |a * p.1 w + b * q.1 w| ≤ |a * p.1 w| + |b * q.1 w| := abs_add_le _ _
        _ = a * |p.1 w| + b * |q.1 w| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * α w + b * α w := by gcongr
        _ = α w := by rw [← add_mul, hab, one_mul]
    · calc |(a * p.1 w + b * q.1 w) * xx w + (a * p.2 w + b * q.2 w)|
          = |a * (p.1 w * xx w + p.2 w) + b * (q.1 w * xx w + q.2 w)| := by congr 1; ring
        _ ≤ |a * (p.1 w * xx w + p.2 w)| + |b * (q.1 w * xx w + q.2 w)| := abs_add_le _ _
        _ = a * |p.1 w * xx w + p.2 w| + b * |q.1 w * xx w + q.2 w| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * β w + b * β w := by gcongr
        _ = β w := by rw [← add_mul, hab, one_mul]
  have hconv : Convex ℝ ((Phi F) ⁻¹' S) := hconvS.linear_preimage (Phi F).toLinearMap
  have hF0 : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Ix F ⊕ Ix F))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp [Real.volume_Ico]
  have key : (2 : ℝ) ^ (d + d) < c * (4 * t ^ 2) ^ d := by
    have h4 : (2 : ℝ) ^ (d + d) = 4 ^ d := by rw [pow_add, ← mul_pow]; norm_num
    have ht2 : t ≤ (t ^ 2) ^ d :=
      le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) hd)
    have hct : c * t = c + 1 := by rw [ht_def]; field_simp
    have h4p : (0 : ℝ) < 4 ^ d := by positivity
    rw [h4, mul_pow]
    calc (4 : ℝ) ^ d < 4 ^ d * (c * t) := by rw [hct]; nlinarith
      _ ≤ 4 ^ d * (c * (t ^ 2) ^ d) := by gcongr
      _ = c * (4 ^ d * (t ^ 2) ^ d) := by ring
  have hvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Ix F ⊕ Ix F))) *
      2 ^ finrank ℝ (Ix F ⊕ Ix F → ℝ) < volume ((Phi F) ⁻¹' S) := by
    rw [hF0, one_mul, hvs, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, hcard]
    rw [show (2 : ENNReal) ^ (d + d) = ENNReal.ofReal ((2 : ℝ) ^ (d + d)) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 key
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Ix F ⊕ Ix F)))).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Ix F ⊕ Ix F)))))
  obtain ⟨⟨y, hyL⟩, hy0, hys⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (μ := volume) (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Ix F ⊕ Ix F)) volume)
    hsymm hconv hvol
  have hint : ∀ j, ∃ n : ℤ, y j = n := by
    intro j
    obtain ⟨n, hn⟩ := (Basis.mem_span_iff_repr_mem (R := ℤ) (Pi.basisFun ℝ (Ix F ⊕ Ix F)) y).1 hyL j
    exact ⟨n, by simpa using hn.symm⟩
  choose n hn using hint
  set a : F := ∑ i, (n (Sum.inl i) : F) * integralBasis F i with ha_def
  set b : F := ∑ i, (n (Sum.inr i) : F) * integralBasis F i with hb_def
  have hPhi : Phi F y = (B F (fun i => (n (Sum.inl i) : ℝ)), B F (fun i => (n (Sum.inr i) : ℝ))) := by
    rw [Phi_apply]; congr 1 <;> congr 1 <;> funext i <;> exact hn _
  have hys' : Phi F y ∈ S := hys
  rw [hPhi] at hys'
  simp only [S, Set.mem_ofPred_eq] at hys'
  refine ⟨![a, b], ?_, ?_, ?_⟩
  · intro h0
    have ha0 : a = 0 := by simpa using congrFun h0 0
    have hb0 : b = 0 := by simpa using congrFun h0 1
    have hm : (fun i => (n (Sum.inl i) : ℝ)) = 0 := by
      apply (B F).injective
      rw [map_zero]; funext w
      rw [← emb_sum F (fun i => n (Sum.inl i)) w, ← ha_def, ha0, map_zero]; rfl
    have hm' : (fun i => (n (Sum.inr i) : ℝ)) = 0 := by
      apply (B F).injective
      rw [map_zero]; funext w
      rw [← emb_sum F (fun i => n (Sum.inr i)) w, ← hb_def, hb0, map_zero]; rfl
    apply hy0
    apply Subtype.ext
    funext j
    cases j with
    | inl i => show y (Sum.inl i) = 0; rw [hn]; simpa using congrFun hm i
    | inr i => show y (Sum.inr i) = 0; rw [hn]; simpa using congrFun hm' i
  · exact Fin.forall_fin_two.2 ⟨sum_integral F _, sum_integral F _⟩
  · intro v
    obtain ⟨h1, h2⟩ := hys' ⟨v, IsTotallyReal.isReal v⟩
    rw [← emb_sum F (fun i => n (Sum.inl i))] at h1
    rw [← emb_sum F (fun i => n (Sum.inl i)), ← emb_sum F (fun i => n (Sum.inr i))] at h2
    have h1' : |InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a|
        ≤ t / r ⟨v, IsTotallyReal.isReal v⟩ := h1
    have h2' : |InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a * (z v).re +
        InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) b|
        ≤ t * r ⟨v, IsTotallyReal.isReal v⟩ := h2
    have hrv : 0 < r ⟨v, IsTotallyReal.isReal v⟩ := hr _
    have hr2v : r ⟨v, IsTotallyReal.isReal v⟩ ^ 2 = |(z v).im| := hr2 _
    show ‖((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a : ℝ) : ℂ) * z v +
        ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) b : ℝ) : ℂ)‖ ^ 2
        ≤ 2 * t ^ 2 * |(z v).im|
    clear_value r α β xx S a b c t
    generalize InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) a = A at h1' h2' ⊢
    generalize InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) b = Bb at h2' ⊢
    generalize r ⟨v, IsTotallyReal.isReal v⟩ = R at hrv hr2v h1' h2'
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero, mul_zero]
    have e1 : (A * (z v).re + Bb) ^ 2 ≤ (t * R) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2' 2
    have e2 : A ^ 2 ≤ (t / R) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1' 2
    have hy2 : (z v).im ^ 2 = R ^ 4 := by
      rw [← sq_abs, ← hr2v]; ring
    have e3 : A ^ 2 * (z v).im ^ 2 ≤ t ^ 2 * R ^ 2 := by
      calc A ^ 2 * (z v).im ^ 2 ≤ (t / R) ^ 2 * (z v).im ^ 2 :=
            mul_le_mul_of_nonneg_right e2 (sq_nonneg _)
        _ = t ^ 2 * R ^ 2 := by
          rw [hy2, div_pow, div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring
    have e4 : (t * R) ^ 2 = t ^ 2 * R ^ 2 := by ring
    rw [← hr2v]
    nlinarith [e1, e3, e4]

end UpperTheory.Esk.MinkowskiBoundLemmas

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aMink : AMink := fun F _ _ _ => MinkowskiBoundLemmas.core F

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AOrb
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aOrb : AMem → AOrb := by
  intro _ F _ _ c hc x
  have hT := UpperTheory.V.Sd.Wc.kcTop F
  have hK0 : IsCompact (K0 F : Set (GF F)) := ((hT.1 (fun _ => 0) (by simp)).2)
  have hKo : IsOpen (Kc c : Set (GF F)) := (hT.1 c hc).1
  have hs : IsCompact ((fun k : GF F => k * x) '' (K0 F : Set (GF F))) :=
    hK0.image (continuous_id.mul continuous_const)
  obtain ⟨t, -, ht⟩ := hs.elim_nhds_subcover (fun g => (fun y : GF F => g⁻¹ * y) ⁻¹' (Kc c : Set (GF F)))
    (fun g _ => (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [(Kc c).one_mem]))
  refine ⟨t, fun k hk => ?_⟩
  have hm := ht ⟨k, hk, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at hm
  obtain ⟨g, hg, hgk⟩ := hm
  exact ⟨g, hg, g⁻¹ * (k * x), hgk, by rw [mul_inv_cancel_left]⟩

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ABnfHP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aBnfH : UpperTheory.Esk.ABnf → UpperTheory.Esk.AOrb → UpperTheory.Esk.ABnfH := by
  classical
  intro hB hO F _ _ c hc
  obtain ⟨S, hS⟩ := hB F
  obtain ⟨T, hT⟩ := hO F c hc 1
  refine ⟨Finset.image₂ (· * ·) S T, fun x => ?_⟩
  obtain ⟨b, hb, x', hx', k, hk, hx⟩ := hS x
  obtain ⟨y, hy, h, hh, hkh⟩ := hT k hk
  refine ⟨b, hb, x' * y, Finset.mem_image₂_of_mem hx' hy, h, hh, ?_⟩
  rw [hx, mul_assoc, ← hkh, mul_one]

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.VOne
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.ClassNumberLemmas

theorem v_one {F : Type} [Field F] [NumberField F] (e : (Af F)ˣ) (h1 : (e : Af F) ∈ PIW.ClassFinD.Ohat F)
    (h2 : ((e⁻¹ : (Af F)ˣ) : Af F) ∈ PIW.ClassFinD.Ohat F) (w : Pl F) : Valued.v (pLoc F w (e : Af F)) = 1 := by
  have a1 : Valued.v (pLoc F w (e : Af F)) ≤ 1 := by
    have h := h1 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have a2 : Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := by
    have h := h2 w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hm : Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : _) = Valued.v (pLoc F w (e : Af F)) * Valued.v (pLoc F w ((e⁻¹ : (Af F)ˣ) : Af F)) := hm.symm
    _ ≤ Valued.v (pLoc F w (e : Af F)) * 1 := by gcongr
    _ = Valued.v (pLoc F w (e : Af F)) := mul_one _

end UpperTheory.Esk.ClassNumberLemmas

namespace UpperTheory.Esk

theorem aCls : ACls := by
  intro F _ _
  obtain ⟨C, hC⟩ := PIW.ClassFinD.idele_class_finite F
  refine ⟨C, fun z => ?_⟩
  obtain ⟨f, c, hc, e, he1, he2, hz⟩ := hC z
  exact ⟨f, e, c, hc, ClassNumberLemmas.v_one e he1 he2, hz⟩

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DetR
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

namespace LatticeCountingLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def box (r : ℝ) : Set F := {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ r}

theorem place_eq (v : InfinitePlace F) (t : F) : v t = |sg v t| := by
  rw [← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]

theorem det_r {c : Pl F → ℕ} (χ : Hc c →* ℂˣ) (v : InfinitePlace F) (g : GL (Fin 2) F) :
    ((mkDat c χ).r v g).val.det = sg v g.val.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  rfl

theorem bnd (v : InfinitePlace F) (N : ℕ) (x : F) {b : ℝ} (h : |sg v x| ≤ b) : v ((N : F) * x) ≤ N * b := by
  rw [place_eq, map_mul, map_natCast, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

end LatticeCountingLemmas

open LatticeCountingLemmas in
theorem dCnt : DScale → DBox → DEntry → DCnt := by
  intro hS hB hE F _ _ _ cc hcc χ ω δ C c hδ hc
  classical
  obtain ⟨N, C0, hN, hC0, hg⟩ := hS F cc hcc χ ω
  obtain ⟨CB, hCB⟩ := hB F
  obtain ⟨B, hBd⟩ := hE δ (max C C0) c hδ hc
  choose gg hgg using hg
  have ha : 0 ≤ (N : ℝ) * max B 0 := by positivity
  have hCB0 : 0 ≤ CB := by
    have h0 : ((box (F := F) 0).ncard : ℝ) ≤ CB * (1 + 0 ^ Fintype.card (InfinitePlace F)) := (hCB 0 le_rfl).2
    have h1 : (0 : ℝ) < 1 + 0 ^ Fintype.card (InfinitePlace F) := by positivity
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg h1
    linarith [Nat.cast_nonneg (α := ℝ) (box (F := F) 0).ncard]
  refine ⟨(CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F))) ^ 3 * CB *
    (1 + ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F)), fun z hz => ?_⟩
  obtain ⟨v0⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hz v0).1
  have hR : 0 ≤ (N : ℝ) * max B 0 * C * |(z v0).1.im| := by positivity
  let f : PG F → F × F × F × F := fun γ => if h : γ • ω = ω then
    ((N : F) * gg γ h 1 0, (N : F) * gg γ h 0 0, (N : F) * gg γ h 1 1, (N : F) * gg γ h 0 1) else 0
  have hinj : Set.InjOn f {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)} := by
    intro γ1 h1 γ2 h2 he
    simp only [f, dif_pos h1.1, dif_pos h2.1, Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3, e4⟩ := he
    have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
    have hgeq : gg γ1 h1.1 = gg γ2 h2.1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact mul_left_cancel₀ hN' e2
      · exact mul_left_cancel₀ hN' e4
      · exact mul_left_cancel₀ hN' e1
      · exact mul_left_cancel₀ hN' e3
    calc γ1 = (gg γ1 h1.1 : PG F) := (hgg γ1 h1.1).1.symm
      _ = (gg γ2 h2.1 : PG F) := by rw [hgeq]
      _ = γ2 := (hgg γ2 h2.1).1
  have hmaps : f '' {γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)} ⊆
      box ((N : ℝ) * max B 0) ×ˢ box ((N : ℝ) * max B 0) ×ˢ box ((N : ℝ) * max B 0) ×ˢ
        box ((N : ℝ) * max B 0 * C * |(z v0).1.im|) := by
    rintro _ ⟨γ, ⟨hgω, hnear⟩, rfl⟩
    obtain ⟨hgγ, hint, hdet⟩ := hgg γ hgω
    simp only [f, dif_pos hgω]
    generalize gg γ hgω = g at hgγ hint hdet ⊢
    have hE' : ∀ v, |(mkDat cc χ).r v g 1 0| ≤ B ∧ |(mkDat cc χ).r v g 0 0| ≤ B ∧ |(mkDat cc χ).r v g 1 1| ≤ B ∧
        |(mkDat cc χ).r v g 0 1| ≤ B * |(z v).1.im| := by
      intro v
      have hv := hnear v
      rw [← hgγ] at hv
      exact hBd ((mkDat cc χ).r v g) (z v) ((hz v).1.trans (le_max_left _ _)) (hz v).2.1
        (by rw [det_r]; exact (hdet v).2.trans (le_max_right _ _)) hv
    have hB3 : ∀ v i j, |(mkDat cc χ).r v g i j| ≤ B → v ((N : F) * g i j) ≤ (N : ℝ) * max B 0 := fun v i j h =>
      bnd v N (g i j) (h.trans (le_max_left _ _))
    have hB4 : ∀ v : InfinitePlace F, v ((N : F) * g 0 1) ≤ (N : ℝ) * max B 0 * C * |(z v0).1.im| := fun v => by
      have h1 : |(mkDat cc χ).r v g 0 1| ≤ max B 0 * (C * |(z v0).1.im|) :=
        (hE' v).2.2.2.trans (mul_le_mul (le_max_left _ _) ((hz v).2.2 v0) (abs_nonneg _) (le_max_right _ _))
      refine (bnd v N (g 0 1) h1).trans (le_of_eq ?_)
      ring
    exact ⟨⟨hint 1 0, fun v => hB3 v 1 0 (hE' v).1⟩, ⟨hint 0 0, fun v => hB3 v 0 0 (hE' v).2.1⟩,
      ⟨hint 1 1, fun v => hB3 v 1 1 (hE' v).2.2.1⟩, ⟨hint 0 1, hB4⟩⟩
  have hfin := (hCB _ ha).1.prod ((hCB _ ha).1.prod ((hCB _ ha).1.prod (hCB _ hR).1))
  refine ⟨Set.Finite.of_finite_image (hfin.subset hmaps) hinj, ?_⟩
  have hle := Set.ncard_le_ncard hmaps hfin
  rw [hinj.ncard_image, Set.ncard_prod, Set.ncard_prod, Set.ncard_prod] at hle
  have h1 : ((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) ≤ CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F)) :=
    (hCB _ ha).2
  have h4 : ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ) ≤
      CB * (1 + ((N : ℝ) * max B 0 * C * |(z v0).1.im|) ^ Fintype.card (InfinitePlace F)) := (hCB _ hR).2
  have hP : 0 ≤ ∏ v, |(z v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hprod : |(z v0).1.im| ^ Fintype.card (InfinitePlace F) ≤ C ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im| := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ => |(z v0).1.im|) (g := fun v => C * |(z v).1.im|)
      (fun _ _ => abs_nonneg _) (fun v _ => (hz v0).2.2 v)
    rwa [Finset.prod_const, Finset.card_univ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at this
  have hRd : ((N : ℝ) * max B 0 * C * |(z v0).1.im|) ^ Fintype.card (InfinitePlace F) ≤
      ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im| := by
    calc _ = ((N : ℝ) * max B 0 * C) ^ Fintype.card (InfinitePlace F) * |(z v0).1.im| ^ Fintype.card (InfinitePlace F) :=
          mul_pow _ _ _
      _ ≤ ((N : ℝ) * max B 0 * C) ^ Fintype.card (InfinitePlace F) * (C ^ Fintype.card (InfinitePlace F) * ∏ v, |(z v).1.im|) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hX : 0 ≤ CB * (1 + ((N : ℝ) * max B 0) ^ Fintype.card (InfinitePlace F)) := mul_nonneg hCB0 (by positivity)
  have hM : 0 ≤ ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F) := by positivity
  have h4' : ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ) ≤
      CB * ((1 + ((N : ℝ) * max B 0 * C * C) ^ Fintype.card (InfinitePlace F)) * (1 + ∏ v, |(z v).1.im|)) :=
    h4.trans (mul_le_mul_of_nonneg_left (by nlinarith) hCB0)
  have hle' : (({γ : PG F | γ • ω = ω ∧ Near δ z (γ • z)}.ncard : ℕ) : ℝ) ≤
      ((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) * (((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) *
        (((box (F := F) ((N : ℝ) * max B 0)).ncard : ℝ) * ((box (F := F) ((N : ℝ) * max B 0 * C * |(z v0).1.im|)).ncard : ℝ))) := by
    exact_mod_cast hle
  refine hle'.trans ((mul_le_mul h1 (mul_le_mul h1 (mul_le_mul h1 h4' (Nat.cast_nonneg _) hX) (by positivity) hX)
    (by positivity) hX).trans_eq (by ring))
end UpperTheory.Esk
end
end

namespace UpperTheory.Esk

theorem dAx : DAx :=
  have m := aMem
  have iw := aIw m
  have row := aRow m iw
  have orb := aOrb m
  have bnf := aBnfH (aBnf m iw aCls (aAdd m)) orb
  have ht := dHt row
  have mul := dMul m iw aMono row
  dAx_of (dCount m bnf orb) ht mul (dProd m aMono row) (dMink m aMono row bnf aMink ht mul)
    (dNormal m bnf orb aUnit aTrans ht mul) (dCnt (dScale m aCls aUnit) dBox dEntry)

theorem dTwo' : DTwo := dTwo aMem

theorem dGood' : DGood := dGood aMem

end UpperTheory.Esk
