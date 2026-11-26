module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SplitDescentOfImagQuadDescent
public import GroundTheory.IdeleRoots.ClassicalIdeles.ExistsPosBoundsOfIsCompact
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ActRat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

private theorem barW_coe (z : (A E)ˣ) : ((Units.map (D.bar : A E →* A E) z : (A E)ˣ) : A E) = D.bar z := rfl

private theorem bar_mul_barInv (z : (A E)ˣ) :
    D.bar (z : A E) * (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = 1 := by
  rw [← barW_coe, Units.mul_inv]

private theorem sZ_val (z : (A E)ˣ) :
    (sZ D z).val = !![(z : A E), 0; 0, (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E)] := by
  simp only [sZ, Units.val_mul, aE_val, dM_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem em_val (h : GL (Fin 2) (A ℚ)) (i j : Fin 2) : (em E h).val i j = am E (h.val i j) := rfl

private theorem am_norm_mul (z : (A E)ˣ) :
    (z : A E) * D.bar z * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
  rw [← D.am_ideleNorm z, ← map_mul, Units.mul_inv, map_one]

private theorem barInv_eq (z : (A E)ˣ) :
    (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) * z := by
  have h2 := am_norm_mul D z
  have h3 := bar_mul_barInv D z
  linear_combination ((z : A E) * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ)) * h3 - (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) * h2

private theorem sZ_mul (z z' : (A E)ˣ) : sZ D (z * z') = sZ D z * sZ D z' := by
  simp only [sZ, map_mul, mul_inv, aE_mul, dM_mul]
  rw [mul_assoc, mul_assoc, ← mul_assoc (dM _) (aE z'), dM_mul_aE, ← mul_assoc (aE z')]

private theorem sZ_cont : Continuous (sZ D) := by
  have h : Continuous (Units.map (D.bar : A E →* A E)) := Continuous.units_map _ D.continuous_bar
  exact continuous_aE.mul (continuous_dM.comp h.inv)

private theorem nu_sZ (z : (A E)ˣ) : nu ℚ (sZ D z) = 1 := by
  have h : ideleNorm ℚ E (Units.map (D.bar : A E →* A E) z) = ideleNorm ℚ E z := D.ideleNorm_barU z
  rw [sZ, nu_mul, nu_aE, nu_dM, map_inv, h, mul_inv_cancel]

private theorem hermitian_standardVector : D.herm (rp X0) = !![0, rt D.θ; -rt D.θ, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE_def, X0, rp]

private theorem action_fixes_standardVector {h : GL (Fin 2) (A E)}
    (h1 : h.val * !![0, rt D.θ; -rt D.θ, 0] * D.star2 h.val = !![0, rt D.θ; -rt D.θ, 0]) :
    D.act h (rp X0) = rp X0 := by
  apply D.herm_injective
  rw [D.herm_act, hermitian_standardVector, h1]

private theorem act_sZ (z : (A E)ˣ) : D.act (sZ D z) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have h3 : (z : A E) * ((z⁻¹ : (A E)ˣ) : A E) = 1 := Units.mul_inv z
  have h4 : D.bar ((z⁻¹ : (A E)ˣ) : A E) * D.bar (z : A E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [sZ_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply]
  · linear_combination (rt D.θ) * h3
  · linear_combination (rt D.θ) * h4

private theorem act_em (g : G1 ℚ) : D.act (em E (gl g)) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have hd : am E (g 0 0) * am E (g 1 1) - am E (g 0 1) * am E (g 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, specialLinear_det_entries, map_one]
  have e : (em E (gl g)).val = !![am E (g 0 0), am E (g 0 1); am E (g 1 0), am E (g 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [e]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, D.bar_am]
  · ring
  · linear_combination (rt D.θ) * hd
  · linear_combination (-rt D.θ) * hd
  · ring

private theorem sZ_diag (e : Eˣ) : ∃ γ, sZ D (IdeleGroup.diagonal E e) = ratGL E 2 γ := by
  obtain ⟨γ₁, h₁⟩ := exists_ratGL_aE (F := E) e
  obtain ⟨γ₂, h₂⟩ := exists_ratGL_dM (F := E) (Units.map (D.σ : E →* E) e)⁻¹
  refine ⟨γ₁ * γ₂, ?_⟩
  have h : (Units.map (D.bar : A E →* A E) (IdeleGroup.diagonal E e))⁻¹ =
      IdeleGroup.diagonal E (Units.map (D.σ : E →* E) e)⁻¹ := by
    rw [map_inv]
    congr 1
    apply Units.ext
    rw [barW_coe, coe_diagonal, coe_diagonal, D.bar_rt]
    rfl
  rw [sZ, h, map_mul, h₁, h₂]

private theorem sZ_conj (z : (A E)ˣ) (g : G1 ℚ) :
    sZ D z * em E (gl g) = em E (gl (cD (ideleNorm ℚ E z)⁻¹ g)) * sZ D z := by
  have hn := am_norm_mul D z
  have hb := barInv_eq D z
  have hN := D.am_ideleNorm z
  have hc : ∀ i j, (em E (gl (cD (ideleNorm ℚ E z)⁻¹ g))).val i j = am E ((cD (ideleNorm ℚ E z)⁻¹ g).1 i j) := fun _ _ => rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hc, em_val, gl_val, cD_val]
  fin_cases i <;> fin_cases j <;> simp [inv_inv, map_mul, hN]
  · ring
  · rw [GroundTheory.Global.coe_ideleNorm] at hN
    rw [hN]
    linear_combination (-(am E (g 0 1)) * (z : A E)) * hn
  · ring
  · ring

private theorem sZ_scalar (z : (A E)ˣ) :
    sZ D z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * em E (dM (ideleNorm ℚ E z)⁻¹) := by
  have hb := barInv_eq D z
  apply Units.ext
  rw [Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, em_val, dM_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · ring

private theorem quadraticForm_rational_points (δ : ℚ) (ξ : Fin 4 → ℚ) : q4 δ (rp ξ) = rt (qr δ ξ) := by
  simp [q4, qr, rp, map_sub, map_mul, map_pow]

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws :
    SzLaws := by
  intro E _ _ _ D
  refine ⟨sZ_mul D, sZ_cont D, nu_sZ D, nu_gl, act_sZ D, act_em D, sZ_diag D, sZ_conj D, sZ_scalar D, ?_, quadraticForm_rational_points D.δ⟩
  intro x hx v
  rw [D.quadForm_act, hx]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private theorem vn (q : A F) : (nU q).val = !![1, q; 0, 1] := rfl

private theorem vm (a : (A F)ˣ) : (mD a).val = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl

private theorem gmul (x y : G1 F) : gl (x * y) = gl x * gl y := map_mul _ _ _

private theorem cont_n : Continuous fun q : A F => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q => inv_eq_of_mul_eq_one_right (Units.ext (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two]))
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

private theorem tri (Y : GL (Fin 2) (A F)) (t₀ t₁ : (A F)ˣ) (h0 : Y.val 0 0 = t₀) (h1 : Y.val 1 1 = t₁) (h : Y.val 1 0 = 0) :
    Y = gl (nU (Y.val 0 1 * ((t₁⁻¹ : (A F)ˣ) : A F))) * diagUnits 2 ![t₀, t₁] := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, h0, h1, h]

private theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

private theorem rat_m (c : Fˣ) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (mD (IdeleGroup.diagonal F c)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] i j) = _
  fin_cases i <;> fin_cases j
  · rfl
  · simp [vm]
  · simp [vm]
  · rfl

private theorem units_cpt {C : Set (GL (Fin 2) (A F))} (hC : IsCompact C) :
    ∃ U : Set (A F)ˣ, IsCompact U ∧ ∀ β ∈ C, β ∈ adelicBorel (K := F) (n := 2) → ∀ i, ∃ u ∈ U, (u : A F) = β.val i i := by
  let Q : Set (A F) := ⋃ i : Fin 2, ((fun β : GL (Fin 2) (A F) => β.val i i) '' C ∪ (fun β : GL (Fin 2) (A F) => (β⁻¹).val i i) '' C)
  have hQ : IsCompact Q := isCompact_iUnion fun i =>
    (hC.image (Units.continuous_val.matrix_elem i i)).union
      (hC.image (Units.continuous_coe_inv.matrix_elem i i))
  refine ⟨Units.embedProduct _ ⁻¹' (Q ×ˢ (MulOpposite.op '' Q)), Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hQ.prod (hQ.image MulOpposite.continuous_op)), fun β hβ hb i => ?_⟩
  have h1 : β.val 1 0 = 0 := hb (by decide : (0 : Fin 2) < 1)
  have h2 : (β⁻¹).val 1 0 = 0 := (adelicBorel.inv_mem hb) (by decide : (0 : Fin 2) < 1)
  have h3 : β.val i i * (β⁻¹).val i i = 1 := by
    have := congrFun (congrFun β.mul_inv i) i
    rw [Matrix.mul_apply, Fin.sum_univ_two] at this
    fin_cases i
    · simpa [-Matrix.coe_units_inv, h2] using this
    · simpa [-Matrix.coe_units_inv, h1] using this
  exact ⟨⟨β.val i i, (β⁻¹).val i i, h3, by rw [mul_comm]; exact h3⟩,
    ⟨Set.mem_iUnion.2 ⟨i, Or.inl ⟨β, hβ, rfl⟩⟩, _, Set.mem_iUnion.2 ⟨i, Or.inr ⟨β, hβ, rfl⟩⟩, rfl⟩, rfl⟩

private theorem siegel {C : Set (GL (Fin 2) (A F))} (hC : IsCompact C) :
    ∃ ω : Set (GL (Fin 2) (A F)), IsCompact ω ∧ ω ⊆ (adelicBorel (K := F) (n := 2) : Subgroup _) ∧
      ∀ (b : A F) (a : (A F)ˣ), ∀ k ∈ C, ∀ (s : ℝ) (hs : 0 < s), s ^ Module.finrank ℚ F = ab a →
        ∃ γ γ' : GL (Fin 2) F, ∃ y ∈ ω, ∃ kk ∈ maxCompact (K := F) (n := 2), gl (nU b * mD a) * k =
          ratGL F 2 γ' * (ratGL F 2 γ * (y * diagUnits 2 ![posIdele s hs, (posIdele s hs)⁻¹] * kk)) := by
  obtain ⟨U, hU, hUm⟩ := units_cpt (hC.mul (isCompact_maxCompact (K := F) (n := 2)))
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  obtain ⟨Q₀, hQ₀, hQ⟩ := exists_isCompact_forall_exists_sub_mem F
  have hQc := hQ₀.prod (isCompact_integralFiniteAdeles F)
  let P : A F × (A F)ˣ × (A F)ˣ × (A F)ˣ → GL (Fin 2) (A F) := fun p =>
    gl (nU p.1) * diagUnits 2 ![p.2.1 * p.2.2.1, p.2.1⁻¹ * p.2.2.2]
  have hP : Continuous P := (cont_n.comp continuous_fst).mul ((continuous_diagUnits (K := F) 2).comp
    (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop))
  refine ⟨P '' _, (hQc.prod (hS.prod (hU.prod hU))).image hP, ?_, fun b a k hk s hs hsa => ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    refine mul_mem ?_ (diagUnits_mem_adelicBorel _ _)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vn]
  obtain ⟨β, hβ, kk, hkk, rfl⟩ := exists_adelicBorel_mul_maxCompact (K := F) (n := 2) k
  have hβC := (mul_inv_cancel_right β kk) ▸ Set.mul_mem_mul hk (show kk⁻¹ ∈ ((maxCompact (K := F) (n := 2) : Subgroup _) : Set (GL (Fin 2) (A F))) from inv_mem hkk)
  obtain ⟨u₀, hu₀, e₀⟩ := hUm β hβC hβ 0
  obtain ⟨u₁, hu₁, e₁⟩ := hUm β hβC hβ 1
  have h1 : β.val 1 0 = 0 := hβ (by decide : (0 : Fin 2) < 1)
  set p : (A F)ˣ := posIdele s hs with hp
  have hm : (IdeleGroup.ideleModule F (a * p⁻¹) : ℝ) = 1 := by
    have : IdeleGroup.ideleModule F a = IdeleGroup.ideleModule F p :=
      Subtype.ext (by rw [hp, ideleModule_posIdele, hsa]; rfl)
    rw [map_mul, map_inv, this, mul_inv_cancel]; rfl
  obtain ⟨c, hc⟩ := hSm (a * p⁻¹) hm.ge hm.le
  set g : (A F)ˣ := IdeleGroup.diagonal F c with hg
  set Y := gl (mD g) * (gl (nU b * mD a) * β) with hY
  have hY' := tri Y (g * a * u₀) ((g * a)⁻¹ * u₁)
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1, ← e₀, mul_assoc])
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, ← e₁, mul_assoc, mul_left_comm])
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1])
  set e := Y.val 0 1 * ((((g * a)⁻¹ * u₁)⁻¹ : (A F)ˣ) : A F)
  obtain ⟨ξ, hξ⟩ := hQ e
  obtain ⟨γ, hγ⟩ := rat_n ξ
  obtain ⟨γ', hγ'⟩ := rat_m c
  refine ⟨γ, γ'⁻¹, _, ⟨(e - rt ξ, g * (a * p⁻¹), u₀, u₁), ⟨hξ, hc, hu₀, hu₁⟩, rfl⟩, kk, hkk, ?_⟩
  have hd : diagUnits 2 ![g * a * u₀, (g * a)⁻¹ * u₁] =
      diagUnits 2 ![g * (a * p⁻¹) * u₀, (g * (a * p⁻¹))⁻¹ * u₁] * diagUnits 2 ![p, p⁻¹] := by
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_assoc, mul_comm, mul_left_comm]
  rw [map_inv, eq_inv_mul_iff_mul_eq, hγ, hγ', ← hg, ← mul_assoc _ β, ← mul_assoc, ← hY, hY', hd]
  have : gl (nU e) = gl (nU (rt ξ)) * gl (nU (e - rt ξ)) := by rw [← n_add]; congr 2; ring
  rw [this]
  simp only [P, mul_assoc]

private theorem pos_inv {s : ℝ} (hs : 0 < s) : (posIdele (K := F) s hs)⁻¹ = posIdele s⁻¹ (inv_pos.2 hs) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← posIdeleHom_apply (K := F) ⟨s, hs⟩, ← posIdeleHom_apply (K := F) ⟨s⁻¹, inv_pos.2 hs⟩, ← map_mul, ← map_one (posIdeleHom F)]
  exact congrArg _ (Subtype.ext (mul_inv_cancel₀ hs.ne'))

private theorem arith {C H M τ s s₀ h : ℝ} {e N d r : ℕ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hh : 0 ≤ h)
    (h1 : h ≤ H * (H * M * (τ * s) ^ e)) :
    C * (s⁻¹ / s) ^ (e * N + d * r) * h ^ N ≤ |C| * (H * (H * M * τ ^ e)) ^ N * s₀⁻¹ ^ (e * N + d * r) * (s ^ d)⁻¹ ^ r := by
  have hp : 0 < s := hs₀.trans_le hs
  have h2 : h ^ N ≤ (H * (H * M * τ ^ e)) ^ N * s ^ (e * N) := by
    refine (pow_le_pow_left₀ hh h1 N).trans_eq ?_
    rw [pow_mul, ← mul_pow, mul_pow τ]; ring_nf
  have h3 : s⁻¹ ^ (e * N + d * r) ≤ s₀⁻¹ ^ (e * N + d * r) := pow_le_pow_left₀ (by positivity) (inv_anti₀ hs₀ hs) _
  have h4 : 0 ≤ (H * (H * M * τ ^ e)) ^ N := by
    by_contra hn
    exact absurd (h2.trans_lt (mul_neg_of_neg_of_pos (not_le.1 hn) (by positivity))) (not_lt.2 (by positivity))
  calc C * (s⁻¹ / s) ^ (e * N + d * r) * h ^ N
      ≤ |C| * (s⁻¹ / s) ^ (e * N + d * r) * ((H * (H * M * τ ^ e)) ^ N * s ^ (e * N)) := by
        gcongr
        exact le_abs_self C
    _ = |C| * (H * (H * M * τ ^ e)) ^ N * s⁻¹ ^ (e * N + d * r) * (s ^ d)⁻¹ ^ r := by
        rw [div_eq_mul_inv, mul_pow, pow_add s⁻¹ (e * N), inv_pow (s ^ d), ← pow_mul, inv_pow s (e * N), inv_pow s (d * r)]
        field_simp
    _ ≤ _ := by gcongr

end SlopeTestRemainingChoices

set_option maxHeartbeats 800000 in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.decE :
    DecE := by
  intro F _ _ _ π f hf
  obtain ⟨ψ, rfl⟩ := UpperTheory.V.Cm.mem_range_ofCusp.2 (π.cusp f hf)
  refine ⟨⟨ψ.2.1.continuous, (π.cusp _ hf).1.left⟩, fun g => ?_, fun C hC c hc r => ?_⟩
  · letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
    rw [← Pp.int_one (ι := UPos 2 1), ← ψ.2.2 1 one_pos one_lt_two g]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : gl (nU (x default)) = unipGL x := by
      refine Units.ext ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Pp.vn, unipMatrix, blockEntry_apply]
      rfl
    simp only [this]
    rfl
  obtain ⟨ω, hω, hωB, hs⟩ := siegel hC
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hω
  set d := Module.finrank ℚ F
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  set s₀ := c ^ (d : ℝ)⁻¹
  have hs₀ : 0 < s₀ := Real.rpow_pos_of_pos hc _
  obtain ⟨N, hN⟩ := CuspidalSpectrum.exists_norm_le_siegel_root ψ.2 hω hωB (pow_pos hs₀ 2) one_pos one_lt_two
  set e := 2 * Fintype.card (InfinitePlace F)
  obtain ⟨B, hB⟩ := hN (e * N + d * r)
  set τ := 1 + s₀⁻¹ + s₀⁻¹ ^ 2
  set H := heightConst F 2
  refine ⟨|B| * (H * (H * M * τ ^ e)) ^ N * s₀⁻¹ ^ (e * N + d * r), fun b a k hk ha => ?_⟩
  set s := ab a ^ (d : ℝ)⁻¹
  have h0 : s₀ ≤ s := Real.rpow_le_rpow hc.le ha (by positivity)
  have hp : 0 < s := hs₀.trans_le h0
  have hsa : s ^ d = ab a := Real.rpow_inv_natCast_pow (hc.le.trans ha) hd
  obtain ⟨γ, γ', y, hy, kk, hkk, e1⟩ := hs b a k hk s hp hsa
  rw [e1, (π.cusp _ hf).1.left, (π.cusp _ hf).1.left, ← hsa]
  have hρ : ∀ i, 0 < (![s, s⁻¹] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> simp [hp]
  have e2 : (![posIdele s hp, (posIdele s hp)⁻¹] : Fin 2 → IdeleGroup F) = fun i => posIdele (![s, s⁻¹] i) (hρ i) := by
    funext i
    fin_cases i
    · rfl
    · exact pos_inv hp
  have hi : s⁻¹ ≤ s₀⁻¹ := inv_anti₀ hs₀ h0
  have h1 : 1 ≤ s₀⁻¹ * s := by rw [inv_mul_eq_div, one_le_div hs₀]; exact h0
  have hi0 : 0 < s₀⁻¹ := inv_pos.2 hs₀
  have h2 : s₀⁻¹ ≤ s₀⁻¹ ^ 2 * s := by nlinarith
  have hL : 1 ≤ τ * s ∧ s ≤ τ * s ∧ s⁻¹ ≤ τ * s := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [τ] <;> nlinarith
  have h3 := hB y hy _ hρ (fun i j hij => by
    obtain rfl : i = 0 := Fin.ext (by have := j.2; simp; omega)
    obtain rfl : j = 1 := Fin.ext (by simpa using hij)
    change s₀ ^ 2 * s⁻¹ ≤ s
    rw [← div_eq_mul_inv, div_le_iff₀ hp]; nlinarith) kk hkk _ rfl
  rw [e2]
  refine h3.trans (arith hs₀ h0 (height_pos _).le ?_)
  have hH : 0 ≤ H := zero_le_one.trans one_le_heightConst
  refine (height_mul_le _ _).trans ?_
  rw [height_eq_one_of_mem_maxCompact hkk, mul_one]
  refine mul_le_mul_of_nonneg_left ((height_mul_le _ _).trans ?_) hH
  have h5 := CuspidalSpectrum.height_diagUnits_posIdele_le (K := F) hρ hL.1 (fun i => by
    fin_cases i
    · exact ⟨hL.2.1, hL.2.2⟩
    · exact ⟨hL.2.2, by simpa using hL.2.1⟩)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hM y hy) hH) h5 (height_pos _).le
    (mul_nonneg hH ((height_pos _).le.trans (hM y hy)))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section Objects

variable {E : Type} [Field E] [NumberField E]

structure Bd (Ψ : GL (Fin 2) (A E) → ℂ) : Prop where
  cont : Continuous Ψ
  left : ∀ γ g, Ψ (ratGL E 2 γ * g) = Ψ g
  bdd : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ h : G1 E, ∀ k ∈ C, ‖Ψ (gl h * k)‖ ≤ B

def PosC (Ψ : GL (Fin 2) (A E) → ℂ) : Prop := ∀ s g, Ψ (GroundTheory.Automorphic.Reduction.centralSection E 2 s * g) = Ψ g

variable [_root_.NumberField.IsTotallyComplex E]

structure InvPair (V V' : Submodule ℂ (Sm E 2)) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) : Prop where
  st : _root_.GlobalTheory.CuspRep.IsStable V
  st' : _root_.GlobalTheory.CuspRep.IsStable V'
  fin : ∀ k (x : V) (y : V'), B ⟨act (.fin k) x.1, st _ _ x.2⟩ ⟨act (.fin k) y.1, st' _ _ y.2⟩ = B x y
  cpt : ∀ k (x : V) (y : V'), B ⟨act (.cpt k) x.1, st _ _ x.2⟩ ⟨act (.cpt k) y.1, st' _ _ y.2⟩ = B x y
  lie : ∀ X (x : V) (y : V'), B ⟨act (.lie X) x.1, st _ _ x.2⟩ y + B x ⟨act (.lie X) y.1, st' _ _ y.2⟩ = 0

end Objects

def MeanLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ y, IntegrableOn (fun h => Ψ (gl h * y)) N.D N.μ) ∧ (Continuous fun y => mean N fun x => Ψ (x * y)) ∧
  (∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y)) ∧
  ∀ γ y, (mean N fun x => Ψ (x * (ratGL E 2 γ * y))) = mean N fun x => Ψ (x * y)

def UILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E) ∧
  (∃ B : ℝ, ∀ t : (A E)ˣ, ab t = 1 → ‖β t‖ ≤ B) ∧ ∀ d : (A E)ˣ, ab d = 1 → (UI fun t => β (t * d)) = UI β

def IILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ Ψ', Bd Ψ' → ∀ c : ℂ, (II N fun x => Ψ x + c * Ψ' x) = II N Ψ + c * II N Ψ') ∧
  (PosC Ψ → ∀ g, (II N fun x => Ψ (x * g)) = II N Ψ)

def IILie : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : MeasE E) (Φ φ : Sm E 2) (X),
  (Bd fun x => Φ.1 x * φ.1 x) → (PosC fun x => Φ.1 x * φ.1 x) → (Bd fun x => (act (.lie X) Φ).1 x * φ.1 x) →
  (Bd fun x => Φ.1 x * (act (.lie X) φ).1 x) →
  (II N fun x => (act (.lie X) Φ).1 x * φ.1 x) + (II N fun x => Φ.1 x * (act (.lie X) φ).1 x) = 0

def SpanGrow : Prop := All fun E _ _ _ _ W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π,
  ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∃ (r : ℕ) (B : ℝ), ∀ b a, ∀ k ∈ C, c ≤ ab a →
    ‖Φ.1 (gl (nU b * mD a) * k)‖ ≤ B * ab a ^ r

def ProdBd : Prop := All fun _ _ _ _ _ W M _ P => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ φ ∈ P.V,
  (Bd fun x => Φ.1 x * φ.1 x) ∧ (PosInv π → GlobalTheory.DiscSpec.IsNormalised P → PosC fun x => Φ.1 x * φ.1 x)

def KillW : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ), Continuous Φ →
  (∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) → (∀ h, WE D Φ h = 0) → ∀ (h : G1 E) g, Φ (gl h * g) = Φ g

def PairEx : Prop := All fun _ _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  ∃ B : span W M π →ₗ[ℂ] P.V →ₗ[ℂ] ℂ, InvPair _ _ B ∧ (∀ x y, B x y = II N fun g => x.1.1 g * y.1.1 g) ∧
    ∀ x : span W M π, (∀ h, WE D x.1.1 h = 0) → B x = 0

def SplitEig : Prop := All fun E _ _ _ D W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ (v : P ℚ) (w : P E), SplitAt v w →
  ∀ B, π.HasSat v B → Fix w Φ.1 → EigAt w B (WE D Φ.1)

def SatPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (w : P E) (T : V →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ)),
  (∀ x : V, ∀ᶠ y in 𝓝 (1 : GL (Fin 2) (Kv w)), ∀ g, x.1.1 (g * lc w y) = x.1.1 g) →
  (∀ (x x' : V) y, (∀ g, x'.1.1 g = x.1.1 (g * lc w y)) → ∀ g, T x' g = T x (g * lc w y)) → (∀ x, T x = 0 → B x = 0) →
  ∀ C C' : Multiset ℂˣ, (∀ x : V, Fix w x.1.1 → EigAt w C (T x)) → (CG.mk Q).HasSat w C' → C' = C.map (·⁻¹)

def InfPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), m.card = 2 →
  (∀ u, ∀ Φ ∈ V, cap τ u Φ = (m.map (u + ·)).prod • Φ) → Q.HasInfChar τ m' → m' = m.map Neg.neg

def CharSel : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  (UI fun z => β (z * (Units.map (D.bar : A E →* A E) z)⁻¹)) ≠ 0 →
  ∃ χ : HChar E, (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) ∧
    (∀ z : (A E)ˣ, (∃ s, Matrix.GeneralLinearGroup.scalar (Fin 2) z = GroundTheory.Automorphic.Reduction.centralSection E 2 s) → χ.1 z = 1) ∧
    (UI fun t => ((χ.1 t : ℂˣ) : ℂ) * β t) ≠ 0

def CharDown : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (χ : HChar E),
  (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) → ∃ χ₀ : HChar ℚ, ∀ z : (A E)ˣ, χ.1 z = χ₀.1 (ideleNorm ℚ E z)

def FinS : Prop := All fun E _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  (∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (II N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0) →
  ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

def DownN : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], Module.finrank ℚ E = 2 → ∀ P : CuspSub E 2,
  GlobalTheory.DiscSpec.IsNormalised P → ConjInv P → ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AbLower
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem ab_lower {F : Type} [Field F] [NumberField F] {Ω : Set (G1 F)} (hΩ : IsCompact Ω) :
    ∃ lo : ℝ, 0 < lo ∧ ∀ p ∈ Ω, ∀ x : (A F)ˣ, (x : A F) = p 0 0 → ((x⁻¹ : (A F)ˣ) : A F) = p 1 1 → lo ≤ ab x := by
  let f : G1 F → A F × (A F)ᵐᵒᵖ := fun p => (p 0 0, MulOpposite.op (p 1 1))
  have hf : Continuous f :=
    (M.continuous_entry 0 0).prodMk (MulOpposite.continuous_op.comp (M.continuous_entry 1 1))
  have hS : IsCompact ((Units.embedProduct (A F)) ⁻¹' (f '' Ω)) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hΩ.image hf)
  obtain ⟨lo, _, hlo, _, hb⟩ := GroundTheory.BlockD.exists_pos_bounds_of_isCompact hS M.continuous_ab M.ab_pos
  refine ⟨lo, hlo, fun p hp x h0 h1 => (hb x ?_).1⟩
  refine ⟨p, hp, ?_⟩
  simp [f, Units.embedProduct, h0, h1]

private theorem parts_eq {F : Type} [Field F] [NumberField F] {t : ℝ} (ht : 0 < t) (a : InfiniteAdeleRing F)
    (h : ∀ w, InfinitePlace.Completion.extensionEmbedding w (a w) = (t : ℂ)) :
    Formalism.D.adeleOfParts F a 1 = ((GroundTheory.Automorphic.Reduction.posIdele t ht : IdeleGroup F) : AdeleRing (𝓞 F) F) := by
  rw [← GroundTheory.BlockD.adeleOfParts_posIdele t ht]
  congr 1
  funext w
  exact (InfinitePlace.Completion.extensionEmbedding w).injective
    ((h w).trans (GroundTheory.BlockD.extensionEmbedding_posIdele t ht w).symm)

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.redE :
    RedE := by
  intro E _ _
  obtain ⟨Ω, K, t₀, hΩ, h10, hK, ht₀, H⟩ := GroundTheory.BlockD.siegelSetsSL2Adelic_holds E
  obtain ⟨lo, hlo, hb⟩ := ab_lower hΩ
  set d : ℕ := Module.finrank ℚ E with hd
  refine ⟨lo * t₀ ^ d, K, by positivity, hK, fun h => ?_⟩
  obtain ⟨_, ⟨γ, rfl⟩, p, hp, t, ht, a, a', ha, k, hk, heq⟩ := H h
  have htpos : 0 < t := ht₀.trans_le ht
  set z : (A E)ˣ := GroundTheory.Automorphic.Reduction.posIdele t htpos with hz
  have ea : Formalism.D.adeleOfParts E a 1 = (z : A E) := parts_eq htpos a fun w => (ha w).2
  have eaa : Formalism.D.adeleOfParts E a 1 * Formalism.D.adeleOfParts E a' 1 = 1 := by
    refine Prod.ext (funext fun w => (ha w).1) ?_
    show (1 : FiniteAdeleRing (𝓞 E) E) * 1 = 1
    simp
  have ea' : Formalism.D.adeleOfParts E a' 1 = ((z⁻¹ : (A E)ˣ) : A E) := by
    rw [ea] at eaa
    exact (Units.inv_eq_of_mul_eq_one_right eaa).symm
  have hp10 : p 1 0 = 0 := h10 p hp
  have hdet : p 0 0 * p 1 1 = 1 := by
    have := p.det_coe
    rw [Matrix.det_fin_two] at this
    simpa [hp10] using this
  let x : (A E)ˣ := ⟨p 0 0, p 1 1, hdet, by rw [mul_comm]; exact hdet⟩
  have hx := hb p hp x rfl rfl
  refine ⟨γ, p 0 1 * p 0 0, x * z, k, hk, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [M.val_mul, M.val_mul, M.val_mul]
    refine heq.trans ?_
    rw [ea, ea']
    congr 1
    ext i j
    fin_cases i <;> fin_cases j
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-(p.1 0 1 * ((z⁻¹ : (A E)ˣ) : A E))) * hdet
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10]
    · simp [nU, mD, x, Matrix.mul_apply, Fin.sum_univ_two, hp10, mul_comm]
  · rw [M.ab_mul]
    have hz' : ab z = t ^ d := by
      simp [ab, hz, GroundTheory.Automorphic.Reduction.ideleModule_posIdele, hd]
    rw [hz']
    have : t₀ ^ d ≤ t ^ d := pow_le_pow_left₀ ht₀.le ht d
    exact mul_le_mul hx this (by positivity) (M.ab_pos x).le
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianMatrixBasisOne
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

section
variable {E : Type} [Field E] [NumberField E]

private noncomputable def mm (D : Dat ℚ E) (u t : ℚ) : E := algebraMap ℚ E u + algebraMap ℚ E t * D.θ

private noncomputable def hm (D : Dat ℚ E) (ξ : Fin 4 → ℚ) : Matrix (Fin 2) (Fin 2) E :=
  !![mm D (ξ 1) 0, mm D (ξ 2) (ξ 3); mm D (ξ 2) (-ξ 3), mm D (ξ 0) 0]

private theorem mm_base (D : Dat ℚ E) (u : ℚ) : mm D u 0 = algebraMap ℚ E u := by simp [mm]

private theorem σ_alg (D : Dat ℚ E) (u : ℚ) : D.σ (algebraMap ℚ E u) = algebraMap ℚ E u := D.σ.commutes u

private theorem σ_mm (D : Dat ℚ E) (u t : ℚ) : D.σ (mm D u t) = mm D u (-t) := by
  simp only [mm, map_add (f := _), map_mul, σ_alg, D.conj, map_neg]; ring

private theorem mm_mul (D : Dat ℚ E) (u t : ℚ) :
    mm D u t * mm D u (-t) = algebraMap ℚ E (u ^ 2 - D.δ * t ^ 2) := by
  have h := D.sq
  simp only [mm, map_sub, map_mul, map_pow, map_neg, ← h]; ring

private theorem herm_rp (D : Dat ℚ E) (ξ : Fin 4 → ℚ) :
    D.herm (rp ξ) = (hm D ξ).map (algebraMap E (A E)) := by
  have h0 : (0 : A ℚ) = rt (0 : ℚ) := (map_zero _).symm
  have hn : -(rt (ξ 3) : A ℚ) = rt (-ξ 3) := (map_neg _ _).symm
  ext i j
  fin_cases i <;> fin_cases j
  · change D.mkE (rt (ξ 1)) 0 = rt (mm D (ξ 1) 0)
    rw [h0, D.mkE_rt]; rfl
  · exact D.mkE_rt _ _
  · change D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (mm D (ξ 2) (-ξ 3))
    rw [hn, D.mkE_rt]; rfl
  · change D.mkE (rt (ξ 0)) 0 = rt (mm D (ξ 0) 0)
    rw [h0, D.mkE_rt]; rfl

private theorem act_iff (D : Dat ℚ E) (γ : SpecialLinearGroup (Fin 2) E) (ξ η : Fin 4 → ℚ) :
    D.act (gl (ratS E γ)) (rp ξ) = rp η ↔ γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ = hm D η := by
  haveI := AdeleBaseChange.nontrivial_adeleRing E
  have inj : Function.Injective fun X : Matrix (Fin 2) (Fin 2) E => X.map (algebraMap E (A E)) :=
    Matrix.map_injective (algebraMap E (A E)).injective
  have hγ : ((gl (ratS E γ)) : Matrix (Fin 2) (Fin 2) (A E)) = γ.1.map (algebraMap E (A E)) := by
    ext i j; exact ratS_apply γ i j
  have hs : D.star2 ((gl (ratS E γ)) : Matrix (Fin 2) (Fin 2) (A E)) =
      ((γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) := by
    ext i j
    rw [D.conjTransposeGal_apply, hγ]
    exact D.bar_rt _
  have hact : D.herm (D.act (gl (ratS E γ)) (rp ξ)) =
      (γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) := by
    rw [D.herm_act, hs, herm_rp, hγ, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro h
    apply inj
    change (γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) = (hm D η).map (algebraMap E (A E))
    rw [← hact, h, herm_rp]
  · intro h
    apply D.herm_injective
    rw [hact, h, herm_rp]

private theorem hermitianMatrix_basisOne (D : Dat ℚ E) (r : ℚ) : hm D ![0, r, 0, 0] = !![algebraMap ℚ E r, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hm, mm]

private theorem prod_pow_unitVector_val (D : Dat ℚ E) (g : Matrix (Fin 2) (Fin 2) E) (R : E) :
    g * !![R, 0; 0, 0] * (g.map D.σ)ᵀ =
      !![g 0 0 * R * D.σ (g 0 0), g 0 0 * R * D.σ (g 1 0); g 1 0 * R * D.σ (g 0 0), g 1 0 * R * D.σ (g 1 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem prod_low (D : Dat ℚ E) (w R : E) :
    (!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) E) * !![R, 0; 0, 0] * ((!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) E).map D.σ)ᵀ =
      !![R, R * D.σ w; w * R, w * R * D.σ w] := by
  rw [prod_pow_unitVector_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem δ_neg (D : Dat ℚ E) : D.δ < 0 := by
  have h := D.neg (algebraMap ℚ ℝ)
  simpa using h

private theorem rank_one (D : Dat ℚ E) (ξ : Fin 4 → ℚ) (h0 : ξ ≠ 0) (hq : qr D.δ ξ = 0) :
    ∃ (γ : SpecialLinearGroup (Fin 2) E) (r : ℚ), r ≠ 0 ∧ rp ξ = D.act (gl (ratS E γ)) (rp ![0, r, 0, 0]) := by
  have hq' : ξ 2 ^ 2 - D.δ * ξ 3 ^ 2 = ξ 1 * ξ 0 := by
    have : ξ 2 ^ 2 - D.δ * ξ 3 ^ 2 - ξ 1 * ξ 0 = 0 := hq
    linarith
  by_cases hx : ξ 1 = 0
  · have hδ := δ_neg D
    rw [hx, zero_mul] at hq'
    have h3 : ξ 3 = 0 := by
      by_contra h
      have : 0 < ξ 3 ^ 2 := by positivity
      nlinarith [sq_nonneg (ξ 2)]
    have h2 : ξ 2 = 0 := by
      rw [h3] at hq'
      simpa using hq'
    have hy : ξ 0 ≠ 0 := fun hy => h0 (by
      ext i; fin_cases i <;> simp [hy, hx, h2, h3])
    refine ⟨⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩, ξ 0, hy, ((act_iff D _ _ _).2 ?_).symm⟩
    rw [hermitianMatrix_basisOne, prod_pow_unitVector_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm, mm, hx, h2, h3]
  · have hx' : algebraMap ℚ E (ξ 1) ≠ 0 := by simpa using hx
    obtain ⟨w, hw, hσ⟩ : ∃ w : E, w * algebraMap ℚ E (ξ 1) = mm D (ξ 2) (-ξ 3) ∧
        D.σ w * algebraMap ℚ E (ξ 1) = mm D (ξ 2) (ξ 3) :=
      ⟨mm D (ξ 2) (-ξ 3) / algebraMap ℚ E (ξ 1), div_mul_cancel₀ _ hx', by
        rw [map_div₀, σ_mm, σ_alg, neg_neg, div_mul_cancel₀ _ hx']⟩
    refine ⟨⟨!![1, 0; w, 1], by simp [Matrix.det_fin_two]⟩, ξ 1, hx, ((act_iff D _ _ _).2 ?_).symm⟩
    have hmul := mm_mul D (ξ 2) (ξ 3)
    rw [hq', map_mul] at hmul
    change !![1, 0; w, 1] * _ * _ = _
    rw [hermitianMatrix_basisOne, prod_low, hm, mm_base, mm_base]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · change algebraMap ℚ E (ξ 1) * D.σ w = mm D (ξ 2) (ξ 3)
      rw [mul_comm]; exact hσ
    · exact hw
    · change w * algebraMap ℚ E (ξ 1) * D.σ w = algebraMap ℚ E (ξ 0)
      rw [hw]
      apply mul_left_cancel₀ hx'
      linear_combination mm D (ξ 2) (-ξ 3) * hσ + hmul
end

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orb1 :
    Orb1 := by
  intro E _ _ _ D
  refine ⟨fun γ => ?_, fun ξ h0 hq => rank_one D ξ h0 hq, fun γ r r' hr h => ?_, fun γ hγ => ?_, fun u r => ?_⟩
  · obtain ⟨N, -, hN⟩ := actRat ℚ E D (Matrix.SpecialLinearGroup.toGL γ)
    refine ⟨Matrix.toLin'OfInv (M := (N⁻¹ : GL (Fin 4) ℚ).val) (M' := N.val) (by simp) (by simp), fun ξ => ?_⟩
    rw [gl_ratS, hN]
    rfl
  · rw [act_iff, hermitianMatrix_basisOne, hermitianMatrix_basisOne, prod_pow_unitVector_val] at h
    have h11 := congrFun (congrFun h 1) 1
    simpa [hr] using h11
  · set a := D.b.repr (γ.1 0 0) 0
    set t := D.b.repr (γ.1 0 0) 1
    have ha : γ.1 0 0 = mm D a t := by
      have h := D.b.sum_repr (γ.1 0 0)
      rw [Fin.sum_univ_two, D.b0, D.b1] at h
      rw [mm, ← h]
      simp [a, t, Algebra.smul_def]
    have hdet : γ.1 0 0 * γ.1 1 1 = 1 := by
      have h := γ.2
      rw [Matrix.det_fin_two] at h
      have h10 : γ.1 1 0 = 0 := hγ
      simpa [h10] using h
    have hne : γ.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hnorm : γ.1 0 0 * D.σ (γ.1 0 0) = algebraMap ℚ E (a ^ 2 - D.δ * t ^ 2) := by
      rw [ha, σ_mm, mm_mul]
    refine ⟨a ^ 2 - D.δ * t ^ 2, fun hc => ?_, fun r => ?_⟩
    · rw [hc, map_zero] at hnorm
      exact (mul_ne_zero hne (by simpa using hne)) hnorm
    · refine (act_iff D _ _ _).2 ?_
      have h10 : γ.1 1 0 = 0 := hγ
      have h00 : γ.1 0 0 * algebraMap ℚ E r * D.σ (γ.1 0 0) = algebraMap ℚ E ((a ^ 2 - D.δ * t ^ 2) * r) := by
        rw [map_mul, ← hnorm]; ring
      rw [hermitianMatrix_basisOne, hermitianMatrix_basisOne, prod_pow_unitVector_val, h10, h00]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · obtain ⟨a, b, rfl⟩ := D.exists_mkE u
    rw [D.act_nU]
    ext i
    fin_cases i <;> simp [rp]
end
