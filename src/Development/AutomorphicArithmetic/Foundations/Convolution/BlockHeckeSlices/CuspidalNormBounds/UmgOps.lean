module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapPoly
open Polynomial GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem UpperTheory.ConvolutionTheory.BW.exists_capPoly {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (ℓ : A →ₗ[ℂ] ℂ) :
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ p.coeff n = ℓ 1 ∧ (∀ m, m + 1 = n → p.coeff m = ℓ (∑ i, F i i)) ∧
      ∀ u, p.eval u = ℓ (Formalism.REAL.qdet F (u + ((n : ℂ) - 1) / 2)) := by
  obtain ⟨-, htop, hsub⟩ := prod_linear n fun k => F k k - algebraMap ℂ A ((k : ℕ) : ℂ)
  have hN : (qdetPoly F).coeff n = 1 := by rw [coeff_qdetPoly_top F n (by omega), htop]
  refine ⟨∑ j ∈ Finset.range (n + 1), C (ℓ ((qdetPoly F).coeff j)) * (X + C (((n : ℂ) - 1) / 2)) ^ j, ?_, ?_, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_pow_X_add_C]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  · rw [finsetSum_coeff, Finset.sum_range_succ, Finset.sum_eq_zero, hN]
    · simp [coeff_X_add_C_pow]
    · intro j hj
      rw [coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hj)]
      simp
  · rintro m rfl
    have h1 : (qdetPoly F).coeff m = ∑ i, F i i - (((m + 1 : ℕ) : ℂ) * (((m + 1 : ℕ) : ℂ) - 1) / 2) • 1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [coeff_qdetPoly_top F m le_rfl, hsub m rfl, Finset.sum_sub_distrib, ← map_sum, sum_fin_cast,
        Algebra.algebraMap_eq_smul_one]
    rw [finsetSum_coeff, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero, hN, h1]
    · rw [coeff_C_mul, coeff_C_mul]
      simp only [coeff_X_add_C_pow, map_sub, map_smul, smul_eq_mul, Nat.sub_self, Nat.choose_self,
        Nat.add_sub_cancel_left, Nat.choose_succ_self_right]
      push_cast
      ring
    · intro j hj
      rw [coeff_C_mul, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hj)]
      simp
  · intro u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← evU_qdetPoly, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le F)), map_sum,
      eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
    simp [mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem uc_ind {P : UC E n → Prop} (h1 : ∀ c : ℂ, P (algebraMap ℂ _ c)) (hι : ∀ X, P (ιC E n X))
    (hadd : ∀ x y, P x → P y → P (x + y)) (hmul : ∀ x y, P x → P y → P (x * y)) (u : UC E n) : P u := by
  have hu : u ∈ Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} := by rw [adjoin_genC]; trivial
  have hs : ∀ (c : ℂ) x, P x → P (c • x) := fun c x hx => by
    rw [Algebra.smul_def]; exact hmul _ _ (h1 c) hx
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, i, j, rfl⟩ := hx
    rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL, sub_eq_add_neg, ← neg_smul]
    exact hs _ _ (hadd _ _ (hι _) (hs _ _ (hι _)))
  | algebraMap c => exact h1 c
  | add x y _ _ hx hy => exact hadd x y hx hy
  | mul x y _ _ hx hy => exact hmul x y hx hy

private theorem uc_fin (u : UC E n) (k : GL (Fin n) (Af E)) : Commute (uC E n u) (rt E n (finGL E n k)) := by
  induction u using uc_ind with
  | h1 c => rw [AlgHom.commutes]; exact Algebra.commutes c _
  | hι X => rw [uC_ιC]; exact lie_rt_fin X k
  | hadd x y hx hy => rw [map_add (f := _)]; exact hx.add_left hy
  | hmul x y hx hy => rw [map_mul]; exact hx.mul_left hy

private theorem uc_inf (y : GL (Fin n) (Cinf E)) (u : UC E n) :
    ∃ u', uC E n u * rt E n (infGL E n y) = rt E n (infGL E n y) * uC E n u' := by
  induction u using uc_ind with
  | h1 c => exact ⟨algebraMap ℂ _ c, by rw [AlgHom.commutes]; exact Algebra.commutes c _⟩
  | hι X =>
    refine ⟨ιC E n (toL ((y⁻¹).val * Matrix.of X * y.val)), ?_⟩
    rw [uC_ιC, uC_ιC, GlobalTheory.CapAdInv.rt_lie]
    congr 2
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
    rfl
  | hadd a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' + b', by rw [map_add (f := _), map_add (f := _), add_mul, mul_add, ha, hb]⟩
  | hmul a b ha hb =>
    obtain ⟨a', ha⟩ := ha
    obtain ⟨b', hb⟩ := hb
    exact ⟨a' * b', by rw [map_mul, map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]⟩

private theorem uc_rt (g : GA E n) (u : UC E n) : ∃ u', uC E n u * rt E n g = rt E n g * uC E n u' := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E n y * finGL E n l = g := ⟨_, _, infGL_mul_finGL g⟩
  obtain ⟨u', h⟩ := uc_inf y u
  exact ⟨u', by rw [map_mul, ← mul_assoc, h, mul_assoc, (uc_fin u' l).eq, mul_assoc]⟩

private theorem uc_left (h : GA E n) (u : UC E n) : ∀ φ : Sm E n, (∀ g, φ.1 (h * g) = φ.1 g) →
    ∀ g, (uC E n u φ).1 (h * g) = (uC E n u φ).1 g := by
  induction u using uc_ind with
  | h1 c =>
    intro φ hφ g
    rw [AlgHom.commutes]
    exact congrArg (c * ·) (hφ g)
  | hι X =>
    intro φ hφ g
    rw [uC_ιC]
    rw [lie_val X φ (smEq E n φ).2, AutomorphicForm.uAction_ι_apply, AutomorphicForm.uAction_ι_apply]
    have : AutomorphicForm.archSlice φ.1 (h * g) = AutomorphicForm.archSlice φ.1 g := by
      funext x
      simp only [AutomorphicForm.archSlice_apply, mul_assoc, hφ]
    simp only [this]
  | hadd a b ha hb =>
    intro φ hφ g
    rw [map_add (f := _)]
    exact congrArg₂ (· + ·) (ha φ hφ g) (hb φ hφ g)
  | hmul a b ha hb =>
    intro φ hφ g
    rw [map_mul]
    exact ha _ (hb φ hφ) g

private def stab (ψ : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {k | rt E n (finGL E n k) ψ = ψ}
  one_mem' := by simp
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hy, hx]
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

private theorem lev_rt (g : GA E n) (ψ : Sm E n) (h : IsOpen (stab ψ : Set (GL (Fin n) (Af E)))) :
    IsOpen (stab (rt E n g ψ) : Set (GL (Fin n) (Af E))) := by
  obtain ⟨y, l, rfl⟩ : ∃ y l, infGL E n y * finGL E n l = g := ⟨_, _, infGL_mul_finGL g⟩
  have hc : Continuous fun k : GL (Fin n) (Af E) => l⁻¹ * k * l := by fun_prop
  have ho : IsOpen ((fun k : GL (Fin n) (Af E) => l⁻¹ * k * l) ⁻¹' (stab ψ : Set _)) :=
    IsOpen.preimage hc h
  refine Subgroup.isOpen_of_mem_nhds (stab (rt E n (infGL E n y * finGL E n l) ψ)) (g := 1)
    (Filter.mem_of_superset (ho.mem_nhds ?_) fun k hk => ?_)
  · simpa using (stab ψ).one_mem
  · have hk' : rt E n (finGL E n (l⁻¹ * k * l)) ψ = ψ := hk
    change rt E n (finGL E n k) (rt E n (infGL E n y * finGL E n l) ψ) = rt E n (infGL E n y * finGL E n l) ψ
    have e : finGL E n k * (infGL E n y * finGL E n l) = infGL E n y * finGL E n l * finGL E n (l⁻¹ * k * l) := by
      rw [← mul_assoc, ← infGL_comm, mul_assoc, mul_assoc (infGL E n y), ← map_mul, ← map_mul]
      congr 2
      group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']

private theorem umg_zero : Umg (0 : Sm E n) :=
  ⟨fun _ _ => rfl, by
    have : {k | finRep E n k (0 : Sm E n) = 0} = Set.univ :=
      Set.eq_univ_of_forall (fun k => map_zero _)
    rw [this]
    exact isOpen_univ, 0, fun u => ⟨0, fun g => by simp⟩⟩

private theorem umg_add {φ ψ : Sm E n} (h : Umg φ) (h' : Umg ψ) : Umg (φ + ψ) := by
  refine ⟨fun γ g => congrArg₂ (· + ·) (h.left γ g) (h'.left γ g), ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := stab φ ⊓ stab ψ) (H₂ := stab (φ + ψ)) (fun k hk => ?_) (h.level.inter h'.level)
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) hk.1 hk.2)
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨M, hM⟩ := h'.growth
    refine ⟨max N M, fun u => ?_⟩
    obtain ⟨B, hB⟩ := hN u
    obtain ⟨C, hC⟩ := hM u
    refine ⟨|B| + |C|, fun g => ?_⟩
    have h1 := AutomorphicForm.one_le_height g
    rw [map_add (f := _), add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hB g).trans ?_) ((hC g).trans ?_))
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_left _ _)) (by positivity) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h1 (le_max_right _ _)) (by positivity) (abs_nonneg _)

private theorem umg_uC {φ : Sm E n} (h : Umg φ) (u : UC E n) : Umg (uC E n u φ) := by
  refine ⟨fun γ g => uc_left _ u φ (h.left γ) g, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := stab φ) (H₂ := stab (uC E n u φ)) (fun k hk => ?_) h.level
    exact (LinearMap.congr_fun (uc_fin u k).eq φ).symm.trans (congrArg (uC E n u) hk)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun v => ?_⟩
    have := hN (v * u)
    rw [map_mul] at this
    exact this

private theorem umg_smul {φ : Sm E n} (h : Umg φ) (c : ℂ) : Umg (c • φ) := by
  have := umg_uC h (algebraMap ℂ _ c)
  rw [AlgHom.commutes] at this
  exact this

private theorem umg_rt {φ : Sm E n} (h : Umg φ) (x : GA E n) : Umg (rt E n x φ) := by
  refine ⟨fun γ g => ?_, lev_rt x φ h.level, ?_⟩
  · show φ.1 (_ * g * x) = φ.1 (g * x)
    rw [mul_assoc]
    exact h.left γ _
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun u => ?_⟩
    obtain ⟨u', hu⟩ := uc_rt x u
    obtain ⟨B, hB⟩ := hN u'
    refine ⟨|B| * (AutomorphicForm.heightConst E n * AutomorphicForm.height x) ^ N, fun g => ?_⟩
    have e : uC E n u (rt E n x φ) = rt E n x (uC E n u' φ) := LinearMap.congr_fun hu φ
    rw [e]
    refine (hB (g * x)).trans ?_
    rw [mul_assoc, ← mul_pow, mul_right_comm]
    exact mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le
      (AutomorphicForm.height_mul_le _ _) N) (pow_nonneg (AutomorphicForm.height_pos _).le N) (abs_nonneg _)

private theorem umg_hk {φ : Sm E n} (h : Umg φ) (w : Pl E) (j : ℕ) : Umg (hk n w j φ) := by
  unfold hk
  rw [LinearMap.smul_apply]
  refine umg_smul ?_ _
  refine finsum_induction (fun T : Module.End ℂ (Sm E n) => Umg (T φ)) umg_zero (fun _ _ => umg_add) fun c => ?_
  exact umg_smul (umg_rt h (finGL E n (locGL E n w c.out))) _

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.umgOps :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.UmgOps E := by
  intro E _ _ _ n
  exact ⟨umg_zero, fun φ h => ⟨ContAut.continuous_of_isOpen_stab E n φ h.level, fun _ => umg_add h, umg_smul h,
    umg_uC h, umg_rt h, umg_hk h⟩⟩
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

theorem UpperTheory.ConvolutionTheory.BW.cuspUmg :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CuspUmg E := by
  intro E _ _ _ n f hf
  refine ⟨⟨hf.1.isLeftInvariant, level_of hf.1.isSmooth hf.1.isKFinite, ?_⟩, hf.2⟩
  obtain ⟨C₀, N, hC₀⟩ := hf.1.hasModerateGrowth
  refine ⟨N, fun u => ?_⟩
  show HasGrowth (uC E n u f).1 N
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, fun g => by simp⟩
  | tmul c x =>
    obtain ⟨C, hC⟩ := hasGrowth_uAction x hf.1.isSmoothKZ ⟨C₀, hC₀⟩
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [uC_tmul, mul_assoc]
    exact (norm_mul c _).le.trans (mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c))
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG GroundTheory.Automorphic UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem tj_mem (w : Pl E) (j : ℕ) :
    Tj ℂ n (Ov E w) (exists_isUnifV w).choose j ∈ Hecke ℂ (KGL w (n := n)) := Tj_mem_hecke (exists_isUnifV w).choose_spec j

private theorem hk_apply (w : Pl E) (j : ℕ) (φ : Sm E n) :
    hk n w j φ = (qc w ^ (((j : ℂ) * ((n : ℂ) - j)) / 2))⁻¹ •
      heckeVec (rw n w) (KGL w (n := n)) (Tj ℂ n (Ov E w) (exists_isUnifV w).choose j) φ := by
  unfold hk
  rw [LinearMap.smul_apply]
  congr 1
  have hf : (Function.support fun c : GL (Fin n) (w.adicCompletion E) ⧸ KGL w (n := n) =>
      Tj ℂ n (Ov E w) (exists_isUnifV w).choose j c.out • rw n w c.out).Finite :=
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w n) (tj_mem w j).2).subset fun c hc h0 => hc (by simp [h0])
  exact (LinearMap.applyₗ (R := ℂ) φ).toAddMonoidHom.map_finsum hf

private theorem hk_comm (w : Pl E) (j : ℕ) (A : Module.End ℂ (Sm E n)) (hA : ∀ g, Commute A (rw n w g)) :
    Commute A (hk n w j) := by
  refine LinearMap.ext fun φ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hk_apply, hk_apply, map_smul,
    map_heckeVec (Final.GLintComm E w n) (tj_mem w j) (ρ' := rw n w) A fun g y => LinearMap.congr_fun (hA g).eq y]

private theorem uC_fin (u : UC E n) (k : GL (Fin n) (Af E)) : Commute (uC E n u) (rt E n (finGL E n k)) := by
  let P := (Subalgebra.centralizer ℂ {rt E n (finGL E n k)}).comap (uC E n)
  have h1 : ∀ X, ιC E n X ∈ P := fun X => by
    rw [Subalgebra.mem_comap, uC_ιC]
    rintro _ rfl
    exact (lie_rt_fin _ _).symm
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ P :=
    Algebra.adjoin_le (by
      rintro _ ⟨τ, i, j, rfl⟩
      rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
      exact P.smul_mem (P.sub_mem (h1 _) (P.smul_mem (h1 _) _)) _)
  have hu : u ∈ P := h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)
  exact (hu _ rfl).symm

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem kgl_eq (w : Pl E) : GLnLocal.integralGL (w.adicCompletion E) n = KGL w (n := n) := by
  have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
      GLnLocal.integralGL (w.adicCompletion E) n = GLint (Fin n) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem split_k (w : Pl E) (k : KA E n) : ∃ k' : GA E n, (∀ g, Commute (rt E n k') (rw n w g)) ∧
    ∃ kw ∈ KGL w (n := n), rt E n k = rt E n k' * rw n w kw := by
  set kf := GeneralLinearGroup.map (pFin E) (k : GA E n) with hkf
  set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
  have hmem : kw ∈ KGL w (n := n) := by
    rw [← kgl_eq]
    have e : kw = Reduction.finAt w (k : GA E n) := by
      ext i j : 2
      rfl
    rw [e]
    exact k.2.2 w
  set u := kf * (locGL E n w kw)⁻¹ with hu
  have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
    rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) (k : GA E n)) * finGL E n u, fun g => ?_, kw, hmem, ?_⟩
  · refine Commute.map (f := rt E n) (y := finGL E n (locGL E n w g)) (Commute.mul_left (infGL_comm _ _) ?_)
    exact Commute.map (LocUniq.comm_locGL w hu1 g) (finGL E n)
  · change _ = _ * rt E n (finGL E n (locGL E n w kw))
    rw [← map_mul, mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]

private theorem rw_comm {w w' : Pl E} (e : w ≠ w') (g : GL (Fin n) (w'.adicCompletion E))
    (k : GL (Fin n) (w.adicCompletion E)) : Commute (rw n w' g) (rw n w k) :=
  Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E n)

private theorem hk_fixed (w : Pl E) (j : ℕ) {φ : Sm E n} (h : ∀ k ∈ KGL w (n := n), rw n w k φ = φ) :
    ∀ k ∈ KGL w (n := n), rw n w k (hk n w j φ) = hk n w j φ := fun k hk' => by
  rw [hk_apply, map_smul, GlobalTheory.LGrp.mem_fixed.1
    (SatCompare.heckeVec_mem_fixed (Final.GLintComm E w n) (tj_mem w j) (GlobalTheory.LGrp.mem_fixed.2 h)) k hk']

private theorem hk_zero (w : Pl E) {φ : Sm E n} (h : ∀ k ∈ KGL w (n := n), rw n w k φ = φ) : hk n w 0 φ = φ := by
  have e : Tj ℂ n (Ov E w) (exists_isUnifV w).choose 0 = dosetInd ℂ (KGL w (n := n)) 1 := by
    have d : diagJ n (exists_isUnifV w).choose 0 = 1 := by simp [diagJ]
    unfold Tj dosetInd
    congr 1
    ext g
    simp only [d, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, mul_one, SetLike.mem_coe, ← Units.val_mul, Units.val_inj]
  rw [hk_apply, e, SatCompare.heckeVec_one (Final.GLintComm E w n) (GlobalTheory.LGrp.mem_fixed.2 h)]
  simp

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.hkOps :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.HkOps E := by
  intro E _ _ _ n w j
  refine ⟨hk_apply w j, fun u => hk_comm w j _ fun g => uC_fin u _, fun y => hk_comm w j _ fun g => ?_,
    fun S φ hw hφ => ⟨fun w' hw' k hk' => ?_, hk_zero w (hφ w hw), fun k => ⟨fun w' hw' x hx => ?_, ?_⟩, fun w' hw' j' => ?_⟩⟩
  · exact Commute.map (f := rt E n) (y := finGL E n (locGL E n w g)) (infGL_comm _ _)
  · by_cases e : w = w'
    · subst e
      exact hk_fixed w j (hφ w hw) k hk'
    · rw [← Module.End.mul_apply, (hk_comm w j _ (rw_comm e k)).eq, Module.End.mul_apply, hφ w' hw' k hk']
  · obtain ⟨k', h1, kw, h2, h3⟩ := split_k w' k
    rw [h3, Module.End.mul_apply, hφ w' hw' kw h2, ← Module.End.mul_apply, ← (h1 x).eq, Module.End.mul_apply, hφ w' hw' x hx]
  · obtain ⟨k', h1, kw, h2, h3⟩ := split_k w k
    rw [h3, Module.End.mul_apply, Module.End.mul_apply, hφ w hw kw h2, hk_fixed w j (hφ w hw) kw h2,
      ← Module.End.mul_apply, (hk_comm w j _ h1).eq, Module.End.mul_apply]
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w n
      have hf := GlobalTheory.LGrp.mem_fixed.2 (hφ w hw)
      simp only [hk_apply, SatCompare.heckeVec_smul hK (tj_mem w _)]
      rw [← SatCompare.heckeVec_conv hK (tj_mem w _) (tj_mem w _) hf, ← SatCompare.heckeVec_conv hK (tj_mem w _) (tj_mem w _) hf,
        Final.HeckeCommGL E w n ℂ _ (tj_mem w j) _ (tj_mem w j'), smul_comm]
    · exact LinearMap.congr_fun (hk_comm w' j' _ fun g => (hk_comm w j _ (rw_comm e g)).symm).eq φ
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ResTyp
open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GroundTheory.Automorphic GroundTheory.Automorphic.Reduction Matrix

private theorem lev_val {R : Type} [CommRing R] {r s : ℕ} (a : GL (Fin r) R) (b : GL (Fin s) R) :
    (lev R r s (a, b)).val = reindex finSumFinEquiv finSumFinEquiv (fromBlocks a.val 0 0 b.val) := by
  have : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  rw [lev, this]
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with x | x <;> rcases y with y | y
  all_goals simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
    GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal']

private theorem lev_euclid {L : Type} [NormedField L] {r s : ℕ} (a : GL (Fin r) L) (b : GL (Fin s) L)
    (ha : ∀ y, euclidNorm (y ᵥ* a.val) = euclidNorm y) (hb : ∀ y, euclidNorm (y ᵥ* b.val) = euclidNorm y)
    (y : Fin (r + s) → L) : euclidNorm (y ᵥ* (lev L r s (a, b)).val) = euclidNorm y := by
  have sq : ∀ {m : ℕ} {x z : Fin m → L}, euclidNorm x = euclidNorm z → ∑ i, ‖x i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := fun h =>
    (Real.sqrt_inj (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 h
  have e1 : ∀ i, (y ᵥ* (lev L r s (a, b)).val) (Fin.castAdd s i) = ((fun j => y (Fin.castAdd s j)) ᵥ* a.val) i := by
    intro i
    simp [lev_val, vecMul, dotProduct, Fin.sum_univ_add]
  have e2 : ∀ i, (y ᵥ* (lev L r s (a, b)).val) (Fin.natAdd r i) = ((fun j => y (Fin.natAdd r j)) ᵥ* b.val) i := by
    intro i
    simp [lev_val, vecMul, dotProduct, Fin.sum_univ_add]
  rw [euclidNorm, euclidNorm, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [e1, e2]
  rw [sq (ha _), sq (hb _)]

private theorem lev_entries {L : Type} [Field L] (O : Subring L) {r s : ℕ} (a : GL (Fin r) L) (b : GL (Fin s) L)
    (ha : ∀ i j, a i j ∈ O) (hb : ∀ i j, b i j ∈ O) (x y : Fin (r + s)) : (lev L r s (a, b)).val x y ∈ O := by
  rw [lev_val, reindex_apply, submatrix_apply]
  rcases finSumFinEquiv.symm x with x | x <;> rcases finSumFinEquiv.symm y with y | y
  · exact ha x y
  · exact O.zero_mem
  · exact O.zero_mem
  · exact hb x y

theorem UpperTheory.ConvolutionTheory.BW.resTyp :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.ResTyp E := by
  intro E _ _ _ r s ρ
  have key : ∀ (k : KA E r) (k' : KA E s), lev (Ad E) r s ((k : GA E r), (k' : GA E s)) ∈ KA E (r + s) := by
    intro k k'
    obtain ⟨h1, h2⟩ := mem_maxCompact.1 k.2
    obtain ⟨h3, h4⟩ := mem_maxCompact.1 k'.2
    refine mem_maxCompact.2 ⟨fun w => ?_, fun v => ?_⟩
    · have e : infAt w (lev (Ad E) r s ((k : GA E r), (k' : GA E s))) = lev _ r s (infAt w k.1, infAt w k'.1) :=
        Slice1.map_lev (infEval w) _
      rw [e]
      exact lev_euclid _ _ (h1 w) (h3 w)
    · have e : finAt v (lev (Ad E) r s ((k : GA E r), (k' : GA E s))) = lev _ r s (finAt v k.1, finAt v k'.1) :=
        Slice1.map_lev (finEval v) _
      rw [e]
      obtain ⟨a1, a2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 (h2 v)
      obtain ⟨b1, b2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 (h4 v)
      refine (GLnLocal.mem_integralGL_iff _ _).2 ⟨lev_entries _ _ _ a1 b1, ?_⟩
      rw [← map_inv]
      exact lev_entries _ _ _ a2 b2
  let j : KA E r × KA E s →* KA E (r + s) :=
    ((lev (Ad E) r s).comp ((KA E r).subtype.prodMap (KA E s).subtype)).codRestrict _ fun k => key k.1 k.2
  have hj : Continuous j := Continuous.subtype_mk ((Slice1.continuous_lev (Ad E)).comp
    (continuous_subtype_val.prodMap continuous_subtype_val)) _
  refine ⟨⟨ρ.ρ.comp (j.comp (MonoidHom.inl _ _)), ρ.cont.comp (hj.comp (continuous_id.prodMk continuous_const)), ?_⟩,
    ⟨ρ.ρ.comp (j.comp (MonoidHom.inr _ _)), ρ.cont.comp (hj.comp (continuous_const.prodMk continuous_id)), ?_⟩, key⟩
  · funext k
    have h : lev (Ad E) r s ((k : GA E r), 1) ∈ KA E (r + s) := key k 1
    rw [resL, dite_eq_left h]
    rfl
  · funext k
    have h : lev (Ad E) r s (1, (k : GA E s)) ∈ KA E (r + s) := key 1 k
    rw [resR, dite_eq_left h]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.DatBasics
open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup
open UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem posIdele_inf (s : ℝ) (hs : 0 < s) (w : InfinitePlace E) :
    ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change GroundTheory.Global.posRealElem w _ = _
  unfold GroundTheory.Global.posRealElem
  rw [dite_eq_right hw]
  simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]

private noncomputable def eU (E : Type) [Field E] (x : ℝ) : (Cinf E)ˣ where
  val := fun _ => (Real.exp x : ℂ)
  inv := fun _ => (Real.exp (-x) : ℂ)
  val_inv := funext fun _ => by simp [← Complex.exp_add]
  inv_val := funext fun _ => by simp [← Complex.exp_add]

private theorem diag_eq (a : Fin n → ℝ) :
    (diagUnits n fun i => posIdele (K := E) (Real.exp (a i)) (Real.exp_pos _) : GA E n) =
      infGL E n (diagUnits n fun i => eU E (a i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  set y : GL (Fin n) (Cinf E) := diagUnits n fun i => eU E (a i) with hy
  have h2 : ((infGL E n y).val i j).2 = (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j :=
    congrArg (fun g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)
  have h1 : ∀ w, ((infGL E n y).val i j).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
    fun w => congrFun (infGL_entry y i j) w
  have hyv : y.val = Matrix.diagonal fun i => (fun _ : InfinitePlace E => (Real.exp (a i) : ℂ)) := rfl
  rw [coe_diagUnits]
  refine Prod.ext (funext fun w => ?_) ?_
  · rw [h1, hyv]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      exact (map_zero _).symm
  · rw [h2]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact FiniteAdeleRing.ext E fun v => posIdele_finite _ _ v
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl

private theorem sum_Eop (i : Fin n) : ∑ τ : E →+* ℂ, Eop τ i i = lie E n (toL (Matrix.single i i 1)) := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k l, coord τ (toL (Matrix.single i i (1 : Cinf E)) k l) = if i = k then if i = l then 1 else 0 else 0 := by
    intro k l
    change coord τ (Matrix.single i i (1 : Cinf E) k l) = _
    rw [Matrix.single_apply]
    by_cases h1 : i = k <;> by_cases h2 : i = l <;> simp [h1, h2]
  simp only [e]
  simp

private theorem lie_one : lie E n (oneL E n) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [lie_eq_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ l, coord τ (oneL E n k l) = if k = l then 1 else 0 := by
    intro l
    change coord τ ((1 : Matrix (Fin n) (Fin n) (Cinf E)) k l) = _
    rw [Matrix.one_apply]
    split_ifs <;> simp
  simp only [e]
  simp

private theorem lie_one_eq_zero (hn : 0 < n) (f : Sm E n) (h : ∀ t g, f.1 (zt E n t * g) = f.1 g) :
    lie E n (oneL E n) f = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have hd : HasDerivAt (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) (oneL E n) 0 := by
    have e : (fun t : ℝ => toL (diagUnits n fun _ => eU E t : GL (Fin n) (Cinf E)).val) =
        fun t : ℝ => Real.exp t • oneL E n := by
      funext t k l w
      change (Matrix.diagonal fun _ => (fun _ : InfinitePlace E => (Real.exp t : ℂ))) k l w =
        Real.exp t • (1 : Matrix (Fin n) (Fin n) (Cinf E)) k l w
      by_cases h : k = l
      · subst h; simp
      · simp [h]
    rw [e]
    simpa using (Real.hasDerivAt_exp 0).smul_const (oneL E n)
  have h0 : (diagUnits n fun _ => eU E 0 : GL (Fin n) (Cinf E)) = 1 := by
    rw [← map_one (diagUnits n)]
    congr 1
    funext i
    exact Units.ext (funext fun _ => by simp [eU])
  have h1 := hasDerivAt_curve f g (fun t => diagUnits n fun _ => eU E t) _ h0 hd
  have e : (fun t : ℝ => f.1 (g * infGL E n (diagUnits n fun _ => eU E t))) = fun _ => f.1 g := by
    funext t
    have ha : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    have e : rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (n * Module.finrank ℚ E * t), Real.exp_pos _⟩ =
        ⟨Real.exp t, Real.exp_pos t⟩ := by
      refine Subtype.ext ?_
      change Real.exp (n * Module.finrank ℚ E * t) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t
      rw [← Real.exp_mul]
      congr 1
      field_simp
    rw [← h (n * Module.finrank ℚ E * t) g, ← diag_eq, zt, centralSection_mul_comm, centralSection, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e]
    rfl
  rw [e] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem trace_eq {f : Sm E n} {τ : E →+* ℂ} {Λ : Fin n → ℂ} (hn : 0 < n)
    (h : ∀ u, cap τ u f = (∏ i, (u + Λ i)) • f) : (∑ i, Eop τ i i) f = (∑ i, Λ i) • f := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨p, -, -, h3, h4⟩ := exists_capPoly (Eop (a := m + 1) τ) (ℓ ∘ₗ LinearMap.applyₗ f)
  have e : p = Polynomial.C (ℓ f) * ∏ i, (Polynomial.X - Polynomial.C (-Λ i)) := by
    refine Polynomial.funext fun u => ?_
    rw [h4]
    change ℓ (cap τ u f) = _
    rw [h, map_smul]
    simp [Polynomial.eval_prod, mul_comm]
  have h5 := h3 m rfl
  have h6 := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (m + 1))) (fun i => -Λ i) (by simp)
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h6
  rw [e, Polynomial.coeff_C_mul, h6] at h5
  rw [map_sub, map_smul, sub_eq_zero]
  refine h5.symm.trans ?_
  simp [mul_comm]

private theorem blo_sum {S : Set (Pl E)} (b : Blo S n) : ∑ τ, ∑ i, b.Λ τ i = 0 := by
  have h := lie_one_eq_zero b.pos b.f b.cen
  rw [lie_one, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => trace_eq b.pos (b.inf τ), ← Finset.sum_smul] at h
  exact (smul_eq_zero.1 h).resolve_right b.ne

private theorem J_eq {S : Set (Pl E)} (d : Dat S n) (j : Fin d.len) : ∃ c : ℂ,
    d.J j = c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, lie E n (toL (Matrix.single i i 1)) :=
  ⟨_, by rw [Dat.J, Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i]⟩

private theorem comm_lie (i l : Fin n) :
    Commute (lie E n (toL (Matrix.single i i 1))) (lie E n (toL (Matrix.single l l 1))) := by
  have h := isLieHom_ιC (E := E) (a := n) (Matrix.single i i 1) (Matrix.single l l 1)
  have e : Matrix.single i i (1 : Cinf E) * Matrix.single l l 1 - Matrix.single l l 1 * Matrix.single i i 1 = 0 := by
    by_cases h : i = l
    · subst h; simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h), sub_zero]
  rw [e] at h
  have h2 := congrArg (uC E n) h
  simp only [map_sub, map_mul, uC_ιC] at h2
  have z : lie E n (toL 0) = 0 := map_zero (lie E n)
  rw [z] at h2
  first | exact sub_eq_zero.1 h2 | exact sub_eq_zero.1 h2.symm

private theorem comm_rt (i : Fin n) (a : Fin n → (Cinf E)ˣ) :
    Commute (lie E n (toL (Matrix.single i i 1))) (rt E n (infGL E n (diagUnits n a))) := by
  have h := GlobalTheory.CapAdInv.rt_lie (E := E) (diagUnits n a) (Matrix.single i i 1)
  have e : (diagUnits n a).val * Matrix.single i i (1 : Cinf E) * ((diagUnits n a)⁻¹).val = Matrix.single i i 1 := by
    rw [Units.mul_inv_eq_iff_eq_mul, coe_diagUnits]
    ext k l
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp
  rw [e] at h
  exact h.symm

private theorem comb {S : Set (Pl E)} (d : Dat S n) : Function.Surjective d.idx ∧ d.len ≤ n ∧
    (∀ j, ∑ τ, ∑ i, (if d.idx i = j then d.lam τ i else 0) = 0) ∧
    ∀ j w, w ∉ S → (d.sat j w).card = ∑ i, if d.idx i = j then 1 else 0 := by
  induction d with
  | nil => exact ⟨fun j => j.elim0, le_rfl, fun j => j.elim0, fun j => j.elim0⟩
  | @cons r s b d ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    let I : Fin (r + s) → Fin (d.len + 1) := Fin.addCases (fun _ => 0) fun i => (d.idx i).succ
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ∀ j : Fin (d.len + 1), ∃ i, I i = j
      refine Fin.cases ⟨Fin.castAdd s ⟨0, b.pos⟩, Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _⟩ fun j => ?_
      obtain ⟨i, rfl⟩ := h1 j
      exact ⟨Fin.natAdd r i, by simp [I]⟩
    · have := b.pos
      change d.len + 1 ≤ _
      omega
    · change ∀ j : Fin (d.len + 1), ∑ τ, ∑ i, (if I i = j then
        Fin.addCases (motive := fun _ => ℂ) (b.Λ τ) (d.lam τ) i else 0) = 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases ?_ fun j => ?_
      · simpa [Fin.succ_ne_zero] using blo_sum b
      · simpa [(Fin.succ_ne_zero _).symm] using h3 j
    · change ∀ (j : Fin (d.len + 1)) w, w ∉ S →
        (Fin.cases (motive := fun _ => Pl E → Multiset ℂˣ) b.sat d.sat j w).card = ∑ i, if I i = j then 1 else 0
      simp only [Fin.sum_univ_add, I, Fin.addCases_left, Fin.addCases_right]
      refine Fin.cases (fun w hw => ?_) fun j w hw => ?_
      · simpa [Fin.succ_ne_zero] using (b.isSat w hw).2.2.1
      · simpa [(Fin.succ_ne_zero _).symm] using h4 j w hw

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.datBasics :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.DatBasics E := by
  intro E _ _ _
  refine ⟨fun S r b => blo_sum b, fun S n d => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := comb d
  have hp : ∀ x : ℝ, posIdele (K := E) (Real.exp x) (Real.exp_pos x) = posIdeleHom E ⟨Real.exp x, Real.exp_pos x⟩ :=
    fun _ => rfl
  refine ⟨h1, h2, fun j => ?_, fun j w hw => ?_, ?_, fun v v' => ?_, fun v => ⟨_, diag_eq _⟩, fun j l => ?_,
    fun j v => ?_, fun j => ?_⟩
  · rw [Finset.sum_filter, Fintype.sum_prod_type]
    exact h3 j
  · rw [h4 j w hw, Dat.size, Finset.card_filter]
  · rw [Dat.tr, ← map_one (diagUnits n)]
    congr 1
    funext i
    rw [hp, Pi.one_apply, ← map_one (posIdeleHom E)]
    congr 1
    exact Subtype.ext (by simp)
  · rw [Dat.tr, Dat.tr, Dat.tr, ← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, hp, hp, hp, ← map_mul]
    congr 1
    exact Subtype.ext (by simp [add_div, Real.exp_add])
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨c', hc'⟩ := J_eq d l
    rw [hc, hc']
    set_option synthInstance.maxHeartbeats 400000 in
    exact ((Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun k _ => comm_lie i k).smul_left c).smul_right c'
  · obtain ⟨c, hc⟩ := J_eq d j
    obtain ⟨a, ha⟩ : ∃ a : Fin n → (Cinf E)ˣ, d.tr v = infGL E n (diagUnits n a) := ⟨_, diag_eq _⟩
    rw [hc, ha]
    exact (Commute.sum_left _ _ _ fun i _ => comm_rt i a).smul_left c
  · obtain ⟨c, hc⟩ := J_eq d j
    exact ⟨c • ∑ i ∈ Finset.univ.filter fun i => d.idx i = j, ιC E n (toL (Matrix.single i i 1)), by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => uC_ιC _]
      exact hc⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.ZSpec
open NumberField

theorem UpperTheory.ConvolutionTheory.BW.zSpec :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.ZSpec E := by
  intro E _ _ _ n τ
  have key : ∀ ℓ : UpperTheory.V.Cm.UC E n →ₗ[ℂ] ℂ, ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ p.coeff n = ℓ 1 ∧
      (∀ u, p.eval u = ℓ (UpperTheory.V.Cm.capC τ u)) ∧ ∀ i, ℓ (zC E n τ i) = p.coeff (n - i) := fun ℓ => by
    obtain ⟨p, h1, h2, -, h4⟩ := exists_capPoly (UpperTheory.V.Cm.genC (a := n) τ) ℓ
    refine ⟨p, h1, h2, h4, fun i => ?_⟩
    have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1))) :=
      fun a _ b _ h => Fin.ext (Nat.cast_injective h)
    have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h1)
    conv_rhs => rw [Lagrange.eq_interpolate hinj hd]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, zC, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, h4, map_smul, smul_eq_mul, mul_comm]
    rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, -, h2, -, h4⟩ := key ℓ
    rw [map_sub, h4, Nat.sub_zero, h2, sub_self]
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, h1, -, h3, h4⟩ := key ℓ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, ← h3, map_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, h4, smul_eq_mul, mul_comm]
    simp
end
