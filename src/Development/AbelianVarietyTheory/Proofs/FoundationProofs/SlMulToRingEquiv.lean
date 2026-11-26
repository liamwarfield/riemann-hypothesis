module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegralPadicInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ

theorem toGQ_mul_of_pos (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dite_eq_left hmm, dite_eq_left h, dite_eq_left h']
  apply Subtype.ext
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul] at *
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem mZl_mul (l : ℕ) [Fact l.Prime] (m m' : Matrix (Fin 2) (Fin 2) ℤ) :
    mZl l (m * m') = mZl l m * mZl l m' := by
  unfold mZl; rw [Matrix.map_mul]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.kmap_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) (x : X.Khat l) :
    X.kmap l ψ (X.kmap l φ x) = X.kmap l (φ.trans ψ) x := by
  unfold Tower.kmap
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp]
  congr 3

theorem Tower.sl_mul_toRingEquiv (X : Tower Ω ε) (g h : GQ) :
    (X.sl (g * h)).toRingEquiv = (X.sl g).toRingEquiv.trans (X.sl h).toRingEquiv := by
  ext f; exact X.sl_mul g h f

theorem Tower.act_act (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) (b : X.Fn l) :
    X.act l m' (X.act l m b) = X.act l (m * m') b := by
  funext u
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap, toGQ_mul_of_pos m m' hm hm', Tower.sl_mul_toRingEquiv, mZl_mul, Matrix.mulVec_mulVec]

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.CupCob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_int (x : Qbar l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | (apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt ..)

theorem nsub_le_max (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  have : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  rw [this]; exact c.O.algebraMap_mem _

theorem eps_cont : Continuous fun s : G ℚ Ω => eps l s :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

theorem det_sq (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det ^ 2 = 1 := by
  have := congrArg (fun f => ((f s : (Qbar l)ˣ) : Qbar l)) h
  simpa [dt] using this

theorem mat_dual1 (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  have hinv : (dt W s)⁻¹ = dt W s := by
    have h2 := congrArg (fun f => f s) h
    simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h2
    exact inv_eq_of_mul_eq_one_left h2
  simp only [mat, dual1, tw_val, MonoidHom.mul_apply, MonoidHom.inv_apply, hinv, Units.val_mul]
  simp [dt, eps]

theorem om_smul_right (k : Qbar l) (p q : Fin 2 → Qbar l) : om p (k • q) = k * om p q := by
  simp only [om, Pi.smul_apply, smul_eq_mul]; ring

theorem om_mulVec (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (p q : Fin 2 → Qbar l) :
    om (M *ᵥ p) (M *ᵥ q) = M.det * om p q := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem om_key (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) (p q : Fin 2 → Qbar l) :
    om (mat W s *ᵥ p) (mat (dual1 W) s *ᵥ q) = eps l s * om p q := by
  rw [mat_dual1 W h, Matrix.smul_mulVec, om_smul_right, om_mulVec]
  linear_combination (eps l s * om p q) * det_sq W h s

theorem mat_dual1_mul (W : R2 Ω l) (s t : G ℚ Ω) (x : Fin 2 → Qbar l) :
    mat (dual1 W) (s * t) *ᵥ x = mat (dual1 W) s *ᵥ (mat (dual1 W) t *ᵥ x) := by
  simp only [mat, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (x : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ i, x i ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem (hM _ _) (hx _)) (mul_mem (hM _ _) (hx _))

theorem om_mem (c : Coef l) (p q : Fin 2 → Qbar l) (hp : ∀ i, p i ∈ c.O) (hq : ∀ i, q i ∈ c.O) : om p q ∈ c.O :=
  sub_mem (mul_mem (hp _) (hq _)) (mul_mem (hp _) (hq _))

theorem dual_representation_integral (c : Coef l) (W : R2 Ω l) (h : dt W ^ 2 = 1) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω)
    (i j : Fin 2) : mat (dual1 W) s i j ∈ c.O := by
  rw [mat_dual1 W h, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem (mul_mem (eps_mem c s) ?_) (hint s i j)
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hint _ _ _) (hint _ _ _)) (mul_mem (hint _ _ _) (hint _ _ _))

theorem mulVec_le {L : ℝ} (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (q : Fin 2 → Qbar l)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) (i : Fin 2) : ‖(M *ᵥ q) i‖ ≤ L := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hM _ _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem om_le_left {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ L) (hq : ∀ i, ‖q i‖ ≤ 1) :
    ‖om p q‖ ≤ L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hp 0)
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) hL).trans (le_of_eq (mul_one L))

theorem om_le_right {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) :
    ‖om p q‖ ≤ L := by
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem ident_a (A v w x B2 B1 B0 : Fin 2 → Qbar l) (e : Qbar l) (key : om w v = e * om x B0) :
    om A v - (e * om x B0 - om x B2 + om x B1) = om (A - (w - x)) v + om x (B2 - (B1 + v)) := by
  simp only [om, Pi.sub_apply, Pi.add_apply] at *
  linear_combination key

theorem ident_b (As At Ast Bt x : Fin 2 → Qbar l) (M P : Matrix (Fin 2) (Fin 2) (Qbar l)) (N : Matrix (Fin 2) (Fin 2) (Qbar l))
    (e : Qbar l) (key : om (P *ᵥ At) (M *ᵥ (N *ᵥ x)) = e * om At (N *ᵥ x)) :
    om As (M *ᵥ Bt) - (e * -om At (N *ᵥ x) - -om Ast (M *ᵥ (N *ᵥ x)) + -om As (M *ᵥ x)) =
      om As (M *ᵥ (Bt - (N *ᵥ x - x))) - om (Ast - (As + P *ᵥ At)) (M *ᵥ (N *ᵥ x)) := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply] at *
  linear_combination -key

end GlobalTheory.Ord2.CupCob

namespace GlobalTheory.Ord2.CupCob

theorem cup_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l)
    (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 →
    Coc1 c n W H a → Coc1 c n (dual1 W) H b → (Cob1 c n W H a ∨ Cob1 c n (dual1 W) H b) → Cob2 c n H (cup W a b) := by
  intro l _ Ω _ _ _ c n W H a b hW hint hdet ha hb hcob
  have hWn : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hint s i j)
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := dual_representation_integral c W hdet hint
  have hDn : ∀ s i j, ‖mat (dual1 W) s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hDm s i j)
  have han : ∀ s i, ‖a s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (ha.2.1 s i)
  have hbn : ∀ s i, ‖b s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (hb.2.1 s i)
  rcases hcob with ⟨x, hx, hax⟩ | ⟨x, hx, hbx⟩
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    refine ⟨fun t => om x (b t), ?_, fun t => om_mem c _ _ hx (hb.2.1 t), ?_⟩
    · show ContinuousOn (fun t => x 0 * b t 1 - x 1 * b t 0) H
      exact (continuousOn_const.mul (continuousOn_pi.1 hb.1 1)).sub (continuousOn_const.mul (continuousOn_pi.1 hb.1 0))
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s x (b t)
      rw [cup, ident_a (a s) (mat (dual1 W) s *ᵥ b t) (mat W s *ᵥ x) x (b (s * t)) (b s) (b t) (eps l s) key]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_left _ _ (fun i => hax s hs i) (mulVec_le _ _ (hDn s) (hbn t))
      · exact om_le_right _ _ hxn (fun i => hb.2.2 s hs t ht i)
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
    have hD : Continuous fun s => mat (dual1 W) s := by
      have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (mat_dual1 W hdet)
      rw [this]
      exact (eps_cont.mul hM.matrix_det).smul hM
    have hv : Continuous fun s => mat (dual1 W) s *ᵥ x := hD.matrix_mulVec continuous_const
    refine ⟨fun s => -om (a s) (mat (dual1 W) s *ᵥ x), ?_,
      fun s => neg_mem (om_mem c _ _ (ha.2.1 s) (mulVec_mem c _ _ (hDm s) hx)), ?_⟩
    · show ContinuousOn (fun s => -(a s 0 * (mat (dual1 W) s *ᵥ x) 1 - a s 1 * (mat (dual1 W) s *ᵥ x) 0)) H
      exact (((continuousOn_pi.1 ha.1 0).mul ((continuous_apply 1).comp hv).continuousOn).sub
        ((continuousOn_pi.1 ha.1 1).mul ((continuous_apply 0).comp hv).continuousOn)).neg
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s (a t) (mat (dual1 W) t *ᵥ x)
      beta_reduce
      rw [cup, mat_dual1_mul W s t x,
        ident_b (a s) (a t) (a (s * t)) (b t) x (mat (dual1 W) s) (mat W s) (mat (dual1 W) t) (eps l s) key]
      refine (nsub_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_right _ _ (han s) (mulVec_le _ _ (hDn s) (fun i => hbx t ht i))
      · exact om_le_left _ _ (fun i => ha.2.2 s hs t ht i)
          (mulVec_le _ _ (hDn s) (mulVec_le _ _ (hDn t) hxn))

end GlobalTheory.Ord2.CupCob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryModStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_product_coboundary_mod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → Coc1 c n W H a → Coc1 c n (dual1 W) H b → (Cob1 c n W H a ∨ Cob1 c n (dual1 W) H b) → Cob2 c n H (cup W a b) := by
  first | exact @GlobalTheory.Ord2.CupCob.cup_cob | exact GlobalTheory.Ord2.CupCob.cup_cob | (intros; apply GlobalTheory.Ord2.CupCob.cup_cob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffNormLeOne
namespace GlobalTheory.IntegralCoefficientNormBound

open Polynomial

theorem coeff_norm_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rw [show algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)
      = ((algebraMap ℤ_[l] ℚ_[l] a : ℚ_[l]) : PadicAlgCl l) from rfl, PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) := by
  intro l _ x hx
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := h.le
  have key : (aeval x p) = x ^ p.natDegree +
      ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := by
    conv_lhs => rw [hm.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_add (f := _), map_sum, aeval_C, aeval_X_pow]
  rw [← aeval_def] at hp
  rw [hp] at key
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at key
    simp at key
  have hsum : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ (p.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
          gcongr
          exact coeff_norm_le_one l _
      _ = ‖x‖ ^ i := one_mul _
      _ ≤ ‖x‖ ^ (p.natDegree - 1) := pow_le_pow_right₀ hx1 (by omega)
  have heq : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree,
      algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := eq_neg_of_add_eq_zero_left key.symm
  have : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]; exact hsum
  have hlt : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

end GlobalTheory.IntegralCoefficientNormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem norm_le_one_of_isIntegral_zl (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralCoefficientNormBound.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (a : c.O) :
    ‖(a : PadicAlgCl l)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_zl l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map c.O.val)

theorem norm_unit_coefO {l : ℕ} [Fact l.Prime] (c : Coef l) (u : c.Oˣ) :
    ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem_coefO c u
  have h3 := norm_le_one_of_mem_coefO c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

theorem mem_coefO_of_memE_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l),
    MemE c x → ‖x‖ ≤ 1 → x ∈ c.O := by
  intro l _ c x hE hx
  obtain ⟨k, hk⟩ := hE
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk
  set y : c.O := ⟨_, hk⟩ with hy
  set L : c.O := (l : c.O) ^ k with hL
  have hLval : ((L : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k := by simp [hL]
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hL0 : L ≠ 0 := by
    intro h
    have : ((L : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    rw [hLval] at this
    exact pow_ne_zero k hl0 this
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  by_cases hy0 : y = 0
  · have : (l : PadicAlgCl l) ^ k * x = 0 := by
      have := congrArg (fun z : c.O => (z : PadicAlgCl l)) hy0
      simpa [hy] using this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (pow_ne_zero k hl0)
    · rw [h]; exact c.O.zero_mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ z : c.O, z ≠ 0 → ∃ n : ℕ, ‖(z : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n ∧
      ϖ ^ n ∣ z ∧ z ∣ ϖ ^ n := by
    intro z hz
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    refine ⟨n, ?_, ?_, ?_⟩
    · rw [h, Subalgebra.coe_mul, norm_mul, norm_unit_coefO, one_mul, Subalgebra.coe_pow, norm_pow]
    · exact ⟨(u : c.O), by rw [h, mul_comm]⟩
    · exact ⟨((u⁻¹ : c.Oˣ) : c.O), by rw [h, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  obtain ⟨a, hya, hdy, -⟩ := key y hy0
  obtain ⟨b, hLb, -, hdL⟩ := key L hL0
  have hϖ1 : ‖(ϖ : PadicAlgCl l)‖ ≤ 1 := norm_le_one_of_mem_coefO c ϖ
  have hϖ0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hyx : ((y : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k * x := rfl
  have hLlt : ‖((L : c.O) : PadicAlgCl l)‖ < 1 := by
    rw [hLval, norm_pow, hnl]
    exact pow_lt_one₀ (by positivity) hlt1 (by omega)
  have hϖlt : ‖(ϖ : PadicAlgCl l)‖ < 1 := by
    rcases lt_or_eq_of_le hϖ1 with h | h
    · exact h
    exfalso
    rw [hLb, h, one_pow] at hLlt
    exact lt_irrefl _ hLlt
  have hab : b ≤ a := by
    have hle : ‖(ϖ : PadicAlgCl l)‖ ^ a ≤ ‖(ϖ : PadicAlgCl l)‖ ^ b := by
      rw [← hya, ← hLb, hyx, hLval, norm_mul]
      calc ‖(l : PadicAlgCl l) ^ k‖ * ‖x‖ ≤ ‖(l : PadicAlgCl l) ^ k‖ * 1 :=
            mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = _ := mul_one _
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 hle
  have hdiv : L ∣ y := dvd_trans hdL (dvd_trans (pow_dvd_pow ϖ hab) hdy)
  obtain ⟨z, hz⟩ := hdiv
  have : (l : PadicAlgCl l) ^ k * x = (l : PadicAlgCl l) ^ k * (z : PadicAlgCl l) := by
    rw [← hyx, hz, Subalgebra.coe_mul, hLval]
  rw [mul_left_cancel₀ (pow_ne_zero k hl0) this]
  exact z.2

end GlobalTheory.Ord2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOneStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integers_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (x : Qbar l), MemE c x → ‖x‖ ≤ 1 → x ∈ c.O := by
  first | exact @GlobalTheory.Ord2.mem_coefO_of_memE_norm_le_one | exact GlobalTheory.Ord2.mem_coefO_of_memE_norm_le_one | (intros; apply GlobalTheory.Ord2.mem_coefO_of_memE_norm_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapPadicIntQbarContinuous
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

theorem algebraMap_padicInt_qbar_continuous (l : ℕ) [Fact l.Prime] :
    Continuous (algebraMap ℤ_[l] (Qbar l)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (by exact continuous_subtype_val)

theorem Coef.isCompact_O (l : ℕ) [Fact l.Prime] (c : Coef l) :
    IsCompact ((c.O : Set (Qbar l))) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[l] c.O
  have hg : Continuous (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) := by
    have h : (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) =
        fun v => ∑ i, algebraMap ℤ_[l] (Qbar l) (v i) *
          ((f (fun j => if i = j then 1 else 0) : c.O) : Qbar l) := by
      funext v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp [Algebra.smul_def]
    rw [h]
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact ((algebraMap_padicInt_qbar_continuous l).comp (continuous_apply i)).mul continuous_const
  have hrange : Set.range (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) = (c.O : Set (Qbar l)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (f v).2
    · intro hx
      obtain ⟨v, hv⟩ := hf ⟨x, hx⟩
      exact ⟨v, by simp [hv]⟩
  rw [← hrange]
  exact isCompact_range hg

theorem norm_natCast_prime_qbar (l : ℕ) [Fact l.Prime] :
    ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem coef_limit (l : ℕ) [Fact l.Prime] (c : Coef l) (a : ℕ → Qbar l)
    (ha : ∀ r, a r ∈ c.O) (hstep : ∀ r, ‖a (r + 1) - a r‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∃ b ∈ c.O, ∀ r, ‖b - a r‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq
  have hq1 : q < 1 := norm_natCast_prime_qbar l
  have hq0 : 0 ≤ q := norm_nonneg _
  have hstep' : ∀ r, ‖a (r + 1) - a r‖ ≤ q ^ r := fun r => by simpa [norm_pow] using hstep r

  have htail : ∀ N k, ‖a (N + k) - a N‖ ≤ q ^ N := by
    intro N k
    induction k with
    | zero => simpa using pow_nonneg hq0 N
    | succ k ih =>
      have e : a (N + (k + 1)) - a N = (a (N + k + 1) - a (N + k)) + (a (N + k) - a N) := by
        rw [← add_assoc]; abel
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep' (N + k)).trans (pow_le_pow_of_le_one hq0 hq1.le (Nat.le_add_right N k))
  have htail' : ∀ N n, N ≤ n → ‖a n - a N‖ ≤ q ^ N := by
    intro N n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact htail N k
  have hcau : CauchySeq a := by
    refine cauchySeq_of_le_tendsto_0 (fun N => q ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [dist_eq_norm]
    have e : a n - a m = (a n - a N) + -(a m - a N) := by abel
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (htail' N n hn) ?_)
    rw [norm_neg]; exact htail' N m hm
  obtain ⟨b, hb, hlim⟩ := cauchySeq_tendsto_of_isComplete (GlobalTheory.Coef.isCompact_O l c).isComplete ha hcau
  refine ⟨b, hb, fun r => ?_⟩
  have hmem : b ∈ Metric.closedBall (a r) (q ^ r) := by
    refine Metric.isClosed_closedBall.mem_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop r] with n hn
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact htail' r n hn
  rw [Metric.mem_closedBall, dist_eq_norm] at hmem
  simpa [norm_pow] using hmem

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramified
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem eps_eq_algebraMap (s : G ℚ Ω) :
    eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
  simp [eps, cycBar]
  rfl

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  rw [eps_eq_algebraMap]; exact c.O.algebraMap_mem _

theorem continuous_eps : Continuous (fun s : G ℚ Ω => eps l s) := by
  have h : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
  have e : ∀ s : G ℚ Ω, eps l s = algebraMap ℚ_[l] (Qbar l) (((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
    fun s => rfl
  simp only [e]
  have hc : Continuous (fun x : ℤ_[l] => (x : ℚ_[l])) := continuous_subtype_val
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc.comp h)

theorem eps_eq_one_of_mem_Ine [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} {v : Pl}
    (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) (h : IsPlaceOver A v) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    eps l σ = 1 := by
  have e : cycBar ℚ Ω l σ = cyc ℚ Ω l σ := (cyc_eq_map_cycZ ℚ Ω l σ).symm
  simp only [eps, e, cyc_eq_one_of_mem_Ine hl h hσ, Units.val_one]

theorem val_dt (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem dt_inv_eq (W : R2 Ω l) (h : dt W ^ 2 = 1) : (dt W)⁻¹ = dt W := by
  rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h

theorem mat_dual1_eq (W : R2 Ω l) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (((dt W)⁻¹ s : (Qbar l)ˣ) : Qbar l)) • mat W s := by
  simp [mat, dual1, tw_val, eps]

theorem mat_dual1_eq' (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  rw [mat_dual1_eq, dt_inv_eq W h, val_dt]

theorem continuous_mat (W : R2 Ω l) (hW : Continuous W) : Continuous fun s => mat W s :=
  Units.continuous_val.comp hW

theorem continuous_mat_dual1 (W : R2 Ω l) (hW : Continuous W) (h : dt W ^ 2 = 1) :
    Continuous fun s => mat (dual1 W) s := by
  simp only [mat_dual1_eq' W h]
  exact (continuous_eps.mul (continuous_mat W hW).matrix_det).smul (continuous_mat W hW)

theorem om_add_left (x x' y : Fin 2 → Qbar l) : om (x + x') y = om x y + om x' y := by
  simp only [om, Pi.add_apply]; ring

theorem om_add_right (x y y' : Fin 2 → Qbar l) : om x (y + y') = om x y + om x y' := by
  simp only [om, Pi.add_apply]; ring

theorem om_mulVec_smul (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (c : Qbar l) (x y : Fin 2 → Qbar l) :
    om (M *ᵥ x) ((c • M) *ᵥ y) = c * M.det * om x y := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
  ring

theorem om_pair (W : R2 Ω l) (s : G ℚ Ω) (x y : Fin 2 → Qbar l) :
    om (mat W s *ᵥ x) (mat (dual1 W) s *ᵥ y) = eps l s * om x y := by
  rw [mat_dual1_eq, om_mulVec_smul, mul_assoc (eps l s), ← val_dt, ← Units.val_mul,
    show (dt W)⁻¹ s * dt W s = 1 by simp, Units.val_one, mul_one]

theorem cup_cocycle (W : R2 Ω l) {a b : G ℚ Ω → Fin 2 → Qbar l} (ha : a ∈ Z1 (Loc.colRep W))
    (hb : b ∈ Z1 (Loc.colRep (dual1 W))) (r s t : G ℚ Ω) :
    eps l r * cup W a b s t + cup W a b r (s * t) = cup W a b (r * s) t + cup W a b r s := by
  simp only [cup]
  rw [cocycle_mulVec hb s t, cocycle_mulVec ha r s, mat_mul' (dual1 W) r s, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_add, om_add_right, om_add_left, om_pair]
  ring

theorem cg_refl (n : ℕ) (x : Qbar l) : Cg n x x := by
  simp [Cg]

theorem vanish_NS [IsAlgClosure ℚ Ω] {S : Finset Pl} (hS : ContainsAbove S l) (V : R2 Ω l)
    (hV : Continuous fun s => mat V s) {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep V))
    (hu : Unr V z) (hI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ V.ker) :
    ∀ α ∈ NS Ω (S : Set Pl), mat V α = 1 ∧ z α = 0 := by
  have z1 : z 1 = 0 := by
    have := cocycle_mulVec hz 1 1
    rw [mul_one, mat_one', Matrix.one_mulVec] at this
    simpa using this
  let K : Subgroup (G ℚ Ω) :=
    { carrier := {g | mat V g = 1 ∧ z g = 0}
      one_mem' := ⟨mat_one' V, z1⟩
      mul_mem' := by
        rintro g h ⟨h1, h2⟩ ⟨h3, h4⟩
        exact ⟨by rw [mat_mul', h1, h3, mul_one], by rw [cocycle_mulVec hz, h2, h4, Matrix.mulVec_zero, add_zero]⟩
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        have hm : mat V g⁻¹ * mat V g = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
        rw [h1, mul_one] at hm
        refine ⟨hm, ?_⟩
        have := cocycle_mulVec hz g⁻¹ g
        rw [inv_mul_cancel, z1, h2, Matrix.mulVec_zero, add_zero] at this
        exact this.symm }
  have hK : K.Normal := ⟨fun g ⟨h1, h2⟩ x => by
    have hm : mat V (x * g * x⁻¹) = 1 := by
      rw [mat_mul', mat_mul', h1, mul_one, ← mat_mul', mul_inv_cancel, mat_one']
    refine ⟨hm, ?_⟩
    rw [cob_conj hz x g 0 (by rw [h2, Matrix.mulVec_zero, sub_zero]), hm, Matrix.one_mulVec, sub_self]⟩
  have hcl : IsClosed (K : Set (G ℚ Ω)) :=
    (isClosed_eq hV continuous_const).inter (isClosed_eq hz.1 continuous_const)
  intro α hα
  have hle : NS Ω (S : Set Pl) ≤ K := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    have hv' : v ∉ S := by simpa using hv
    have hτ' : τ ∈ Ine (F := ℚ) A := hτ
    have hm : mat V τ = 1 := by
      have h1 : V τ = 1 := hI v hv' A hA hτ'
      simp [mat, h1]
    refine ⟨hm, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv' (hS v h)
    obtain ⟨B0, hB0, x, hx⟩ := hu v hl
    obtain ⟨x', hx'⟩ := (place_indep l Ω V z hz v B0 A hB0 hA).1 ⟨x, hx⟩
    rw [hx' τ hτ', hm, Matrix.one_mulVec, sub_self]
  exact hle hα

theorem cupProductDualTwist_isTwoCocycle_unramified_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ)
    (S : Finset Pl) (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) →
    dt W ^ 2 = 1 → ContainsAbove S l →
    (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) →
    a ∈ Z1 (Loc.colRep W) → b ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, a s i ∈ c.O) → (∀ s i, b s i ∈ c.O) →
    Unr W a → Unr (dual1 W) b → Coc2 c n S (cup W a b) := by
  intro l _ Ω _ _ _ c n S W a b hW hWi hdt hS hI ha hb hai hbi hua hub
  have hWc := continuous_mat W hW
  have hDc := continuous_mat_dual1 W hW hdt
  have hDI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
    intro w hw B hB σ hσ
    have h1 : W σ = 1 := hI w hw B hB hσ
    have hm : mat W σ = 1 := by simp [mat, h1]
    have he : eps l σ = 1 := eps_eq_one_of_mem_Ine (fun h => hw (hS w h)) hB hσ
    show dual1 W σ = 1
    apply Units.ext
    show mat (dual1 W) σ = 1
    rw [mat_dual1_eq' W hdt, hm, he, Matrix.det_one, mul_one, one_smul]
  have vW := vanish_NS hS W hWc ha hua hI
  have vD := vanish_NS hS (dual1 W) hDc hb hub hDI
  have hker : (toGS Ω (S : Set Pl)).ker = NS Ω (S : Set Pl) := QuotientGroup.ker_mk' _
  have hD : ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
    intro s i j
    rw [mat_dual1_eq' W hdt, Matrix.smul_apply, smul_eq_mul, Matrix.det_fin_two]
    exact c.O.mul_mem (c.O.mul_mem (eps_mem c s)
      (c.O.sub_mem (c.O.mul_mem (hWi s 0 0) (hWi s 1 1)) (c.O.mul_mem (hWi s 0 1) (hWi s 1 0)))) (hWi s i j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha' : Continuous a := ha.1
    have hb' : Continuous b := hb.1
    have hA : ∀ i, Continuous fun p : G ℚ Ω × G ℚ Ω => a p.1 i :=
      fun i => (continuous_apply i).comp (ha'.comp continuous_fst)
    have hB : ∀ i, Continuous fun p : G ℚ Ω × G ℚ Ω => b p.2 i :=
      fun i => (continuous_apply i).comp (hb'.comp continuous_snd)
    have hM : ∀ i j, Continuous fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp (hDc.comp continuous_fst))
    simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact ((hA 0).mul (((hM 1 0).mul (hB 0)).add ((hM 1 1).mul (hB 1)))).sub
      ((hA 1).mul (((hM 0 0).mul (hB 0)).add ((hM 0 1).mul (hB 1))))
  · intro s t
    simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.sub_mem
      (c.O.mul_mem (hai s 0) (c.O.add_mem (c.O.mul_mem (hD s 1 0) (hbi t 0)) (c.O.mul_mem (hD s 1 1) (hbi t 1))))
      (c.O.mul_mem (hai s 1) (c.O.add_mem (c.O.mul_mem (hD s 0 0) (hbi t 0)) (c.O.mul_mem (hD s 0 1) (hbi t 1))))
  · intro r s t
    rw [cup_cocycle W ha hb r s t]
    exact cg_refl n _
  · intro s t α hα β hβ
    rw [hker] at hα hβ
    have e : cup W a b (s * α) (t * β) = cup W a b s t := by
      simp only [cup]
      rw [cocycle_mulVec ha s α, (vW α hα).2, Matrix.mulVec_zero, add_zero, cocycle_mulVec hb t β, (vD β hβ).2,
        Matrix.mulVec_zero, add_zero, mat_mul', (vD α hα).1, mul_one]
    rw [e]
    exact cg_refl n _

end GlobalTheory.Ord2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramifiedStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → ContainsAbove S l → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → a ∈ Z1 (Loc.colRep W) → b ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, a s i ∈ c.O) → (∀ s i, b s i ∈ c.O) → Unr W a → Unr (dual1 W) b → Coc2 c n S (cup W a b) := by
  first | exact @GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | exact GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt | (intros; apply GlobalTheory.Ord2.cupProductDualTwist_isTwoCocycle_unramified_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecCauchy
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA

theorem spec_cauchy : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (Y : ∀ r : ℕ, Γ → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l), (∀ r s x i, ‖Y r s x i‖ ≤ 1) → (∀ r x, ‖η r x‖ ≤ 1) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖η (r + 1) x - η r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ r s i, ‖spec (η (r + 1)) (Y (r + 1)) s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l _ Γ _ Y η hY hη hYp hηc r s i
  set red := (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) with hred
  have hpush : spec (η r) (Y r) s i = ∑ x', η r (red x') * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hYp r s]
    simp only [push, Finset.sum_apply, Finset.mul_sum]
    rw [← Finset.sum_fiberwise (Finset.univ) red (fun x' => η r (red x') * Y (r + 1) s x' i)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' hx' => ?_
    rw [(Finset.mem_filter.mp hx').2]
  have hspec : spec (η (r + 1)) (Y (r + 1)) s i = ∑ x', η (r + 1) x' * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpush, hspec, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x' _ => ?_
  rw [← sub_mul, norm_mul]
  calc ‖η (r + 1) x' - η r (red x')‖ * ‖Y (r + 1) s x' i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ * 1 :=
        mul_le_mul (hηc r x') (hY _ _ _ _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

end GlobalTheory.KA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  intro l _ Ω _ _ _ e S A W hW a ha
  set T : Subgroup (G ℚ Ω) := W.ker ⊓ (cycZ ℚ Ω l).ker with hT
  have hTc : IsClosed (T : Set (G ℚ Ω)) := by
    have h1 : IsClosed (W.ker : Set (G ℚ Ω)) := isClosed_singleton.preimage hW.cont
    have h2 : IsClosed ((cycZ ℚ Ω l).ker : Set (G ℚ Ω)) := isClosed_singleton.preimage (continuous_cycZ ℚ Ω l)
    exact h1.inter h2
  have hNS : NS Ω (S : Set Pl) ≤ T := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hTc
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    refine ⟨hW.unr v hv B hB hτ, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hW.above v h)
    exact GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hτ
  have haT : a ∈ T := hNS ((QuotientGroup.eq_one_iff _).mp ha)
  have hWa : W a = 1 := haT.1
  have hca : cycZ ℚ Ω l a = 1 := haT.2
  have hcb : cycBar ℚ Ω l a = 1 := by simp [cycBar, hca]
  have hdt : dt W a = 1 := by simp [dt, hWa]
  apply Units.ext
  rw [dual1, tw_val]
  simp [hcb, hdt, hWa]

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramifiedQuotient : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro l _ Ω _ _ _ e S A W hW c hc s i j

  have hdet : (mat W s).det ∈ c.O := by
    let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W s i j, hc s i j⟩
    have hM : M.map c.O.val = mat W s := by ext i j; rfl
    have h := RingHom.map_det (SubringClass.subtype c.O) M
    rw [RingHom.mapMatrix_apply] at h
    rw [← hM]
    have e1 : (M.map c.O.val) = M.map (SubringClass.subtype c.O) := rfl
    rw [e1, ← h]
    exact (M.det).2

  have hinv : (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
    have h2 : dt W s ^ 2 = 1 := by
      have := congrArg (fun f => f s) hW.det2
      simpa using this
    have : (dt W s)⁻¹ = dt W s := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
    rw [this]; rfl
  have hcyc : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) ∈ c.O := by
    show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O
    exact c.O.algebraMap_mem _
  have hval : mat (dual1 W) s i j = ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s i j := by
    simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply]
  rw [hval, hinv]
  exact c.O.mul_mem (c.O.mul_mem hcyc hdet) (hc s i j)

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNormaStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.DualCont

theorem cyc_cont' {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem units_cont {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

theorem continuous_galoisRepRankTwoTateDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → Continuous (dual1 W) := by
  intro l _ Ω _ _ _ e S A W hN
  have hW : Continuous fun s => ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hN.cont
  have hd : Continuous (dt W) := by
    apply units_cont
    show Continuous fun s => (Matrix.GeneralLinearGroup.det (W s) : Qbar l)
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hW.matrix_det
  have hc := cyc_cont' (Ω := Ω) l
  have hχ : Continuous (cycBar ℚ Ω l * (dt W)⁻¹) := by
    show Continuous fun s => cycBar ℚ Ω l s * ((dt W) s)⁻¹
    exact hc.mul hd.inv
  apply units_cont
  show Continuous fun s => ((tw W (cycBar ℚ Ω l * (dt W)⁻¹) s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
  simp only [tw_val]
  exact (Units.continuous_val.comp hχ).smul hW

end GlobalTheory.Ord2.DualCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNormStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_galoisRepRankTwoTateDual_of_ordinaryNormalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → Continuous (dual1 W) := by
  first | exact @GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual | exact GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual | (intros; apply GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual <;> assumption)
end
end
