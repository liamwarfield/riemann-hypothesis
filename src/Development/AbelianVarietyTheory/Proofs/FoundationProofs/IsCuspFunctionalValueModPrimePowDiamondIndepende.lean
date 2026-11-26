module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ

theorem mul_inv_mem_Gam_of_isDiam {N l d : ℕ} {s t : SL(2, ℤ)} (hs : IsDiam N l d s) (ht : IsDiam N l d t) :
    s * t⁻¹ ∈ Gam N l := by
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨ht0, htd⟩ := ht
  rw [Subgroup.mem_inf] at hs0 ht0
  refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ hs0.2 (Subgroup.inv_mem _ ht0.2)⟩
  have hsN := CongruenceSubgroup.Gamma0_mem.1 hs0.1
  have htN := CongruenceSubgroup.Gamma0_mem.1 ht0.1
  have ds := s.det_coe
  have dt := t.det_coe
  rw [Matrix.det_fin_two] at ds dt
  have ds' : ((s 0 0 * s 1 1 - s 0 1 * s 1 0 : ℤ) : ZMod N) = 1 := by rw [ds]; simp
  have dt' : ((t 0 0 * t 1 1 - t 0 1 * t 1 0 : ℤ) : ZMod N) = 1 := by rw [dt]; simp
  push_cast at ds' dt'
  simp only [en] at hsd htd
  rw [CongruenceSubgroup.Gamma1_mem]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · linear_combination ds' + (s 0 0 : ZMod N) * (htd - hsd) + (s 0 1 : ZMod N) * hsN - (s 0 1 : ZMod N) * htN
  · linear_combination dt' + (t 0 0 : ZMod N) * (hsd - htd) + (t 0 1 : ZMod N) * htN - (t 0 1 : ZMod N) * hsN
  · linear_combination (t 1 1 : ZMod N) * hsN - (s 1 1 : ZMod N) * htN

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.act_eq_of_mem_B (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem Tower.act_isDiam_eq (X : Tower Ω ε) {N l w d : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    {s : SL(2, ℤ)} (hs : IsDiam N l d s) :
    X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b := by
  have ht : IsDiam N l d (sgD N l d) := Classical.epsilon_spec ⟨s, hs⟩
  have hγ := mul_inv_mem_Gam_of_isDiam hs ht
  have e : s = (s * (sgD N l d)⁻¹) * sgD N l d := by group
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  rw [e, Matrix.SpecialLinearGroup.coe_mul, ← Tower.act_act Ω ε X l _ _ (hpos _) (hpos _) b,
    X.act_eq_of_mem_B hb hγ]

theorem isThB_act_isDiam_iff : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ) (b : X.Fn l), b ∈ X.B N l w →
    ∀ s : SL(2, ℤ), IsDiam N l d s → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b) φ ↔
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  intro Ω _ _ _ ε X A N l _ n w d b hb s hs φ
  rw [X.act_isDiam_eq hb hs]

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndependeStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFunctionalValueModPrimePow_diamond_independent : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ) (b : X.Fn l), b ∈ X.B N l w → ∀ s : SL(2, ℤ), IsDiam N l d s → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b) φ ↔ IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  first | exact @GlobalTheory.KZ.isThB_act_isDiam_iff | exact GlobalTheory.KZ.isThB_act_isDiam_iff | (intros; apply GlobalTheory.KZ.isThB_act_isDiam_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnit
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem Tower.sum_act_upper_mul_unit {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (c : X.Fn l) (hc : ∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) (q : ℕ) (e : ℤ) (hq : 0 < q)
    (he : IsCoprime e (q : ℤ)) :
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c =
      ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set f : ℤ → X.Fn l := fun r => X.act l !![1, r; 0, (q : ℤ)] c with hf
  have step : ∀ x : ℤ, X.act l !![1, x; 0, (q : ℤ)] c = f (x % q) := by
    intro x
    have hm : !![1, x; 0, (q : ℤ)] = !![(1 : ℤ), x / q; 0, 1] * !![1, x % q; 0, (q : ℤ)] := by
      have := Int.emod_add_mul_ediv x q
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
    rw [hm, ← Tower.act_act Ω ε X l _ _ (by simp [Matrix.det_fin_two]) (by simp [Matrix.det_fin_two]; exact hq), hc]
  let g : ℕ → ℕ := fun j => (((j : ℤ) * e) % q).toNat
  have hg : ∀ j, ((g j : ℕ) : ℤ) = ((j : ℤ) * e) % q := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq'.ne')
  have hgr : ∀ j, g j < q := fun j => by
    have h1 := Int.emod_lt_of_pos ((j : ℤ) * e) hq'
    have h2 := hg j
    omega
  have hinj : Set.InjOn g (Finset.range q) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h : ((i : ℤ) * e) % q = ((j : ℤ) * e) % q := by rw [← hg, ← hg, hij]
    have hd : (q : ℤ) ∣ ((j : ℤ) - i) * e := by
      rw [sub_mul]; exact (Int.ModEq.dvd h)
    have hd' : (q : ℤ) ∣ (j : ℤ) - i := he.symm.dvd_of_dvd_mul_right hd
    have h0 := Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt]; constructor <;> omega)
    omega
  have himg : (Finset.range q).image g = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_image] at hr; obtain ⟨j, _, rfl⟩ := hr; exact Finset.mem_range.2 (hgr j)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c
      = ∑ j ∈ Finset.range q, f ((g j : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [step, hg]
    _ = ∑ r ∈ (Finset.range q).image g, f (r : ℤ) := (Finset.sum_image (f := fun r : ℕ => f (r : ℤ)) hinj).symm
    _ = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by rw [himg]

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnitStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Fn l), (∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) → ∀ (q : ℕ) (e : ℤ), 0 < q → IsCoprime e (q : ℤ) → ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  first | exact @GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | exact GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | (intros; apply GlobalTheory.KZ.Tower.sum_act_upper_mul_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralLimitCompatibleModPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralLimitCompatibleModPrimePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pow_anti {m n : ℕ} (h : n ≤ m) :
    ‖((l : ℕ) : Qbar l) ^ m‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_natCast_l_lt_one.le h

theorem isCompact_coef (c : Coef l) : IsCompact (c.O : Set (Qbar l)) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  let f : (Fin k → ℤ_[l]) → Qbar l :=
    fun v => ∑ i, algebraMap ℤ_[l] (Qbar l) (v i) * (s i : Qbar l)
  have hcont : Continuous f := by
    have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
      have : ⇑(algebraMap ℤ_[l] (Qbar l)) = fun a : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) := by
        funext a; exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) a
      rw [this]
      exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact continuous_finsetSum _ fun i _ => (ha.comp (continuous_apply i)).mul continuous_const
  have heq : (c.O : Set (Qbar l)) = Set.range f := by
    ext x
    constructor
    · intro hx
      have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (Set.range s) := by rw [hs]; trivial
      obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hmem
      refine ⟨v, ?_⟩
      have := congrArg (fun y : c.O => (y : Qbar l)) hv
      simp only [AddSubmonoidClass.coe_finsetSum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.smul_def]
      rfl
    · rintro ⟨v, rfl⟩
      exact c.O.sum_mem fun i _ => c.O.mul_mem (c.O.algebraMap_mem _) (s i).2
  rw [heq]
  exact isCompact_range hcont

theorem cg_of_le {a : ℕ → Qbar l} (h : ∀ n, Cg n (a (n + 1)) (a n)) {n m : ℕ} (hnm : n ≤ m) :
    Cg n (a m) (a n) := by
  induction m, hnm using Nat.le_induction with
  | base => unfold Cg; simp
  | succ m hm ih =>
    have h1 : Cg n (a (m + 1)) (a m) := by
      unfold Cg at *; exact (h m).trans (norm_l_pow_anti hm)
    exact cg_trans h1 ih

theorem exists_limit_coef : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (X : Type) (a : ℕ → X → Qbar l),
    (∀ n x, a n x ∈ c.O) → (∀ n x, Cg n (a (n + 1) x) (a n x)) →
    ∃ z : X → Qbar l, (∀ x, z x ∈ c.O) ∧ ∀ n x, Cg n (z x) (a n x) := by
  intro l _ c X a hO hC
  have key : ∀ x, ∃ y ∈ (c.O : Set (Qbar l)), ∀ n, Cg n y (a n x) := by
    intro x
    have hle : ∀ n m, n ≤ m → ‖a m x - a n x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
      fun n m h => cg_of_le (a := fun k => a k x) (fun k => hC k x) h
    have hcs : CauchySeq (fun m => a m x) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists_forall_of_atTop
      refine ⟨N, fun m hm => ?_⟩
      rw [dist_eq_norm]
      exact (hle N m hm).trans_lt (hN N le_rfl)
    obtain ⟨y, hy, hlim⟩ := cauchySeq_tendsto_of_isComplete (isCompact_coef c).isComplete
      (fun m => hO m x) hcs
    refine ⟨y, hy, fun n => ?_⟩
    unfold Cg
    have ht : Filter.Tendsto (fun m => ‖a m x - a n x‖) Filter.atTop (nhds ‖y - a n x‖) :=
      (hlim.sub_const _).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨n, fun m hm => hle n m hm⟩)
  choose z hz using key
  exact ⟨z, fun x => (hz x).1, fun n x => (hz x).2 n⟩

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralLimitCompatibleModPrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_limit_compatible_modPrimePow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (X : Type) (a : ℕ → X → Qbar l), (∀ n x, a n x ∈ c.O) → (∀ n x, Cg n (a (n + 1) x) (a n x)) → ∃ z : X → Qbar l, (∀ x, z x ∈ c.O) ∧ ∀ n x, Cg n (z x) (a n x) := by
  first | exact @GlobalTheory.Ord2.exists_limit_coef | exact GlobalTheory.Ord2.exists_limit_coef | (intros; apply GlobalTheory.Ord2.exists_limit_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeAction
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeAction
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.GamComm

theorem intCast_eq_of_dvd {K M : ℕ} (hK : K ∣ M) {x y : ℤ} (h : (x : ZMod M) = y) : (x : ZMod K) = y := by
  simpa only [map_intCast] using congrArg (ZMod.castHom hK (ZMod K)) h

theorem gamma_le_of_dvd {K M : ℕ} (hK : K ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h1)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h2)
  · simpa using intCast_eq_of_dvd hK (y := 0) (by simpa using h3)
  · simpa using intCast_eq_of_dvd hK (y := 1) (by simpa using h4)

theorem mul_inv_mem_Gam (N l : ℕ) (g δ : SL(2, ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h00 : (en δ 0 0 : ZMod N) = en g 0 0) (h11 : (en δ 1 1 : ZMod N) = en g 1 1) : g * δ⁻¹ ∈ Gam N l := by
  refine Subgroup.mem_inf.2 ⟨?_, mul_mem (Subgroup.mem_inf.1 hg).2 (inv_mem (Subgroup.mem_inf.1 hδ).2)⟩
  have a1 : (en g 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hg).1
  have a2 : (en δ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hδ).1
  have hdet : (en δ 0 0 : ZMod N) * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod N) h
    simpa [en] using this
  have e00 : en (g * δ⁻¹) 0 0 = en g 0 0 * en δ 1 1 - en g 0 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e10 : en (g * δ⁻¹) 1 0 = en g 1 0 * en δ 1 1 - en g 1 1 * en δ 1 0 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have e11 : en (g * δ⁻¹) 1 1 = en g 1 1 * en δ 0 0 - en g 1 0 * en δ 0 1 := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩
  · change ((en (g * δ⁻¹) 0 0 : ℤ) : ZMod N) = 1
    rw [e00]; push_cast
    linear_combination hdet - (en δ 1 1 : ZMod N) * h00 + ((en δ 0 1 : ZMod N) - en g 0 1) * a2
  · change ((en (g * δ⁻¹) 1 1 : ℤ) : ZMod N) = 1
    rw [e11]; push_cast
    linear_combination hdet - (en δ 0 0 : ZMod N) * h11 + (en δ 0 1 : ZMod N) * a2 - (en δ 0 1 : ZMod N) * a1
  · change ((en (g * δ⁻¹) 1 0 : ℤ) : ZMod N) = 0
    rw [e10]; push_cast
    rw [a1, a2]; ring

theorem act_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ _ ε X N l w _ hN b hb δ hδ s
  funext u
  refine AdicCompletion.ext fun n => ?_
  have hcls := GlobalTheory.KZ.H3.cls_props Ω ε X l n
  have hF := hcls.2.2.2.2.2.1
  obtain ⟨f, hf⟩ := hcls.1 (AdicCompletion.eval (idl l) (X.Kl l) n
    (b ![(mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0,
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (mZl l (δ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))
  obtain ⟨M₀, hM₀, hlev⟩ := X.level (f : X.K)
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨M, hM, hM0, hMN, hMl, hMn⟩ : ∃ M : ℕ, 0 < M ∧ M₀ ∣ M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M :=
    ⟨M₀ * N * l * l ^ n, by positivity, ⟨N * l * l ^ n, by ring⟩, ⟨M₀ * l * l ^ n, by ring⟩,
      ⟨M₀ * N * l ^ n, by ring⟩, ⟨M₀ * N * l, by ring⟩⟩
  obtain ⟨ζ, hζ, i, hi, hs, hχ⟩ := GlobalTheory.exists_primitiveRoot_pow_cyclotomicCharacter l n M hM hMn s
  obtain ⟨g, h00, h01, h10, h11⟩ := GlobalTheory.exists_sl2_conj_diag_zmod M i hi δ
  have hc : (en δ 0 0 : ZMod M) = en g 0 0 ∧ (en δ 0 1 : ZMod M) = ((i : ℤ) : ZMod M) * en g 0 1 ∧
      ((i : ℤ) : ZMod M) * en δ 1 0 = en g 1 0 ∧ (en δ 1 1 : ZMod M) = en g 1 1 :=
    ⟨h00, by simpa only [Int.cast_natCast] using h01, by simpa only [Int.cast_natCast] using h10, h11⟩
  have hrec := X.recip M f hM (fun γ hγ => hlev γ (gamma_le_of_dvd hM0 hγ)) ζ hζ s i
    (by rw [zpow_natCast, hs]) g δ hc
  have h10' : (((i : ℤ) * en δ 1 0 : ℤ) : ZMod M) = en g 1 0 := by push_cast; exact h10
  have hg0 : ∀ K : ℕ, K ∣ M → δ ∈ CongruenceSubgroup.Gamma0 K → g ∈ CongruenceSubgroup.Gamma0 K := fun K hK h => by
    have a : (en δ 1 0 : ZMod K) = 0 := CongruenceSubgroup.Gamma0_mem.1 h
    refine CongruenceSubgroup.Gamma0_mem.2 ((intCast_eq_of_dvd hK h10').symm.trans ?_)
    rw [Int.cast_mul, a, mul_zero]
  have hgam : g * δ⁻¹ ∈ Gam N l :=
    mul_inv_mem_Gam N l g δ
      (Subgroup.mem_inf.2 ⟨hg0 N hMN (Subgroup.mem_inf.1 hδ).1, hg0 l hMl (Subgroup.mem_inf.1 hδ).2⟩) hδ
      (intCast_eq_of_dvd hMN h00) (intCast_eq_of_dvd hMN h11)
  have hact : X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (g : Matrix (Fin 2) (Fin 2) ℤ) b := by
    have e : (g : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [e, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos), hb.2 _ hgam]
  have hpol := StabGal.eval_Pol_congr X l w b hb.1 n _ _
    (StabGal.twist_congr l n M hMn δ g i (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) hc
      (by simpa only [Int.cast_natCast] using hχ) u)
  rw [hact]
  have hL := hF (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hF (X.gal s) _ _ hf.symm)
  have hR := hF (X.gal s) _ _ (hF (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (hpol.symm.trans hf.symm))
  refine hL.trans (Eq.trans ?_ hR.symm)
  congr 1
  apply Units.ext
  change X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ)) (X.gal s f) = X.gal s (X.sl (toGQ (g : Matrix (Fin 2) (Fin 2) ℤ)) f)
  rw [StabGal.toGQ_SL, StabGal.toGQ_SL, hrec]

end GlobalTheory.KZ.GamComm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeActionStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_commutes_hecke_action : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.GamComm.act_galB_comm | exact GlobalTheory.KZ.GamComm.act_galB_comm | (intros; apply GlobalTheory.KZ.GamComm.act_galB_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocit
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GammaZeroComm

theorem act_eq_self_of_mem_B {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w) {h : SL(2, ℤ)} (hh : h ∈ Gam N l) :
    X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 h hh
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem eval_kmap_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ : X.K ≃+* X.K) (n : ℕ) {x y : X.Khat l} (h : x - y ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine Submodule.smul_induction_on h (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ m))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add (f := _), map_add (f := _), ha, hb, add_zero]

theorem exists_twist (M : ℕ) (e e' : ℤ) (he : (e : ZMod M) * e' = 1) (γ : SL(2, ℤ)) :
    ∃ γ₁ : SL(2, ℤ), (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1 := by
  have hdet : (en γ 0 0 : ZMod M) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod M) this
    push_cast at h2
    exact h2
  obtain ⟨γ₁, hγ₁⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M
    ⟨!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet - (en γ 0 1 : ZMod M) * en γ 1 0 * he⟩
  have hent : ∀ i j, (en γ₁ i j : ZMod M) =
      (!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1] : Matrix (Fin 2) (Fin 2) (ZMod M)) i j :=
    fun i j => congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => g.1 i j) hγ₁
  refine ⟨γ₁, ?_, ?_, ?_, ?_⟩
  · rw [hent]; rfl
  · rw [hent]
    show _ = (e : ZMod M) * (e' * en γ 0 1)
    rw [← mul_assoc, he, one_mul]
  · rw [hent]; rfl
  · rw [hent]; rfl

theorem cong_of_dvd {M K : ℕ} (hK : K ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    (en γ 0 0 : ZMod K) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod K) = e * en γ₁ 0 1 ∧
      (e : ZMod K) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod K) = en γ₁ 1 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := h
  have e00 := congrArg (ZMod.castHom hK (ZMod K)) h00
  have e01 := congrArg (ZMod.castHom hK (ZMod K)) h01
  have e10 := congrArg (ZMod.castHom hK (ZMod K)) h10
  have e11 := congrArg (ZMod.castHom hK (ZMod K)) h11
  simp only [map_mul, map_intCast] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem twist_mul_inv_mem {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    γ₁ * γ⁻¹ ∈ Gam N l := by
  obtain ⟨a00, -, a10, a11⟩ := cong_of_dvd hN h
  obtain ⟨-, -, b10, -⟩ := cong_of_dvd hl h
  have cN : (en γ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.1
  have cl : (en γ 1 0 : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.2
  have hdet : (en γ 0 0 : ZMod N) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod N) this
    push_cast at h2
    exact h2
  have m00 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 0 0 = en γ₁ 0 0 * en γ 1 1 - en γ₁ 0 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m10 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 0 = en γ₁ 1 0 * en γ 1 1 - en γ₁ 1 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m11 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 1 = en γ₁ 1 1 * en γ 0 0 - en γ₁ 1 0 * en γ 0 1 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  rw [cN] at a10 hdet
  rw [cl] at b10
  refine ⟨(CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, CongruenceSubgroup.Gamma0_mem.2 ?_⟩
  · rw [m00]; push_cast; rw [← a00, cN]; linear_combination hdet
  · rw [m11]; push_cast; rw [← a11, ← a10]; linear_combination hdet
  · rw [m10]; push_cast; rw [← a10, cN]; ring
  · rw [m10]; push_cast; rw [← b10, cl]; ring

theorem twist_vec {l n M : ℕ} [Fact l.Prime] (hM : l ^ n ∣ M) {e : ℤ} {χ : ℤ_[l]} (hχ : (e : ℤ_[l]) - χ ∈ (idl l) ^ n)
    {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) (u : Fin 2 → ℤ_[l]) (i : Fin 2) :
    (![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] :
      Fin 2 → ℤ_[l]) i - (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i ∈ (idl l) ^ n := by
  obtain ⟨e00, e01, e10, e11⟩ := cong_of_dvd hM h
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hχ ⊢
  rw [map_intCast] at hχ
  simp only [en] at e00 e01 e10 e11
  rw [hχ] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add (f := _), map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem galB_act_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) = X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) := by
  intro Ω _ _ _ ε X _ _ N l w _ _ hN _ _ γ hγ s b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  obtain ⟨M0, hM0, hlev⟩ := X.eval_kmap_levelRed l
    (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]) n
  obtain ⟨M, hM, hNM, hlM, hlnM, hM0M⟩ : ∃ M : ℕ, 0 < M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M ∧ M0 ∣ M :=
    ⟨N * l * l ^ n * M0, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hl.pos) (pow_pos hl.pos n)) hM0,
      ⟨l * l ^ n * M0, by ring⟩, ⟨N * l ^ n * M0, by ring⟩, ⟨N * l * M0, by ring⟩, ⟨N * l * l ^ n, by ring⟩⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  obtain ⟨e, he, heχ⟩ := exists_int_exponent_cyclotomic l s n M hM hlnM
  obtain ⟨e', he', -⟩ := exists_int_exponent_cyclotomic l s.symm n M hM hlnM
  have hee : (e : ZMod M) * e' = 1 := by
    have h1 : ζ ^ (e * e') = ζ := by
      rw [_root_.zpow_mul, ← he ζ hζ, ← map_zpow₀, ← he' ζ hζ, AlgEquiv.apply_symm_apply]
    have h0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
    have h2 : ζ ^ (e * e' - 1) = 1 := by rw [zpow_sub_one₀ h0, h1, mul_inv_cancel₀ h0]
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (e * e') M).2 ((hζ.zpow_eq_one_iff_dvd _).1 h2)
    push_cast at h3
    exact h3.symm
  obtain ⟨γ₁, hc⟩ := exists_twist M e e' hee γ
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hact : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) b := by
    conv_lhs => rw [← act_eq_self_of_mem_B X N l w hb (twist_mul_inv_mem hNM hlM hγ hc)]
    rw [Tower.act_act Ω ε X l _ _ (hpos _) (hpos _), ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  rw [hact]
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s)
      (X.kmap l (X.sl (toGQ (γ₁ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1])))) =
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s)
        (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap, Betti.toGQ_sl, Betti.toGQ_sl,
    ← eval_kmap_congr X l _ n (X.B_sub_mem N l w b hb n _ _ (twist_vec hlnM heχ hc u))]
  refine hlev _ _ fun f hf => ?_
  exact X.recip M f hM (fun g hg => hf g (LevelRed.gamma_le_of_dvd hM0M hg)) ζ hζ s e (he ζ hζ) γ₁ γ hc

end GlobalTheory.KZ.GammaZeroComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocitStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) = X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.GammaZeroComm.galB_act_comm | exact GlobalTheory.KZ.GammaZeroComm.galB_act_comm | (intros; apply GlobalTheory.KZ.GammaZeroComm.galB_act_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FgInertiaCocyclesModCoboundariesCoefRing
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FgInertiaCocyclesModCoboundariesCoefRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.InertCoh

theorem fg_map_mkQ_of_ev {R M N : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Z B Y : Submodule R M) (ev : M →ₗ[R] N) (L : Submodule R N) (hL : L.FG)
    (h1 : ∀ z ∈ Z, ∃ y ∈ Y, z - y ∈ B) (h2 : ∀ y ∈ Y, ev y ∈ L) (h3 : ∀ y ∈ Y, ev y = 0 → y ∈ B) :
    (Z.map B.mkQ).FG := by
  let f : Y →ₗ[R] N := ev ∘ₗ Y.subtype
  let g : Y →ₗ[R] (M ⧸ B) := B.mkQ ∘ₗ Y.subtype
  have hf : (LinearMap.range f).FG := by
    refine hL.of_le ?_
    rintro _ ⟨y, rfl⟩
    exact h2 y y.2
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro y hy
    exact (Submodule.Quotient.mk_eq_zero B).2 (h3 y y.2 hy)
  haveI : Module.Finite R (LinearMap.range f) := Module.Finite.iff_fg.2 hf
  haveI : Module.Finite R (Y ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  have hg : (LinearMap.range g).FG := by
    rw [← Submodule.range_liftQ (LinearMap.ker f) g hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine hg.of_le ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hzy⟩ := h1 z hz
  exact ⟨⟨y, hy⟩, ((Submodule.Quotient.eq B).2 hzy).symm⟩

theorem cobound_mem_coc {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {W : R2 Ω l} {c : Coef l}
    (I : Subgroup (G ℚ Ω)) (hW : Continuous W) (hO : ∀ s i j, mat W s i j ∈ c.O) {v : Fin 2 → Qbar l}
    (hv : ∀ i, v i ∈ c.O) : (fun s => mat W s *ᵥ v - v) ∈ coc W c I := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hW
  refine mem_coc.2 ⟨fun i => ?_, fun s i => ?_, fun s _ t _ => ?_⟩
  · exact (continuous_apply i).comp ((hm.matrix_mulVec continuous_const).sub continuous_const)
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    exact c.O.sub_mem (c.O.sum_mem fun j _ => c.O.mul_mem (hO s i j) (hv j)) (hv i)
  · simp only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel

theorem fg_coc_mod_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  intro l _ Ω _ _ W c I P γ hW hO hP hγ
  haveI := c.dvr
  haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  let Y : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) :=
    coc W c I ⊓ ⨅ σ ∈ P, LinearMap.ker (LinearMap.proj σ : (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (Fin 2 → Qbar l))
  have hY : ∀ z, z ∈ Y ↔ z ∈ coc W c I ∧ ∀ σ ∈ P, z σ = 0 := by
    intro z
    simp [Y, Submodule.mem_iInf]
  let ι : (Fin 2 → c.O) →ₗ[c.O] (Fin 2 → Qbar l) := (Algebra.linearMap c.O (Qbar l)).compLeft (Fin 2)
  have hL : (LinearMap.range ι).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine fg_map_mkQ_of_ev _ _ Y (LinearMap.proj γ) _ hL ?_ ?_ ?_
  · intro z hz
    obtain ⟨v, hv, hzv⟩ := hP z hz
    refine ⟨z - fun s => mat W s *ᵥ v - v, (hY _).2 ⟨Submodule.sub_mem _ hz (cobound_mem_coc I hW hO hv), ?_⟩, ?_⟩
    · intro σ hσ
      simp only [Pi.sub_apply, hzv σ hσ, sub_self]
    · exact mem_cob.2 ⟨v, fun s _ => by simp only [sub_sub_cancel]⟩
  · intro y hy
    exact ⟨fun i => ⟨y γ i, (mem_coc.1 ((hY y).1 hy).1).2.1 γ i⟩, rfl⟩
  · intro y hy h0
    refine mem_cob.2 ⟨0, fun s hs => ?_⟩
    rw [hγ y ((hY y).1 hy).1 ((hY y).1 hy).2 h0 s hs]
    simp

end GlobalTheory.InertCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FgInertiaCocyclesModCoboundariesCoefRingStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_inertiaCocycles_mod_coboundaries_coefRing : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  first | exact @GlobalTheory.InertCoh.fg_coc_mod_cob | exact GlobalTheory.InertCoh.fg_coc_mod_cob | (intros; apply GlobalTheory.InertCoh.fg_coc_mod_cob <;> assumption)
end
end
