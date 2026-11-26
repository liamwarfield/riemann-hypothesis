module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceVectorValuedEqFiniteKernelSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRange
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infHom (lam : InfinitePlace E → DomWeight n) : Submodule ℂ (Wsp lam →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {T | ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w)}
  add_mem' ha hb x hx w := by
    simp only [LinearMap.add_apply, ha x hx, hb x hx, map_add (f := _)]
  zero_mem' x _ w := by simp
  smul_mem' c T hT x hx w := by
    simp only [LinearMap.smul_apply, hT x hx, map_smul]

theorem RU_mul (a b : UA E n) (φ : UA E n → ℂ) : RU E n (a * b) φ = RU E n a (RU E n b φ) := by
  rw [map_mul]; rfl

theorem comp_mem_infHom (lam : InfinitePlace E → DomWeight n) {T : Wsp lam →ₗ[ℂ] (UA E n → ℂ)} (hT : T ∈ infHom lam)
    (k : finU (E := E) (n := n)) : RU E n k.1 ∘ₗ T ∈ infHom lam := by
  intro x hx w
  simp only [LinearMap.comp_apply, hT x hx, ← RU_mul, GlobalTheory.DefU.fin_mul_inf k.2 hx]

theorem exists_op (lam : InfinitePlace E → DomWeight n) (A : Module.End ℂ (Wsp lam)) :
    ∃ P : Module.End ℂ (UA E n → ℂ), ∀ T ∈ infHom lam, ∀ w, T (A w) = P (T w) := by
  have hA : A ∈ Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) := by
    rw [GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top E n lam]; exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨RU E n x.1, fun T hT w => hT x.1 x.2 w⟩
  | zero => exact ⟨0, fun T _ w => by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨P, hP⟩ := hA
    obtain ⟨Q, hQ⟩ := hB
    exact ⟨P + Q, fun T hT w => by simp [hP T hT, hQ T hT]⟩
  | smul c A _ hA =>
    obtain ⟨P, hP⟩ := hA
    exact ⟨c • P, fun T hT w => by simp [hP T hT]⟩

theorem eq_zero_of_sum (lam : InfinitePlace E → DomWeight n) {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (Wsp lam))
    (T : ι → Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (hT : ∀ j, T j ∈ infHom lam) (h : ∑ j, T j (b j) = 0) (k : ι) :
    T k = 0 := by
  refine b.ext fun m => ?_
  obtain ⟨P, hP⟩ := exists_op lam ((b.coord k).smulRight (b m))
  have := congrArg P h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at this
  rw [LinearMap.zero_apply, ← this]
  rw [Finset.sum_eq_single k]
  · rw [← hP _ (hT k)]; simp
  · intro j _ hj
    rw [← hP _ (hT j)]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, hj]
  · simp

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_span_values (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π)
    (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) {φ : UA E n → ℂ} (hφ : φ ∈ π) :
    φ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ} := by
  set Sv := Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ}
  have hle : Sv ≤ π := Submodule.span_le.2 (by rintro _ ⟨T, -, hT, w, rfl⟩; exact hT w)
  have hst : ∀ g, ∀ ψ ∈ Sv, RU E n g ψ ∈ Sv := by
    intro g ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      rw [eq_splitFin_mul_splitInf g, RU_mul, ← hT _ (splitInf E n g).2]
      exact Submodule.subset_span ⟨_, comp_mem_infHom lam hT (splitFin E n g),
        fun w' => hπ.stable _ _ (hTπ w'), _, rfl⟩
    | zero => simp
    | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨T, hT0, hTπ, hT⟩ := GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep E n lam π hπ hW
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hT0
  rcases hπ.irred Sv hle hst with h | h
  · have hm : T w ∈ Sv := Submodule.subset_span ⟨T, hT, hTπ, w, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact absurd hm hw
  · rw [h]; exact hφ

theorem mem_range_of_mem (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (lam : InfinitePlace E → DomWeight n)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v))
    {φ : UA E n → ℂ} (hφ : φ ∈ π) (hfix : φ ∈ fixed (RF E n) (globLev S K')) :
    φ ∈ LinearMap.range (Phi S lam K') := by
  classical
  let b := Module.finBasis ℂ (Wsp lam)
  have hdec : ∀ ψ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ},
      ∃ T : Fin (Module.finrank ℂ (Wsp lam)) → (Wsp lam →ₗ[ℂ] (UA E n → ℂ)),
        (∀ j, T j ∈ infHom lam) ∧ (∀ j w, T j w ∈ π) ∧ ψ = ∑ j, T j (b j) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      refine ⟨fun j => b.repr w j • T, fun j => Submodule.smul_mem _ _ hT, fun j w' => π.smul_mem _ (hTπ w'), ?_⟩
      calc T w = T (∑ j, b.repr w j • b j) := by rw [b.sum_repr]
        _ = ∑ j, (b.repr w j • T) (b j) := by simp only [map_sum, map_smul, LinearMap.smul_apply]
    | zero => exact ⟨0, fun _ => zero_mem _, fun _ _ => π.zero_mem, by simp⟩
    | add a c _ _ ha hc =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      obtain ⟨C, hC, hCπ, rfl⟩ := hc
      exact ⟨A + C, fun j => add_mem (hA j) (hC j), fun j w => π.add_mem (hAπ j w) (hCπ j w),
        by simp [Finset.sum_add_distrib]⟩
    | smul c a _ ha =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      exact ⟨c • A, fun j => Submodule.smul_mem _ c (hA j), fun j w => π.smul_mem c (hAπ j w),
        by simp [Finset.smul_sum]⟩
  obtain ⟨T, hT, hTπ, rfl⟩ := hdec φ (mem_span_values lam π hπ hW hφ)
  have hfixT : ∀ k ∈ globLev S K', ∀ j, RU E n k.1 ∘ₗ T j = T j := by
    intro k hk j
    have h1 : RU E n k.1 (∑ j, T j (b j)) = ∑ j, T j (b j) := by
      have := hfix ⟨k, hk⟩
      simpa [RF] using this
    have h2 : ∑ i, (RU E n k.1 ∘ₗ T i - T i) (b i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finset.sum_sub_distrib, ← map_sum, h1, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_sum lam b _ (fun i => sub_mem (comp_mem_infHom lam (hT i) k) (hT i)) h2 j)
  obtain ⟨F, hFa⟩ : ∃ F : Fin (Module.finrank ℂ (Wsp lam)) → finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam),
      ∀ j x w, F j x w = T j w x.1 :=
    ⟨fun j x => LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) x.1 ∘ₗ T j, fun _ _ _ => rfl⟩
  have hphi : ∀ j, phiFun lam (F j) = T j := by
    intro j
    refine LinearMap.ext fun w => funext fun g => ?_
    rw [phiFun_apply, hFa]
    have hg := eq_splitFin_mul_splitInf g
    have hw : wInf lam g = wInf lam (splitInf E n g).1 := by
      conv_lhs => rw [hg]
      rw [map_mul, wInf_fin, one_mul]
    rw [hw, hT j _ (splitInf E n g).2]
    change T j w ((splitFin E n g).1 * (splitInf E n g).1) = T j w g
    rw [← hg]
  have hF : ∀ j, F j ∈ vecM S lam K' := by
    intro j
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · refine LinearMap.ext fun w => ?_
      rw [LinearMap.dualMap_apply, hFa, hFa]
      obtain ⟨r, hr, hrf, hrc⟩ := GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts E n γ
      set i := splitInf E n r
      have hri : r = (finPt γ).1 * i.1 := by rw [← hrf]; exact eq_splitFin_mul_splitInf r
      have hc : ∀ v : InfinitePlace E, cEmb v.embedding (i.1⁻¹) = GeneralLinearGroup.map v.embedding (γ⁻¹).1 := by
        intro v
        have : i.1⁻¹ = r⁻¹ * (finPt γ).1 := by rw [hri]; group
        rw [this, map_mul, map_inv, hrc v, cEmb_fin, mul_one, Subgroup.coe_inv, map_inv]
      have hwi : wInf lam i.1⁻¹ = wAt lam γ⁻¹ := by
        change PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding i.1⁻¹)) = _
        unfold wAt
        simp only [hc]
      have hl := (hπ.aut _ (hTπ j w)).left r hr (i.1⁻¹ * x.1)
      rw [← hwi, hT j _ (inv_mem i.2)]
      change T j w ((finPt γ).1 * x.1) = T j w (x.1 * i.1⁻¹)
      rw [GlobalTheory.DefU.fin_mul_inf x.2 (inv_mem i.2), ← hl, hri]
      group
    · refine LinearMap.ext fun w => ?_
      rw [hFa, hFa]
      change T j w (x.1 * k.1) = T j w x.1
      exact congrFun (LinearMap.congr_fun (hfixT k hk j) w) x.1
  refine ⟨∑ j, ⟨F j, hF j⟩ ⊗ₜ b j, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Phi_tmul, hphi]

theorem forms_le_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  refine iSup_le fun π => iSup_le fun hπ => ?_
  rintro φ ⟨hφ, hfix⟩
  exact mem_range_of_mem S K' lam π hπ.1 hπ.2 hφ hfix

end GlobalTheory.BCT.TrKer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRangeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAutForms_weight_level_le_tensor_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  first | exact @GlobalTheory.BCT.TrKer.forms_le_range | exact GlobalTheory.BCT.TrKer.forms_le_range | (intros; apply GlobalTheory.BCT.TrKer.forms_le_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctions
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer.HopStab

theorem toSub_mul_right {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (y * k)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : y * (k : G) ∈ H := H.mul_mem hy k.2
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : y * (k : G) ∉ H := fun h => hy (by simpa using H.mul_mem h (H.inv_mem k.2))
    rw [dite_eq_right h2, dite_eq_right hy]

theorem toSub_mul_left {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (k * x) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (k * y)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : (k : G) * y ∈ H := H.mul_mem k.2 hy
    rw [dite_eq_left h2, dite_eq_left hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : (k : G) * y ∉ H := fun h => hy (by simpa using H.mul_mem (H.inv_mem k.2) h)
    rw [dite_eq_right h2, dite_eq_right hy]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_loc {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K')
    {w : Pl E} (hw : w ∈ S) : ∃ k' : UL n w, k' ∈ K' w ∧ (k' : GLw n w) = cLoc w k.1 := by
  unfold globLev at hk
  have := (Subgroup.mem_iInf.1 hk w)
  have := Subgroup.mem_iInf.1 this hw
  simpa using this

theorem globFn_mul_right {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (x * k) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_right _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).2) _ k' hk'

theorem globFn_mul_left {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU (E := E) (n := n)} (hk : k ∈ globLev S K') (x : finU (E := E) (n := n)) :
    globFn S f (k * x) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_left _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).1) _ k' hk'

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hopM_apply {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam))
    (hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite)
    (x : finU (E := E) (n := n)) :
    hopM S lam K' f F x = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ •
      ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • F (x * q.out) := by
  have hsub : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' => globFn S f q.out • F (x * q.out)) ⊆
      (hfin.toFinset : Set _) := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F x) h0
    simpa [rightReg, LinearMap.funLeft] using this
  unfold hopM levOp
  rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ hsub]
  simp [rightReg, LinearMap.funLeft, Finset.sum_apply, LinearMap.sum_apply]

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab

theorem hopM_mem_vecM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  intro E _ _ _ n S lam K' _ f hf F hF
  by_cases hfin : (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite
  swap
  · have h0 : hopM S lam K' f = 0 := by
      unfold hopM levOp
      rw [finsum_of_infinite_support hfin, smul_zero]
    rw [h0]
    exact (vecM S lam K').zero_mem
  have hsupp : ∀ y : finU (E := E) (n := n), (Function.support fun q : finU (E := E) (n := n) ⧸ globLev S K' =>
      globFn S f q.out • F (y * q.out)).Finite := by
    intro y
    refine hfin.subset fun q hq => ?_
    simp only [Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) => L F y) h0
    simpa [rightReg, LinearMap.funLeft] using this
  refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
  · rw [hopM_apply f F hfin, hopM_apply f F hfin, map_smul, map_finsum _ (hsupp x)]
    congr 1
    refine finsum_congr fun q => ?_
    rw [mul_assoc, hF.1 γ, map_smul]
  · rw [hopM_apply f F hfin, hopM_apply f F hfin]
    congr 1
    symm
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K'))]
    refine finsum_congr fun q => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') (k * q.out)
    have hq : (MulAction.toPerm k : Equiv.Perm (finU (E := E) (n := n) ⧸ globLev S K')) q =
        ((k * q.out : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ globLev S K') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hh, globFn_mul_right hf.1 h.2, globFn_mul_left hf.1 hk, ← mul_assoc, ← mul_assoc, hF.2 h h.2]

end GlobalTheory.BCT.TrKer.HopStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctionsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperatorVector_mem_levelFunctions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | exact GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM | (intros; apply GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionE
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer

theorem finsum_comp_eq_comp_finsum {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (T : V →ₗ[ℂ] W) (g : ι → W →ₗ[ℂ] W) (h : ι → V →ₗ[ℂ] V) (hc : ∀ i, g i ∘ₗ T = T ∘ₗ h i)
    (hs : ∀ i, g i = 0 ↔ h i = 0) : (∑ᶠ i, g i) ∘ₗ T = T ∘ₗ ∑ᶠ i, h i := by
  have hg : Function.support g = Function.support h := by
    ext i; simp only [Function.mem_support, ne_eq, hs]
  by_cases hfin : (Function.support h).Finite
  · rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by rw [hg]; simp),
      finsum_eq_sum_of_support_subset h (s := hfin.toFinset) (by simp)]
    ext x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (hc i) x
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hg])]
    simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RF_apply' (x : finU (E := E) (n := n)) (φ : UA E n → ℂ) (g : UA E n) : RF E n x φ g = φ (g * x.1) := rfl

theorem RF_ne_zero (x : finU (E := E) (n := n)) : RF E n x ≠ 0 := by
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => (1 : ℂ))) 1
  simp at this
  exact one_ne_zero this

theorem rightReg_dual_ne_zero (lam : InfinitePlace E → DomWeight n) [Nontrivial (Wsp lam)] (x : finU (E := E) (n := n)) :
    rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) x ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Wsp lam)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Wsp lam), φ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 hc)
  intro h
  have := congrFun (LinearMap.congr_fun h (fun _ => φ)) 1
  have h2 : φ = 0 := by simpa [rightReg, LinearMap.funLeft] using this
  exact hφ (by rw [h2]; rfl)

theorem hop_phiFun (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam) :
    hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  rcases subsingleton_or_nontrivial (Wsp lam) with hW | hW
  · rw [Subsingleton.elim w 0]; simp
  set T : (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (UA E n → ℂ) := (phiFun lam).flip w with hT
  have key : (∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out • (RF E n q.out ∘ₗ LinearMap.id)) ∘ₗ T =
      T ∘ₗ ∑ᶠ q : finU (E := E) (n := n) ⧸ globLev S K', globFn S f q.out •
        (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id) := by
    refine finsum_comp_eq_comp_finsum T _ _ (fun q => ?_) (fun q => ?_)
    · ext G g
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, hT, LinearMap.flip_apply,
        LinearMap.map_smul, Pi.smul_apply]
      rw [RF_apply', phiFun_mul_fin]
    · rw [smul_eq_zero, smul_eq_zero, LinearMap.comp_id, LinearMap.comp_id]
      simp only [RF_ne_zero, rightReg_dual_ne_zero, or_false]
  have := LinearMap.congr_fun key F
  simp only [LinearMap.comp_apply, hT, LinearMap.flip_apply] at this
  simp only [hop, hopM, levOp, LinearMap.smul_apply, this, LinearMap.map_smul]

theorem hop_phiFun_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w :=
  fun _ _ _ _ _ S lam K' f F w => hop_phiFun S lam K' f F w

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionEStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (F : finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) (w : Wsp lam), hop S K' f (phiFun lam F w) = phiFun lam (hopM S lam K' f F) w := by
  first | exact @GlobalTheory.BCT.TrKer.hop_phiFun_comm | exact GlobalTheory.BCT.TrKer.hop_phiFun_comm | (intros; apply GlobalTheory.BCT.TrKer.hop_phiFun_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftOfFiniteTensorProductComplex
open scoped TensorProduct

namespace GlobalTheory

open scoped TensorProduct in
private lemma trace_eq_zero_of_not_finite' {V : Type} [AddCommGroup V] [Module ℂ V]
    (h : ¬ Module.Finite ℂ V) (f : V →ₗ[ℂ] V) : LinearMap.trace ℂ V f = 0 := by
  have hb : ¬ ∃ s : Finset V, Nonempty (Module.Basis s ℂ V) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp [LinearMap.trace, hb]

open scoped TensorProduct in
private lemma finite_left_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ V := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra! h
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).mp h)
  let p : V ⊗[ℂ] W →ₗ[ℂ] V :=
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ
  refine Module.Finite.of_surjective p fun v => ⟨v ⊗ₜ ((φ w)⁻¹ • w), ?_⟩
  simp [p, hφ]

open scoped TensorProduct in
private lemma finite_right_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ W := by
  have : Module.Finite ℂ (W ⊗[ℂ] V) :=
    Module.Finite.equiv (TensorProduct.comm ℂ V W)
  exact finite_left_of_finite_tensor_of_nontrivial (W := V)


open scoped TensorProduct in
theorem _root_.GlobalTheory.trace_tensorProduct_map_complex {U U' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] (T : U →ₗ[ℂ] U) (T' : U' →ₗ[ℂ] U') :
    LinearMap.trace ℂ (U ⊗[ℂ] U') (TensorProduct.map T T') =
      LinearMap.trace ℂ U T * LinearMap.trace ℂ U' T' := by
  by_cases hU : Module.Finite ℂ U
  · by_cases hU' : Module.Finite ℂ U'
    · exact LinearMap.trace_tensorProduct' T T'
    · rw [trace_eq_zero_of_not_finite' hU' T', mul_zero]
      by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
      · rcases subsingleton_or_nontrivial U with hs | hs
        · rw [Subsingleton.elim T 0, TensorProduct.map_zero_left, map_zero]
        · exact absurd (finite_right_of_finite_tensor_of_nontrivial (V := U)) hU'
      · exact trace_eq_zero_of_not_finite' hUU _
  · rw [trace_eq_zero_of_not_finite' hU T, zero_mul]
    by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
    · rcases subsingleton_or_nontrivial U' with hs | hs
      · rw [Subsingleton.elim T' 0, TensorProduct.map_zero_right, map_zero]
      · exact absurd (finite_left_of_finite_tensor_of_nontrivial (W := U')) hU
    · exact trace_eq_zero_of_not_finite' hUU _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMul
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem trace_map_id {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (A : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ (M ⊗[ℂ] W) (TensorProduct.map A LinearMap.id) =
      LinearMap.trace ℂ M A * Module.finrank ℂ W := by
  rw [GlobalTheory.trace_tensorProduct_map_complex, LinearMap.trace_id]

theorem trOn_forms_eq_finrank_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = (Module.finrank ℂ (GlobalTheory.BCT.TrKer.Wsp lam) : ℂ) * trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) := by
  intro E _ _ _ hE n hn S hS lam K' hK f hf
  have hinj := GlobalTheory.T.automorphic_map_phi_injective E hE n hn S hS lam K' hK
  have hrange : LinearMap.range (Phi S lam K') = forms S lam K' :=
    le_antisymm (GlobalTheory.T.vectorFormTensor_range_le_unitaryAutFormsWeightLevel E hE n hn S hS lam K' hK) (GlobalTheory.T.unitaryAutForms_weight_level_le_tensor_range E hE n hn S hS lam K' hK)
  have hM := GlobalTheory.T.unitaryHeckeOperatorVector_mem_levelFunctions E n S lam K' hK f hf
  let A := (hopM S lam K' f).restrict hM
  have hcomm : ∀ x, hop S K' f (Phi S lam K' x) = Phi S lam K' (TensorProduct.map A LinearMap.id x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul F w =>
      rw [TensorProduct.map_tmul, Phi_tmul, Phi_tmul, GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  have hF : ∀ v ∈ forms S lam K', hop S K' f v ∈ forms S lam K' := by
    intro v hv
    rw [← hrange] at hv ⊢
    obtain ⟨x, rfl⟩ := hv
    exact ⟨_, (hcomm x).symm⟩
  obtain ⟨e, hev⟩ : ∃ e : (vecM S lam K' ⊗[ℂ] Wsp lam) ≃ₗ[ℂ] forms S lam K',
      ∀ y, ((e y : forms S lam K') : UA E n → ℂ) = Phi S lam K' y :=
    ⟨(LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange), fun y => rfl⟩
  have he : (hop S K' f).restrict hF = e.conj (TensorProduct.map A LinearMap.id) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv : (v : UA E n → ℂ) = Phi S lam K' (e.symm v) :=
      (congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (e.apply_symm_apply v)).symm.trans (hev _)
    calc (((hop S K' f).restrict hF v : forms S lam K') : UA E n → ℂ) = hop S K' f v :=
          LinearMap.restrict_coe_apply _ _ v
      _ = hop S K' f (Phi S lam K' (e.symm v)) := congrArg _ hv
      _ = Phi S lam K' (TensorProduct.map A LinearMap.id (e.symm v)) := hcomm _
      _ = ((e (TensorProduct.map A LinearMap.id (e.symm v)) : forms S lam K') : UA E n → ℂ) := (hev _).symm
      _ = ((e.conj (TensorProduct.map A LinearMap.id) v : forms S lam K') : UA E n → ℂ) :=
          congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (LinearEquiv.conj_apply_apply _ _ _).symm
  have h1 : trOn (forms S lam K') (hop S K' f) = LinearMap.trace ℂ _ ((hop S K' f).restrict hF) := dif_pos hF
  have h2 : trOn (vecM S lam K') (hopM S lam K' f) = LinearMap.trace ℂ _ A := dif_pos hM
  rw [h1, h2]
  exact (congrArg (LinearMap.trace ℂ _) he).trans
    ((LinearMap.trace_conj' _ e).trans ((trace_map_id A).trans (mul_comm _ _)))

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMulStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_forms_weight_eq_finrank_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = (Module.finrank ℂ (GlobalTheory.BCT.TrKer.Wsp lam) : ℂ) * trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) := by
  first | exact @GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul | exact GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul | (intros; apply GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsEqDimMulKernelSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_kernSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = dimW lam * kernSum S lam K' f := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf
  rw [GlobalTheory.T.heckeTrace_forms_weight_eq_finrank_mul E hU n hn S hS lam K' hK f hf, GlobalTheory.T.heckeTrace_vectorValued_eq_finite_kernelSum E hU n hn S hS lam K' hK f hf, TrKer.finrank_wsp]
  unfold kernSum
  congr 2
  refine finsum_congr fun q => ?_
  congr 1
  refine finsum_congr fun γ => ?_
  congr 1
  unfold TrKer.wAt chW
  rw [TrKer.trace_piMap]
  exact Finset.prod_congr rfl fun v _ => GlobalTheory.T.trace_dualWeylModule_inv_rationalPoint_eq_conj_charAt E n (lam v) γ v

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsEqDimMulKernelSumStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_forms_eq_dim_mul_kernelSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = dimW lam * kernSum S lam K' f := by
  first | exact @GlobalTheory.BCT.trOn_forms_hop_eq_kernSum | exact GlobalTheory.BCT.trOn_forms_hop_eq_kernSum | (intros; apply GlobalTheory.BCT.trOn_forms_hop_eq_kernSum <;> assumption)
end
