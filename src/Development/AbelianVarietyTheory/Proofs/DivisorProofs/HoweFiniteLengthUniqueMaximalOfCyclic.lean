module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HwSubStableOfComm
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem hwSub_stable_of_comm {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (f : Module.End ℂ V)
    (hf : ∀ Z v, f (act Z v) = act Z (f v)) (μ : Ix p q → ℚ) :
    ∀ v ∈ hwSub act μ, f v ∈ hwSub act μ := by
  intro v hv
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have := congrArg f (h1 a)
    simpa [hf, map_sub, map_smul] using this
  · rw [← hf, h2 a b hab, map_zero]

theorem hw_joint_split : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) →
    ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') →
    ∀ μ : ∀ w, Ix (R w) (S w) → ℚ,
    (N ⊔ N') ⊓ (⨅ w, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w, hwSub (a w) (μ w)) := by
  intro T _ _ R S V _ _ a hg hc N N' hN hN' μ
  have key : ∀ s : Finset T, (N ⊔ N') ⊓ (⨅ w ∈ s, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hws ih =>
      set H := ⨅ w ∈ s, hwSub (a w) (μ w) with hH
      have hHst : ∀ X, ∀ v ∈ H, a w X v ∈ H := by
        intro X v hv
        rw [hH, Submodule.mem_iInf] at hv ⊢
        intro w'
        have hv' := hv w'
        rw [Submodule.mem_iInf] at hv' ⊢
        intro hw'
        have hne : w ≠ w' := fun h => hws (h ▸ hw')
        exact hwSub_stable_of_comm (a w') (a w X) (fun Z u => hc w w' hne X Z u) (μ w') v (hv' hw')
      have hK : ∀ M : Submodule ℂ V, (∀ Z, ∀ y ∈ M, a w Z y ∈ M) → KStable (a w) (M ⊓ H) := by
        intro M hM X _ v hv
        exact Submodule.mem_inf.mpr ⟨hM X v (Submodule.mem_inf.mp hv).1, hHst X v (Submodule.mem_inf.mp hv).2⟩
      have hsp := GlobalTheory.T.howeHighestWeight_sup_stable_le (R w) (S w) V (a w) (hg w) (N ⊓ H) (N' ⊓ H) (hK N (hN w)) (hK N' (hN' w)) (μ w)
      rw [Finset.iInf_insert]
      calc (N ⊔ N') ⊓ (hwSub (a w) (μ w) ⊓ H) = ((N ⊔ N') ⊓ H) ⊓ hwSub (a w) (μ w) := by
              rw [inf_comm (hwSub (a w) (μ w)) H, inf_assoc]
        _ ≤ ((N ⊓ H) ⊔ (N' ⊓ H)) ⊓ hwSub (a w) (μ w) := inf_le_inf_right _ ih
        _ ≤ ((N ⊓ H) ⊓ hwSub (a w) (μ w)) ⊔ ((N' ⊓ H) ⊓ hwSub (a w) (μ w)) := hsp
        _ = (N ⊓ (hwSub (a w) (μ w) ⊓ H)) ⊔ (N' ⊓ (hwSub (a w) (μ w) ⊓ H)) := by
              rw [inf_assoc, inf_assoc, inf_comm H]
  simpa using key Finset.univ

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiPlaceStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHWOfFd
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem exists_isHW_of_fd : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act →
    (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∀ U : Submodule ℂ V, U ≠ ⊥ →
    FiniteDimensional ℂ U → KStable act U → ∃ (μ : Ix p q → ℚ) (v : V), v ∈ U ∧ IsHW act μ v := by
  intro p q V _ _ act hL hd U hU hfd hK
  exact GlobalTheory.BlockReps.exists_hw (fun Y Z _ _ => hL Y Z) hK (fun v _ => hd v) hU

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameBlockIffIsLeft
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem eab_mul_eab {p q : ℕ} (a b c d : Ix p q) :
    Eab a b * Eab c d = if b = c then Eab a d else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem mat_eq_sum_eab {p q : ℕ} (X : Mat p q) : X = ∑ a, ∑ b, X a b • Eab a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold Eab; rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem act_eq_sum_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (X : Mat p q) (v : V) :
    act X v = ∑ a, ∑ b, X a b • units act a b v := by
  conv_lhs => rw [mat_eq_sum_eab X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, units]

theorem sameBlock_iff_isLeft {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

theorem lie_units_stab : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V),
    (IsLieAct act → IsGl (units act)) ∧
    (∀ N : Submodule ℂ V, (∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ N, units act a b u ∈ N) ↔ KStable act N) ∧
    ∀ N : Submodule ℂ V, (∀ a b, ∀ u ∈ N, units act a b u ∈ N) → Stab act N := by
  intro p q V _ _ act
  refine ⟨fun hL a b c d => ?_, fun N => ⟨fun h X hX w hw => ?_, fun h a b hab u hu => ?_⟩, fun N h Z y hy => ?_⟩
  · simp only [units]
    rw [← hL, eab_mul_eab, eab_mul_eab, map_sub]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp
  · rw [act_eq_sum_units]
    refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
    by_cases hab : a.isLeft = b.isLeft
    · exact N.smul_mem _ (h a b hab w hw)
    · rw [hX a b (fun hs => hab ((sameBlock_iff_isLeft a b).1 hs)), zero_smul]; exact N.zero_mem
  · refine h (Eab a b) (fun c d hcd => ?_) u hu
    unfold Eab
    rw [Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'; exact absurd ((sameBlock_iff_isLeft _ _).2 hab) hcd
    · rfl
  · rw [act_eq_sum_units]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (h a b y hy)

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceComapInjectiveIntert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceComapInjectiveIntert
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_comap_locU (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M) (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (hf : Function.Injective f) (hF : ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) :
    (∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)) ∧ (LocU s F' → LocU s F) := by
  have key : ∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f) := by
    rintro U' ⟨hfin, hst, ip', hs, hp, hadj⟩
    refine ⟨?_, ?_, ?_⟩
    · have hinj : Function.Injective (f.restrict (p := U'.comap f) (q := U') (fun x hx => hx)) := by
        intro x y hxy
        apply Subtype.ext
        apply hf
        have := congrArg Subtype.val hxy
        simpa using this
      exact Module.Finite.of_injective _ hinj
    · intro a b hab u hu
      show f (F a b u) ∈ U'
      rw [hF a b hab]
      exact hst a b hab (f u) hu
    · refine ⟨(ip'.comp f).compl₂ f, ?_, ?_, ?_⟩
      · intro x hx y hy
        simpa using hs (f x) hx (f y) hy
      · intro x hx hx0
        have : f x ≠ 0 := fun h => hx0 (hf (by rw [h, map_zero]))
        simpa using hp (f x) hx this
      · intro a b hab x hx y hy
        have hba : s b = s a := hab.symm
        simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
        rw [hF a b hab, hF b a hba]
        exact hadj a b hab (f x) hx (f y) hy
  refine ⟨key, ?_⟩
  intro hL t
  classical
  obtain ⟨U', ht, hU'⟩ := hL (t.image f)
  refine ⟨U'.comap f, ?_, key U' hU'⟩
  intro x hx
  exact ht (f x) (Finset.mem_image_of_mem f hx)

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceComapInjectiveIntertStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_comap_injective_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M'), Function.Injective f → (∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (∀ U' : Submodule ℂ M', UnitOn s F' U' → UnitOn s F (U'.comap f)) ∧ (LocU s F' → LocU s F) := by
  first | exact @GlobalTheory.HoweR.unitOn_comap_locU | exact GlobalTheory.HoweR.unitOn_comap_locU | (intros; apply GlobalTheory.HoweR.unitOn_comap_locU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquot
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SubQuot

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_wtSub' {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem mem_hwSub' {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, mem_wtSub', Submodule.mem_iInf]

variable (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N N' : Submodule ℂ V)

def resA (h' : Stab act N') : Mat p q →ₗ[ℂ] Module.End ℂ N' where
  toFun Z := (act Z).restrict (h' Z)
  map_add' X Y := by
    ext x
    simp [LinearMap.restrict_apply]
  map_smul' c X := by
    ext x
    simp [LinearMap.restrict_apply]

theorem resA_coe (h' : Stab act N') (Z : Mat p q) (x : N') :
    ((resA act N' h' Z x : N') : V) = act Z x := rfl

abbrev below : Submodule ℂ N' := N.comap N'.subtype

theorem le_comap_resA (h : Stab act N) (h' : Stab act N') (Z : Mat p q) :
    below N N' ≤ (below N N').comap (resA act N' h' Z) := fun x hx => h Z x hx

def quoA (h : Stab act N) (h' : Stab act N') : Mat p q →ₗ[ℂ] Module.End ℂ (N' ⧸ below N N') where
  toFun Z := (below N N').mapQ (below N N') (resA act N' h' Z) (le_comap_resA act N N' h h' Z)
  map_add' X Y := by
    apply Submodule.linearMap_qext
    ext x
    simp
  map_smul' c X := by
    apply Submodule.linearMap_qext
    ext x
    simp

def Rel (T : Module.End ℂ V) (T' : Module.End ℂ (N' ⧸ below N N')) : Prop :=
  ∀ x : N', ∃ y : N', (y : V) = T x ∧ T' ((below N N').mkQ x) = (below N N').mkQ y

variable {N N'}

theorem Rel.mul {T₁ T₂ : Module.End ℂ V} {T₁' T₂' : Module.End ℂ (N' ⧸ below N N')} (h₁ : Rel N N' T₁ T₁')
    (h₂ : Rel N N' T₂ T₂') : Rel N N' (T₁ * T₂) (T₁' * T₂') := by
  intro x
  obtain ⟨y₂, hy₂, e₂⟩ := h₂ x
  obtain ⟨y₁, hy₁, e₁⟩ := h₁ y₂
  refine ⟨y₁, ?_, ?_⟩
  · rw [hy₁, hy₂]; rfl
  · rw [Module.End.mul_apply, e₂, e₁]

theorem Rel.add {T₁ T₂ : Module.End ℂ V} {T₁' T₂' : Module.End ℂ (N' ⧸ below N N')} (h₁ : Rel N N' T₁ T₁')
    (h₂ : Rel N N' T₂ T₂') : Rel N N' (T₁ + T₂) (T₁' + T₂') := by
  intro x
  obtain ⟨y₂, hy₂, e₂⟩ := h₂ x
  obtain ⟨y₁, hy₁, e₁⟩ := h₁ x
  refine ⟨y₁ + y₂, ?_, ?_⟩
  · rw [Submodule.coe_add, hy₁, hy₂]; rfl
  · rw [LinearMap.add_apply, e₁, e₂, map_add (f := _)]

theorem Rel.sub {T₁ T₂ : Module.End ℂ V} {T₁' T₂' : Module.End ℂ (N' ⧸ below N N')} (h₁ : Rel N N' T₁ T₁')
    (h₂ : Rel N N' T₂ T₂') : Rel N N' (T₁ - T₂) (T₁' - T₂') := by
  intro x
  obtain ⟨y₂, hy₂, e₂⟩ := h₂ x
  obtain ⟨y₁, hy₁, e₁⟩ := h₁ x
  refine ⟨y₁ - y₂, ?_, ?_⟩
  · rw [Submodule.coe_sub, hy₁, hy₂]; rfl
  · rw [LinearMap.sub_apply, e₁, e₂, map_sub]

theorem Rel.smul {T : Module.End ℂ V} {T' : Module.End ℂ (N' ⧸ below N N')} (h : Rel N N' T T') (c : ℂ) :
    Rel N N' (c • T) (c • T') := by
  intro x
  obtain ⟨y, hy, e⟩ := h x
  refine ⟨c • y, ?_, ?_⟩
  · rw [Submodule.coe_smul, hy]; rfl
  · rw [LinearMap.smul_apply, e, map_smul]

theorem Rel.neg {T : Module.End ℂ V} {T' : Module.End ℂ (N' ⧸ below N N')} (h : Rel N N' T T') :
    Rel N N' (-T) (-T') := by
  intro x
  obtain ⟨y, hy, e⟩ := h x
  refine ⟨-y, ?_, ?_⟩
  · rw [Submodule.coe_neg, hy]; rfl
  · rw [LinearMap.neg_apply, e, map_neg]

theorem Rel.one : Rel N N' (1 : Module.End ℂ V) 1 := fun x => ⟨x, rfl, rfl⟩

theorem Rel.zero : Rel N N' (0 : Module.End ℂ V) 0 := fun _ => ⟨0, rfl, by simp⟩

theorem Rel.sum {κ : Type} (s : Finset κ) {T : κ → Module.End ℂ V} {T' : κ → Module.End ℂ (N' ⧸ below N N')}
    (h : ∀ i, Rel N N' (T i) (T' i)) : Rel N N' (∑ i ∈ s, T i) (∑ i ∈ s, T' i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (Rel.zero : Rel N N' 0 0)
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

theorem rel_qop {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → ι → Module.End ℂ V}
    {G' : ι → ι → Module.End ℂ (N' ⧸ below N N')} (h : ∀ a b, Rel N N' (G a b) (G' a b)) (α β : ℂ) (a b : ι) :
    Rel N N' (qop G α β a b) (qop G' α β a b) := by
  unfold qop
  refine ((Rel.sum _ fun c => (h a c).mul (h c b)).sub ((h a b).smul α)).sub ?_
  split_ifs
  · exact Rel.one.smul β
  · exact Rel.zero

theorem rel_negT {ι : Type} {G : ι → ι → Module.End ℂ V}
    {G' : ι → ι → Module.End ℂ (N' ⧸ below N N')} (h : ∀ a b, Rel N N' (G a b) (G' a b)) (a b : ι) :
    Rel N N' (negT G a b) (negT G' a b) := Rel.neg (h b a)

end GlobalTheory.HoweR.SubQuot

namespace GlobalTheory.HoweR


open SubQuot in
theorem exists_hwSub_of_quadMod : ∀ (p q : ℕ) (α β α' β' : ℂ), ∃ B : ℚ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, N < N' → Stab act N →
    Stab act N' → QuadMod act α β α' β' N N' →
    ∃ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) ∧ ∃ v ∈ N', v ∈ hwSub act μ ∧ v ∉ N := by
  intro p q α β α' β'
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_unitary_piece_bounded_weights_of_quadratic (Ix p q) (fun a => a.isLeft) α β α' β'
  obtain ⟨B, hB⟩ := exists_rat_gt R
  refine ⟨B, ?_⟩
  intro V _ _ act hG N N' hlt hN hN' hQ
  let K := below N N'
  let A := quoA act N N' hN hN'
  have hmk : ∀ Z (x : N'), A Z (K.mkQ x) = K.mkQ (resA act N' hN' Z x) := fun _ _ => rfl

  have hlie : IsLieAct A := by
    intro X Y
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    have e : resA act N' hN' (X * Y - Y * X) x =
        resA act N' hN' X (resA act N' hN' Y x) - resA act N' hN' Y (resA act N' hN' X x) := by
      ext
      simp only [resA_coe, Submodule.coe_sub, hG.1 X Y, LinearMap.sub_apply, Module.End.mul_apply]
    rw [hmk, e, map_sub]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hmk]

  have hwts : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub A μ := by
    intro v
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    have h1 := GlobalTheory.WeightDecomp.mem_iSup_inf_wtSub p q V act N' (fun a => hN' _) x x.2 (hG.2.1 x)
    have h2 : (⨆ μ : Ix p q → ℚ, N' ⊓ wtSub act μ) ≤
        ((⨆ μ : Ix p q → ℚ, wtSub A μ).comap K.mkQ).map N'.subtype := by
      refine iSup_le fun μ y hy => ⟨⟨y, (Submodule.mem_inf.1 hy).1⟩, ?_, rfl⟩
      show K.mkQ ⟨y, (Submodule.mem_inf.1 hy).1⟩ ∈ ⨆ μ : Ix p q → ℚ, wtSub A μ
      refine Submodule.mem_iSup_of_mem μ ?_
      have hy2 := mem_wtSub'.1 (Submodule.mem_inf.1 hy).2
      refine mem_wtSub'.2 fun a => ?_
      rw [hmk, ← map_smul]
      congr 1
      ext
      exact hy2 a
    obtain ⟨y, hy, hyx⟩ := h2 h1
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

  have hres : LocU (fun a : Ix p q => a.isLeft) (units (resA act N' hN')) :=
    (GlobalTheory.T.isBlockUnitaryFiniteSubspace_comap_injective_intertwiner (Ix p q) N' (fun a => a.isLeft) (units (resA act N' hN')) V (units act) N'.subtype
      Subtype.val_injective (fun a b _ x => rfl)).2 hG.2.2
  have hloc : LocU (fun a : Ix p q => a.isLeft) (units A) :=
    GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range (Ix p q) N' (fun a => a.isLeft) (units (resA act N' hN')) (N' ⧸ K) (units A) {K.mkQ}
      (by
        intro f hf a b _ x
        rw [Set.mem_singleton_iff] at hf
        subst hf
        rfl)
      (by simp) hres

  have hrel : ∀ a b, Rel N N' (units act a b) (units A a b) :=
    fun a b x => ⟨resA act N' hN' (Eab a b) x, rfl, rfl⟩
  have hq1 : ∀ a b, qop (units A) α β a b = 0 := by
    intro a b
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    obtain ⟨y, hy, e⟩ := rel_qop hrel α β a b x
    rw [LinearMap.zero_apply, e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (y : V) ∈ N
    rw [hy]
    exact (hQ a b x x.2).1
  have hq2 : ∀ a b, qop (negT (units A)) α' β' a b = 0 := by
    intro a b
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := K.mkQ_surjective v
    obtain ⟨y, hy, e⟩ := rel_qop (rel_negT hrel) α' β' a b x
    rw [LinearMap.zero_apply, e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (y : V) ∈ N
    rw [hy]
    exact (hQ a b x x.2).2

  obtain ⟨x₀, hx₀', hx₀⟩ := SetLike.exists_of_lt hlt
  have hx0 : K.mkQ ⟨x₀, hx₀'⟩ ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hx₀
  have hnt : Nontrivial (N' ⧸ K) := ⟨⟨_, 0, hx0⟩⟩
  have hgl : IsGl (units A) := (GlobalTheory.HoweR.lie_units_stab p q (N' ⧸ K) A).1 hlie
  obtain ⟨U, hU0, hUu, hUb⟩ := hR (N' ⧸ K) (units A) hnt hgl hq1 hq2 hloc
  have hKS : KStable A U := ((GlobalTheory.HoweR.lie_units_stab p q (N' ⧸ K) A).2.1 U).1 hUu.2.1
  haveI : FiniteDimensional ℂ U := hUu.1
  obtain ⟨μ, v, hvU, hv0, hvhw⟩ := GlobalTheory.HoweR.exists_isHW_of_fd p q (N' ⧸ K) A hlie hwts U hU0 hUu.1 hKS
  have hbd : ∀ a, |μ a| ≤ B := by
    intro a
    have h := hUb a v hvU hv0 ((μ a : ℚ) : ℂ) ((mem_hwSub'.1 hvhw).1 a)
    rw [Complex.ratCast_re] at h
    exact_mod_cast h.trans hB.le
  obtain ⟨x, rfl⟩ := K.mkQ_surjective v
  have hc : ∀ c, act (Eab c c) (x : V) - ((μ c : ℚ) : ℂ) • (x : V) ∈ N := by
    intro c
    have e : K.mkQ (resA act N' hN' (Eab c c) x) = K.mkQ (((μ c : ℚ) : ℂ) • x) := by
      rw [← hmk, map_smul]
      exact (mem_hwSub'.1 hvhw).1 c
    exact (Submodule.Quotient.eq K).1 e
  have hd : ∀ c d, posC c d → act (Eab c d) (x : V) ∈ N := by
    intro c d hcd
    have e : K.mkQ (resA act N' hN' (Eab c d) x) = 0 := by
      rw [← hmk]
      exact (mem_hwSub'.1 hvhw).2 c d hcd
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at e
    exact e
  have kst : ∀ W : Submodule ℂ V, Stab act W → KStable act W := fun W hW X _ w hw => hW X w hw
  obtain ⟨v', hv'N', hv'hw, hxv'⟩ :=
    GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace p q V act hG N N' (kst N hN) (kst N' hN') μ (x : V) x.2 hc hd
  refine ⟨μ, hbd, v', hv'N', hv'hw, fun hv'N => hv0 ?_⟩
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show (x : V) ∈ N
  simpa using N.add_mem hxv' hv'N

end GlobalTheory.HoweR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquotStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boundedHighestWeightVector_quadraticSubquotient : ∀ (p q : ℕ) (α β α' β' : ℂ), ∃ B : ℚ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, N < N' → Stab act N → Stab act N' → QuadMod act α β α' β' N N' → ∃ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) ∧ ∃ v ∈ N', v ∈ hwSub act μ ∧ v ∉ N := by
  first | exact @GlobalTheory.HoweR.exists_hwSub_of_quadMod | exact GlobalTheory.HoweR.exists_hwSub_of_quadMod | (intros; apply GlobalTheory.HoweR.exists_hwSub_of_quadMod <;> assumption)
end
end

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.Places

section One

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_hwSub_iff (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub a μ ↔ (∀ c, a (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → a (Eab c d) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem hw_comm {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {L : Module.End ℂ V} (h : ∀ Z v, L (a Z v) = a Z (L v))
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub a μ) : L v ∈ hwSub a μ := by
  rw [mem_hwSub_iff] at hv ⊢
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · rw [← h, hv.1 c, map_smul]
  · rw [← h, hv.2 c d hcd, map_zero]

end One

section Quad

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem qop_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) (α β : ℂ)
    (a b : ι) {v : M} (hv : v ∈ H) : qop F α β a b v ∈ H := by
  unfold qop
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply]
  refine H.sub_mem (H.sub_mem (H.sum_mem fun c _ => hF _ _ _ (hF _ _ _ hv)) (H.smul_mem _ (hF _ _ _ hv))) ?_
  by_cases hab : a = b
  · simpa [hab] using H.smul_mem β hv
  · simp [hab]

theorem negT_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) :
    ∀ a b, ∀ u ∈ H, negT F a b u ∈ H := fun a b u hu => by
  simp only [negT, LinearMap.neg_apply]
  exact H.neg_mem (hF b a u hu)

end Quad

theorem multi_place_step : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (α β α' β' : T → ℂ), ∃ B : ℚ,
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ N N' : Submodule ℂ V, N < N' →
    (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') → (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) N N') →
    ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) ∧ ∃ v ∈ N', (∀ w, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
  intro T _ _ R S α β α' β'
  have hk := fun w => GlobalTheory.T.exists_boundedHighestWeightVector_quadraticSubquotient (R w) (S w) (α w) (β w) (α' w) (β' w)
  choose Bw hBw using hk
  refine ⟨∑ w, |Bw w|, ?_⟩
  intro V _ _ a hG hc N N' hNN' hsN hsN' hQ
  have hB : ∀ w, |Bw w| ≤ ∑ w, |Bw w| := fun w =>
    Finset.single_le_sum (f := fun w => |Bw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  have h0 : (0 : ℚ) ≤ ∑ w, |Bw w| := Finset.sum_nonneg fun w _ => abs_nonneg (Bw w)
  have key : ∀ s : Finset T, ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ ∑ w, |Bw w|) ∧
      ∃ v ∈ N', (∀ w ∈ s, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨v, hv, hvN⟩ := SetLike.exists_of_lt hNN'
      exact ⟨fun _ _ => 0, fun _ _ => by simpa using h0, v, hv, by simp, hvN⟩
    | insert w s hws ih =>
      obtain ⟨μ, hμB, v, hvN', hvs, hvN⟩ := ih
      let H : Submodule ℂ V := ⨅ w' ∈ s, hwSub (a w') (μ w')
      have memH : ∀ u, u ∈ H ↔ ∀ w' ∈ s, u ∈ hwSub (a w') (μ w') := fun u => by
        simp only [H, Submodule.mem_iInf]
      have sH : ∀ Z, ∀ u ∈ H, a w Z u ∈ H := fun Z u hu => by
        rw [memH] at hu ⊢
        intro w' hw'
        exact hw_comm (fun Z' x => hc w w' (fun e => hws (e ▸ hw')) Z Z' x) (hu w' hw')
      have sU : ∀ c d, ∀ u ∈ H, units (a w) c d u ∈ H := fun c d u hu => sH _ u hu
      have hlt : N ⊓ H < N' ⊓ H := by
        refine lt_of_le_of_ne (inf_le_inf_right _ hNN'.le) fun e => hvN ?_
        have : v ∈ N' ⊓ H := ⟨hvN', (memH v).2 hvs⟩
        rw [← e] at this
        exact this.1
      have hS1 : Stab (a w) (N ⊓ H) := fun Z u hu => ⟨hsN w Z u hu.1, sH Z u hu.2⟩
      have hS2 : Stab (a w) (N' ⊓ H) := fun Z u hu => ⟨hsN' w Z u hu.1, sH Z u hu.2⟩
      have hQ' : QuadMod (a w) (α w) (β w) (α' w) (β' w) (N ⊓ H) (N' ⊓ H) := fun c d u hu =>
        ⟨⟨(hQ w c d u hu.1).1, qop_mem _ H sU _ _ c d hu.2⟩,
          ⟨(hQ w c d u hu.1).2, qop_mem _ H (negT_mem _ H sU) _ _ c d hu.2⟩⟩
      obtain ⟨ν, hνB, u, huN', huhw, huN⟩ := hBw w V (a w) (hG w) _ _ hlt hS1 hS2 hQ'
      refine ⟨Function.update μ w ν, fun w' c => ?_, u, huN'.1, fun w' hw' => ?_, fun h => huN ⟨h, huN'.2⟩⟩
      · rcases eq_or_ne w' w with rfl | e
        · simp only [Function.update_self]
          exact (hνB c).trans ((le_abs_self _).trans (hB w'))
        · rw [Function.update_of_ne e]
          exact hμB w' c
      · rcases Finset.mem_insert.1 hw' with rfl | hw''
        · simpa using huhw
        · have hne : w' ≠ w := fun e => hws (e ▸ hw'')
          rw [Function.update_of_ne hne]
          exact (memH u).1 huN'.2 w' hw''
  obtain ⟨μ, hμ, v, hv, hvs, hvN⟩ := key Finset.univ
  exact ⟨μ, hμ, v, hv, fun w => hvs w (Finset.mem_univ w), hvN⟩

end GlobalTheory.HoweR.Places

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainLengthLeFinrankAddOne
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem chain_length_le_finrank_add_one : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (G U C : Submodule ℂ V), FiniteDimensional ℂ U → G ≤ U ⊔ C → ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, C ≤ N k) → (∀ k l, k < l → ∃ v ∈ N l, v ∈ G ∧ v ∉ N k) → m ≤ Module.finrank ℂ U + 1 := by
  intro V _ _ G U C hU hGUC m N hN hC hsep
  let g : Fin m → Submodule ℂ U := fun k => (N k).comap U.subtype
  have hg : StrictMono g := by
    intro k l hkl
    refine lt_of_le_of_ne (fun x hx => hN.monotone hkl.le hx) ?_
    intro heq
    obtain ⟨v, hvl, hvG, hvk⟩ := hsep k l hkl
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp (hGUC hvG)
    have hcl : c ∈ N l := hC l hc
    have hul : u ∈ N l := by simpa using (N l).sub_mem hvl hcl
    have hmem : (⟨u, hu⟩ : U) ∈ g l := hul
    rw [← heq] at hmem
    exact hvk ((N k).add_mem hmem (hC k hc))
  let f : Fin m → Fin (Module.finrank ℂ U + 1) := fun k =>
    ⟨Module.finrank ℂ (g k), Nat.lt_succ_of_le (Submodule.finrank_le _)⟩
  have hf : Function.Injective f := by
    intro k l h
    have h' : Module.finrank ℂ (g k) = Module.finrank ℂ (g l) := congrArg Fin.val h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'.symm
  simpa using Fintype.card_le_of_injective f hf

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclic
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem howe_finiteLength_uniqueMaximal_of_cyclic : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  intro T _ _ R S V _ _ a hG hc C α β α' β' hQ hAdm hCyc
  refine ⟨?_, ?_⟩
  · obtain ⟨B, hB⟩ := Places.multi_place_step T R S α β α' β'
    obtain ⟨U, hU, hUC⟩ := hAdm B
    let G : Submodule ℂ V := ⨆ (μ : ∀ w, Ix (R w) (S w) → ℚ) (_ : ∀ w c, |μ w c| ≤ B), ⨅ w, hwSub (a w) (μ w)
    have hGUC : G ≤ U ⊔ C := iSup_le fun μ => iSup_le fun h => hUC μ h
    refine ⟨Module.finrank ℂ U + 1, fun m N hN hNk => ?_⟩
    refine chain_length_le_finrank_add_one V G U C hU hGUC m N hN (fun k => (hNk k).2) ?_
    intro k l hkl
    have hQ' : ∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) (N k) (N l) := fun w c d u _ =>
      ⟨(hNk k).2 (hQ w c d u Submodule.mem_top).1, (hNk k).2 (hQ w c d u Submodule.mem_top).2⟩
    obtain ⟨μ, hμB, v, hvl, hvhw, hvk⟩ :=
      hB V a hG hc (N k) (N l) (hN hkl) (fun w => (hNk k).1 w) (fun w => (hNk l).1 w) hQ'
    refine ⟨v, hvl, ?_, hvk⟩
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    exact (le_iSup_of_le μ (le_iSup_of_le hμB le_rfl) : (⨅ w, hwSub (a w) (μ w)) ≤ G) hv
  · intro N N' hN hCN hNt hN' hCN' hN't hsup
    obtain ⟨μ, v, hvhw, hgen, hmult⟩ := hCyc
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    have hv2 : v ∈ (N ⊔ N') ⊓ ⨅ w, hwSub (a w) (μ w) := ⟨by rw [hsup]; exact Submodule.mem_top, hv⟩
    have hsp := hw_joint_split T R S V a hG hc N N' hN hN' μ hv2
    obtain ⟨n, hn, n', hn', hnn⟩ := Submodule.mem_sup.mp hsp
    obtain ⟨y, hy, c, hc', hyc⟩ := Submodule.mem_sup.mp (hmult hn.2)
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hx : x = 0
    · subst hx
      have hnC : n = c := by rw [← hyc]; simp
      have hvN' : v ∈ N' := by
        rw [← hnn]; exact N'.add_mem (hCN' (hnC ▸ hc')) hn'.1
      exact hN't (hgen N' hN' hCN' hvN')
    · have hvN : v ∈ N := by
        have h1 : x • v ∈ N := by
          have : x • v = n - c := by rw [← hyc]; simp
          rw [this]; exact N.sub_mem hn.1 (hCN hc')
        have := N.smul_mem x⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hx, one_smul] at this
      exact hNt (hgen N hN hCN hvN)

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclicStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeAlg_of_cyclic_highest_weight : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  first | exact @GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | exact GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | (intros; apply GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic <;> assumption)
end
