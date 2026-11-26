module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertQRG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Reduce

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Partial
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Assemble
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ModQEqOneOfMemNormalizer
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

section Delta

variable {G : Type} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / (A.relIndex B : ℚ)

theorem idxRatio_eq_of_le (A B D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)
    (hA : D.relIndex A ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / (D.relIndex B : ℚ) := by
  have h1 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = D.relIndex A :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_left)
  have h2 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = D.relIndex B :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_right)
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hc0 : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply hA
    rw [← h1, h0, zero_mul]
  have hc : (D.relIndex (A ⊓ B) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  unfold idxRatio
  rw [← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hc]

theorem relIndex_inf_three_ne_zero {A B C L : Subgroup G} (hA : A.relIndex L ≠ 0)
    (hB : B.relIndex L ≠ 0) (hC : C.relIndex L ≠ 0) : (A ⊓ B ⊓ C).relIndex L ≠ 0 := by
  exact Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero hA hB) hC

theorem relIndex_self_ne_zero (A : Subgroup G) : A.relIndex A ≠ 0 := by
  rw [Subgroup.relIndex_self]
  exact one_ne_zero

theorem idxRatio_mul (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by
  have hDA := relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC
  have hDB := relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC
  rw [idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hDA,
    idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB,
    idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hDA,
    div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex A : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hDB)]

private theorem relIndex_map_of_injective (X Y : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]

theorem idxRatio_map (A B : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  unfold idxRatio
  rw [relIndex_map_of_injective _ _ f hf, relIndex_map_of_injective _ _ f hf]

theorem map_conj_mul' (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one' (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem relIndex_conj_conj_ne_zero (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    (K.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have h1 : K.map (MulAut.conj x).toMonoidHom =
      (K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [map_conj_mul', mul_inv_cancel_left]
  rw [h1, relIndex_map_of_injective _ _ _ (by intro a b h; simpa using h)]
  exact hK (y⁻¹ * x)

theorem relIndex_conj_right_ne_zero (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by
  have h := relIndex_conj_conj_ne_zero K hK 1 a
  rwa [map_conj_one'] at h

theorem dIdx_inv_eq (K : Subgroup G) (x : G) :
    dIdx K x⁻¹ = K.relIndex (K.map (MulAut.conj x).toMonoidHom) := by
  unfold dIdx
  rw [← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h),
    map_conj_mul', mul_inv_cancel, map_conj_one']

theorem modQ_eq_idxRatio (K : Subgroup G) (x : G) :
    modQ K x = idxRatio K (K.map (MulAut.conj x).toMonoidHom) := by
  unfold modQ idxRatio
  rw [dIdx_inv_eq]
  rfl

theorem dIdx_one (K : Subgroup G) : dIdx K 1 = 1 := by
  unfold dIdx
  rw [map_conj_one', Subgroup.relIndex_self]

theorem modQ_one (K : Subgroup G) : modQ K 1 = 1 := by
  unfold modQ
  simp [dIdx_one]

theorem modQ_mul (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (x * y) = modQ K x * modQ K y := by
  rw [modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio,
    ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom
      (by intro a b h; simpa using h), map_conj_mul']
  exact (idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom)
    (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x)
    (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm

end Delta

end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ModQOneOfClosure
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open Formalism.MainNotions.S

def ModQHom : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G), Commensurated K →
    (∀ x y : G, modQ K (x * y) = modQ K x * modQ K y) ∧ (∀ k ∈ K, modQ K k = 1) ∧
      (∀ x : G, modQ K x = 1 → dIdx K x = dIdx K x⁻¹)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

theorem mod_q_hom : ModQHom := by
  unfold ModQHom
  intro G _ K hK
  have hk1 : ∀ k ∈ K, dIdx K k = 1 := by
    intro k hk
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro y hy
    refine Subgroup.mem_map.2 ⟨k⁻¹ * y * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hy) hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨fun x y => modQ_mul K hK x y, fun k hk => ?_, fun x hx => ?_⟩
  · unfold modQ
    rw [hk1 k hk, hk1 k⁻¹ (K.inv_mem hk)]
    norm_num
  · unfold modQ at hx
    have hne : (dIdx K x⁻¹ : ℚ) ≠ 0 := by exact_mod_cast hK x⁻¹
    rw [div_eq_one_iff_eq hne] at hx
    exact_mod_cast hx

section Lift

variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))

def liftFn (hL : LiftU) (g : Uv I v) : I.Gf := Classical.choose (hL I v g g.2)

theorem liftFn_spec (hL : LiftU) (g : Uv I v) :
    matV I v ((liftFn I v hL g : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g ∧ SuppAt I v (liftFn I v hL g) :=
  Classical.choose_spec (hL I v g g.2)

theorem eq_liftFn (hL : LiftU) (hJ : MatVInj) (g : Uv I v) (y : I.Gf)
    (hy : matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = g) (hs : SuppAt I v y) :
    y = liftFn I v hL g := by
  apply hJ I
  intro w
  by_cases hw : w = v
  · rw [hw, hy, (liftFn_spec I v hL g).1]
  · rw [hs w hw, (liftFn_spec I v hL g).2 w hw]

def liftHom (hL : LiftU) (hJ : MatVInj) : Uv I v →* I.Gf where
  toFun := liftFn I v hL
  map_one' := by
    symm
    apply eq_liftFn I v hL hJ 1 1
    · simp
    · intro w _
      simp
  map_mul' := by
    intro g h
    symm
    apply eq_liftFn I v hL hJ (g * h)
    · simp only [Subgroup.coe_mul, map_mul, Subgroup.coe_mul]
      rw [(liftFn_spec I v hL g).1, (liftFn_spec I v hL h).1]
    · intro w hw
      simp only [Subgroup.coe_mul, map_mul]
      rw [(liftFn_spec I v hL g).2 w hw, (liftFn_spec I v hL h).2 w hw, one_mul]

theorem liftHom_apply (hL : LiftU) (hJ : MatVInj) (g : Uv I v) :
    liftHom I v hL hJ g = liftFn I v hL g := rfl

def chiV (hC : KComm) (hL : LiftU) (hJ : MatVInj) : Uv I v →* ℚ where
  toFun g := modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
  map_one' := by simp [modQ_one]
  map_mul' g h := by simp only [map_mul]; exact modQ_mul _ (hC I) _ _

private theorem modQ_eq_one_of_central {G : Type} [Group G] (K : Subgroup G) (y : G)
    (hy : ∀ x : G, y * x * y⁻¹ = x) : modQ K y = 1 := by
  have h1 : ∀ z : G, (∀ x : G, z * x * z⁻¹ = x) → dIdx K z = 1 := by
    intro z hz
    unfold dIdx
    rw [Subgroup.relIndex_eq_one]
    intro k hk
    exact Subgroup.mem_map.2 ⟨k, hk, by simp [MulAut.conj_apply, hz k]⟩
  have h2 : ∀ x : G, y⁻¹ * x * y⁻¹⁻¹ = x := by
    intro x
    have hx := hy x
    rw [inv_inv]
    calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [hx]
      _ = x := by group
  unfold modQ
  rw [h1 y hy, h1 y⁻¹ h2]
  norm_num

theorem chiV_props (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob) :
    (∀ g, 0 < chiV I v hC hL hJ g) ∧
    (∀ s : Uv I v, (∀ t : Uv I v, s * t = t * s) → chiV I v hC hL hJ s = 1) ∧
    (∀ s : Uv I v, (∃ m : ℕ, 1 ≤ m ∧
        (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)) →
        chiV I v hC hL hJ s = 1) := by
  have hM := mod_q_hom I.Gf (PI.AdIndexEq.Ksub I) (hC I)
  have hpos : ∀ g, 0 < chiV I v hC hL hJ g := by
    intro g
    show 0 < modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ g)
    unfold modQ
    apply div_pos
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
    · exact_mod_cast Nat.pos_of_ne_zero (hC I _)
  refine ⟨hpos, fun s hs => ?_, fun s hs => ?_⟩
  · show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ s) = 1
    have hyv : matV I v ((liftHom I v hL hJ s : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = s := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).1
    have hys : SuppAt I v (liftHom I v hL hJ s) := by
      rw [liftHom_apply]
      exact (liftFn_spec I v hL s).2
    apply modQ_eq_one_of_central
    intro x
    apply hJ I
    intro w
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    by_cases hw : w = v
    · rw [hw]
      have hc := congrArg Subtype.val (hs ⟨_, hU I v x⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_mk] at hc
      rw [hyv, hc, mul_inv_cancel_right]
    · rw [hys w hw, one_mul, inv_one, mul_one]
  · obtain ⟨m, hm, hsm⟩ := hs
    have hpow : chiV I v hC hL hJ (s ^ m) = 1 := by
      show modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ (s ^ m)) = 1
      apply hM.2.1
      refine (hK I _).2 fun w => ?_
      rw [liftHom_apply]
      by_cases hw : w = v
      · rw [hw, (liftFn_spec I v hL (s ^ m)).1]
        exact hsm
      · rw [(liftFn_spec I v hL (s ^ m)).2 w hw]
        exact (Kv I w).one_mem
    rw [map_pow] at hpow
    exact (pow_eq_one_iff_of_nonneg (hpos s).le (by omega)).1 hpow

theorem modQ_of_supp (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (y : I.Gf) (hy : SuppAt I v y) :
    modQ (PI.AdIndexEq.Ksub I) y = chiV I v hC hL hJ ⟨_, hU I v y⟩ := by
  show modQ (PI.AdIndexEq.Ksub I) y = modQ (PI.AdIndexEq.Ksub I) (liftHom I v hL hJ ⟨_, hU I v y⟩)
  rw [liftHom_apply, ← eq_liftFn I v hL hJ ⟨_, hU I v y⟩ y rfl hy]

end Lift

theorem locInert_of (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocInertChi) : LocInert := by
  unfold LocInert
  intro I v hv y hy
  obtain ⟨h1, h2, h3⟩ := chiV_props I v hC hL hJ hU hK
  rw [modQ_of_supp I v hC hL hJ hU y hy]
  exact h I v hv _ h1 h2 h3 _

theorem locSplit_of (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (h : LocSplitChi) : LocSplit := by
  unfold LocSplit
  intro I v hv y hy
  obtain ⟨h1, h2, h3⟩ := chiV_props I v hC hL hJ hU hK
  rw [modQ_of_supp I v hC hL hJ hU y hy]
  exact h I v hv _ h1 h2 h3 _

theorem indexEq_of_loc (hC : KComm) (hL : LiftU) (hJ : MatVInj) (hU : MatVU) (hK : KLocGlob)
    (hR : ReduceLoc) (hS : LocSplitChi) (hI : LocInertChi) : PI.AdIndexEq.IndexEq := by
  unfold PI.AdIndexEq.IndexEq
  intro I x
  have hM := mod_q_hom I.Gf (PI.AdIndexEq.Ksub I) (hC I)
  have hloc : ∀ v (y : I.Gf), SuppAt I v y → modQ (PI.AdIndexEq.Ksub I) y = 1 := by
    intro v y hy
    by_cases hv : IsFieldAt I v
    · exact locInert_of hC hL hJ hU hK hI I v hv y hy
    · exact locSplit_of hC hL hJ hU hK hS I v hv y hy
  have hxm := hR I x
  have hx : modQ (PI.AdIndexEq.Ksub I) x = 1 := by
    induction hxm using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨v, hv⟩ | hy
      · exact hloc v y hv
      · exact hM.2.1 y hy
    | one => exact modQ_one _
    | mul a b _ _ ha hb => rw [hM.1, ha, hb, one_mul]
    | inv a _ ha =>
      have h1 := hM.1 a a⁻¹
      rw [mul_inv_cancel, modQ_one, ha, one_mul] at h1
      exact h1.symm
  exact hM.2.2 x hx

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

theorem indexEq_of_open (hG : GLChi) (hQ : QReflPow) : PI.AdIndexEq.IndexEq :=
  indexEq_of_loc compact_commensurated lift_unitary' matrix_v_injective matrix_v_unitary compact_local_global reduce_local
    (locSplitChi_of hG) (locInertChi_of_qReflPow hQ)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPow
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

abbrev Av (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Type :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E

instance charZero_Fv (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    CharZero (v.adicCompletion I.F) :=
  charZero_of_injective_algebraMap (algebraMap I.F (v.adicCompletion I.F)).injective

def InR (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α z : Av I v) : Prop :=
  ∃ a b : v.adicCompletion I.F, a ∈ v.adicCompletionIntegers I.F ∧ b ∈ v.adicCompletionIntegers I.F ∧
    z = incL I v a + incL I v b * α

theorem inR_one (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v) : InR I v α 1 :=
  ⟨1, 0, one_mem _, zero_mem _, by simp⟩

theorem inR_self (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v) : InR I v α α :=
  ⟨0, 1, zero_mem _, one_mem _, by simp⟩

theorem inR_neg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v) {z : Av I v}
    (hz : InR I v α z) : InR I v α (-z) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hz
  exact ⟨-a, -b, neg_mem ha, neg_mem hb, by simp only [map_neg]; ring⟩

theorem inR_mul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) {x y : Av I v} (hx : InR I v α x) (hy : InR I v α y) :
    InR I v α (x * y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  obtain ⟨c, d, hc, hd, rfl⟩ := hy
  refine ⟨a * c - b * d, a * d + b * c + b * d * t, sub_mem (mul_mem ha hc) (mul_mem hb hd),
    add_mem (add_mem (mul_mem ha hd) (mul_mem hb hc)) (mul_mem (mul_mem hb hd) htO), ?_⟩
  simp only [map_sub, map_add (f := _), map_mul]
  linear_combination (incL I v b * incL I v d) * ht

theorem inR_pow (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) {x : Av I v} (hx : InR I v α x) (m : ℕ) :
    InR I v α (x ^ m) := by
  induction m with
  | zero => simpa using inR_one I v α
  | succ k ih => rw [pow_succ]; exact inR_mul I v α htO ht ih hx

theorem exists_pow_sub (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (ht : α * α = incL I v t * α - 1) (N : ℕ) (hN : 0 < N) :
    ∃ i j : ℕ, i < j ∧ ∃ w, InR I v α w ∧ α ^ j - α ^ i = incL I v N * w := by
  classical
  have hpow : ∀ m : ℕ, InR I v α (α ^ m) := fun m => inR_pow I v α htO ht (inR_self I v α) m
  choose a b ha hb hab using hpow
  have hNF : (N : v.adicCompletion I.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let NO : Set (v.adicCompletion I.F) :=
    (fun y => (N : v.adicCompletion I.F) * y) '' (v.adicCompletionIntegers I.F : Set _)
  have hOo : IsOpen (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)) :=
    Valued.isOpen_integer (R := v.adicCompletion I.F)
  have hNO : IsOpen NO := (Homeomorph.mulLeft₀ (N : v.adicCompletion I.F) hNF).isOpenMap _ hOo
  let U : v.adicCompletionIntegers I.F → Set (v.adicCompletion I.F) :=
    fun x => (fun y => y - (x : v.adicCompletion I.F)) ⁻¹' NO
  have hU : ∀ x, IsOpen (U x) := fun x => hNO.preimage (continuous_id.sub continuous_const)
  have hcov : (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)) ⊆ ⋃ x, U x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    exact ⟨0, zero_mem _, by simp⟩
  obtain ⟨T, hT⟩ := (PI.WAU.isCompact_Ov v).elim_finite_subcover U hU hcov
  have hsel : ∀ y ∈ (v.adicCompletionIntegers I.F : Set (v.adicCompletion I.F)),
      ∃ x : T, y ∈ U x := by
    intro y hy
    have := hT hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact ⟨⟨x, hx⟩, hyx⟩
  choose sel hsel' using hsel
  let f : ℕ → T × T := fun m => (sel (a m) (ha m), sel (b m) (hb m))
  have key : ∀ i j, f i = f j → ∃ w, InR I v α w ∧ α ^ j - α ^ i = incL I v N * w := by
    intro i j hij
    have h1 : sel (a i) (ha i) = sel (a j) (ha j) := congrArg Prod.fst hij
    have h2 : sel (b i) (hb i) = sel (b j) (hb j) := congrArg Prod.snd hij
    obtain ⟨p1, hp1, e1⟩ := hsel' (a i) (ha i)
    obtain ⟨p2, hp2, e2⟩ := hsel' (a j) (ha j)
    obtain ⟨q1, hq1, f1⟩ := hsel' (b i) (hb i)
    obtain ⟨q2, hq2, f2⟩ := hsel' (b j) (hb j)
    rw [h1] at e1
    rw [h2] at f1
    refine ⟨incL I v (p2 - p1) + incL I v (q2 - q1) * α,
      ⟨p2 - p1, q2 - q1, sub_mem hp2 hp1, sub_mem hq2 hq1, rfl⟩, ?_⟩
    have ea : a j - a i = (N : v.adicCompletion I.F) * (p2 - p1) := by
      simp only at e1 e2
      linear_combination e1 - e2
    have eb : b j - b i = (N : v.adicCompletion I.F) * (q2 - q1) := by
      simp only at f1 f2
      linear_combination f1 - f2
    have ea' := congrArg (incL I v) ea
    have eb' := congrArg (incL I v) eb
    simp only [map_sub, map_mul, map_natCast] at ea' eb' ⊢
    rw [hab j, hab i]
    linear_combination ea' + α * eb'
  obtain ⟨i, j, hne, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, key i j hf⟩
  · exact ⟨j, i, h, key j i hf.symm⟩

theorem exists_pow_near_one (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    {t : v.adicCompletion I.F} (htO : t ∈ v.adicCompletionIntegers I.F)
    (hsum : α + sigV I v α = incL I v t) (hα : sigV I v α * α = 1) (N : ℕ) (hN : 0 < N) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ w w', InR I v α w ∧ InR I v α w' ∧ α ^ m - 1 = incL I v N * w ∧
      sigV I v α ^ m - 1 = incL I v N * w' := by
  have ht : α * α = incL I v t * α - 1 := by
    rw [← hsum]
    linear_combination (-1 : Av I v) * hα
  have hsig : InR I v α (sigV I v α) :=
    ⟨t, -1, htO, neg_mem (one_mem _), by
      simp only [map_neg, map_one]
      linear_combination hsum⟩
  obtain ⟨i, j, hij, w0, hw0, e0⟩ := exists_pow_sub I v α htO ht N hN
  obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
  have hm : 1 ≤ m := by omega
  have hpi : sigV I v α ^ i * α ^ i = 1 := by rw [← mul_pow, hα, one_pow]
  have hpm : sigV I v α ^ m * α ^ m = 1 := by rw [← mul_pow, hα, one_pow]
  have e1 : α ^ m - 1 = incL I v N * (sigV I v α ^ i * w0) := by
    have : α ^ m - 1 = sigV I v α ^ i * (α ^ (i + m) - α ^ i) := by
      rw [pow_add]
      linear_combination (1 - α ^ m) * hpi
    rw [this, e0]
    ring
  refine ⟨m, hm, sigV I v α ^ i * w0, -(sigV I v α ^ m) * (sigV I v α ^ i * w0),
    inR_mul I v α htO ht (inR_pow I v α htO ht hsig i) hw0,
    inR_mul I v α htO ht (inR_neg I v α (inR_pow I v α htO ht hsig m))
      (inR_mul I v α htO ht (inR_pow I v α htO ht hsig i) hw0), e1, ?_⟩
  have : sigV I v α ^ m - 1 = -(sigV I v α ^ m) * (α ^ m - 1) := by
    linear_combination hpm
  rw [this, e1]
  ring

theorem adelic_bound (I : AutInst) (Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ w ∈ I.Lf, N • (Mx *ᵥ w) ∈ I.Lf := by
  obtain ⟨k, m, hm, hgen⟩ := PI.WAU.B.exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  obtain ⟨N, hN0, hN⟩ := PI.WAU.B.common_nat
    (fun j N => N • (Mx *ᵥ PI.WAU.B.ivec (F := I.F) (m j)) ∈ I.Lf)
    (fun j N M h => PI.WAU.B.nsmul_lam h M)
    (fun j => PI.WAU.B.exists_nat_vec (F := I.F) I.L_span _)
  refine ⟨N, hN0, fun w hw => ?_⟩
  have := PI.WAU.B.mulVec_lam hm hgen (N • Mx) (fun j => by rw [Matrix.smul_mulVec]; exact hN j) hw
  rwa [Matrix.smul_mulVec] at this

theorem loc_bound (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) {N : ℕ}
    (hM : ∀ w ∈ I.Lf, N • (Mx *ᵥ w) ∈ I.Lf) (z : Fin I.n → Av I v)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    N • (Mx.map (PI.FinKW.psiV I v).toRingHom *ᵥ z) ∈
      Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨w, hwv, hww⟩ := PI.FinKW.local_vector_lift I v z
  have hw : w ∈ I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I w (fun u => by
    by_cases hu : u = v
    · subst hu
      rwa [hwv]
    · rw [hww u hu]
      exact zero_mem _)
  have h1 := PI.FinKW.LocTo.mem_local_lattice_iff I _ (hM w hw) v
  rwa [vecV_nsmul, vecV_mulVec', hwv] at h1

theorem local_bound (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (Av I v)) :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • (M *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  classical
  have hlift (j : Fin I.n) :
      ∃ w : Fin I.n → I.E ⊗[I.F] Af I.F, PI.FinKW.vecV I v w = fun i => M i j := by
    obtain ⟨w, hw, _⟩ := PI.FinKW.local_vector_lift I v (fun i => M i j)
    exact ⟨w, hw⟩
  choose w hw using hlift
  let Mx : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun i j => w j i
  have hmap : Mx.map (PI.FinKW.psiV I v).toRingHom = M := by
    ext i j
    exact congrFun (hw j) i
  obtain ⟨N, hN, h⟩ := adelic_bound I Mx
  refine ⟨N, hN, fun z hz => ?_⟩
  simpa only [hmap] using loc_bound I v Mx h z hz

theorem incL_smul_mem (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) {a : v.adicCompletion I.F}
    (ha : a ∈ v.adicCompletionIntegers I.F) {y : Fin I.n → Av I v}
    (hy : y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    incL I v a • y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  have e : incL I v a • y = (⟨a, ha⟩ : v.adicCompletionIntegers I.F) • y := by
    rw [PI.FinKW.LocTo.ov_smul_vec]
    rfl
  rw [e]
  exact Submodule.smul_mem _ _ hy

theorem small_mem (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    (P : Matrix (Fin I.n) (Fin I.n) (Av I v)) (N : ℕ)
    (h1 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (h2 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • ((α • P) *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    {w : Av I v} (hw : InR I v α w) (z : Fin I.n → Av I v)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    (incL I v N * w) • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hw
  have e : (incL I v N * (incL I v a + incL I v b * α)) • (P *ᵥ z) =
      incL I v a • (N • (P *ᵥ z)) + incL I v b • (N • ((α • P) *ᵥ z)) := by
    rw [Matrix.smul_mulVec, ← Nat.cast_smul_eq_nsmul (Av I v), ← Nat.cast_smul_eq_nsmul (Av I v),
      smul_smul, smul_smul, smul_smul, ← add_smul, map_natCast]
    congr 1
    ring
  rw [e]
  exact add_mem (incL_smul_mem I v ha (h1 z hz)) (incL_smul_mem I v hb (h2 z hz))

theorem mul_qr {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n R) (hP : P * P = P) (x y : R) :
    (1 + x • P) * (1 + y • P) = 1 + (x + y + x * y) • P := by
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP,
    add_smul]
  rw [mul_comm x y]
  abel

theorem qr_pow {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (P : Matrix n n R) (hP : P * P = P) (c : R) (m : ℕ) :
    (1 + (c - 1) • P) ^ m = 1 + (c ^ m - 1) • P := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_qr P hP]
    congr 2
    ring

theorem qReflPow_of (hT : TraceInt) : QReflPow := by
  intro I v hv s hs
  obtain ⟨P, α, hP, hα, hsP⟩ := hs
  obtain ⟨t, htO, hsum⟩ := hT I v hv α hα
  obtain ⟨N1, hN1, hb1⟩ := local_bound I v P
  obtain ⟨N2, hN2, hb2⟩ := local_bound I v (α • P)
  have h1 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      (N1 * N2) • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
    intro z hz
    rw [mul_comm, mul_smul]
    exact nsmul_mem (hb1 z hz) N2
  have h2 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      (N1 * N2) • ((α • P) *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
    intro z hz
    rw [mul_smul]
    exact nsmul_mem (hb2 z hz) N1
  obtain ⟨m, hm, w, w', hw, hw', e1, e2⟩ :=
    exists_pow_near_one I v α htO hsum hα (N1 * N2) (Nat.mul_pos hN1 hN2)
  refine ⟨m, hm, ?_⟩
  have hmat : (((s ^ m : Uv I v) : GL (Fin I.n) (Av I v)) : Matrix (Fin I.n) (Fin I.n) (Av I v)) =
      1 + (α ^ m - 1) • P := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hsP, qr_pow P hP α m]
  have hpm : sigV I v α ^ m * α ^ m = 1 := by rw [← mul_pow, hα, one_pow]
  have hinv : (1 + (sigV I v α ^ m - 1) • P) * (1 + (α ^ m - 1) • P) = 1 := by
    rw [mul_qr P hP]
    have : sigV I v α ^ m - 1 + (α ^ m - 1) + (sigV I v α ^ m - 1) * (α ^ m - 1) = 0 := by
      linear_combination hpm
    rw [this, zero_smul, add_zero]
  have hS : ∀ y, (1 + (α ^ m - 1) • P) *ᵥ y = y + (incL I v (N1 * N2 : ℕ) * w) • (P *ᵥ y) := by
    intro y
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, e1]
  have hT' : ∀ y, (1 + (sigV I v α ^ m - 1) • P) *ᵥ y =
      y + (incL I v (N1 * N2 : ℕ) * w') • (P *ᵥ y) := by
    intro y
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, e2]
  intro z
  rw [hmat]
  constructor
  · intro hz
    rw [hS]
    exact add_mem hz (small_mem I v α P (N1 * N2) h1 h2 hw z hz)
  · intro hz
    have := add_mem hz (small_mem I v α P (N1 * N2) h1 h2 hw' _ hz)
    rwa [← hT', Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.GLDelta
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

namespace GLChiPf

open Matrix

variable {k : Type} [Field k] {n : ℕ}

def glOf (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  ⟨M, M⁻¹, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr h),
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr h)⟩

theorem chi_conj (χ : GL (Fin n) k →* ℚ) (s x : GL (Fin n) k) : χ (s * x * s⁻¹) = χ x := by
  rw [map_mul, map_mul, mul_comm (χ s), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem diag_transvection [CharZero k] (i j : Fin n) (hij : i ≠ j) (c : k) :
    diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j (2 * c) := by
  ext a b
  simp only [mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Function.update_apply, Pi.one_apply, eq_comm (a := i) (b := a),
    eq_comm (a := j) (b := b)]
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>
    by_cases hjb : b = j <;> simp_all

theorem chi_transvection [CharZero k] (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (t : TransvectionStruct (Fin n) k) (h : t.toMatrix.det ≠ 0) : χ (glOf t.toMatrix h) = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have key : ∀ a : k, a ≠ 0 → diagonal (Function.update (1 : Fin n → k) i a) *
      diagonal (Function.update (1 : Fin n → k) i a⁻¹) = 1 := by
    intro a ha
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx; simp [ha]
    · simp [Function.update_apply, hx]
  have key' : diagonal (Function.update (1 : Fin n → k) i 2⁻¹) *
      diagonal (Function.update (1 : Fin n → k) i 2) = 1 := by
    simpa using key 2⁻¹ (inv_ne_zero h2)
  let s : GL (Fin n) k := ⟨diagonal (Function.update (1 : Fin n → k) i 2),
    diagonal (Function.update (1 : Fin n → k) i 2⁻¹), key 2 h2, key'⟩
  have hsq : s * glOf _ h * s⁻¹ = glOf _ h * glOf _ h := by
    apply Units.ext
    change diagonal (Function.update (1 : Fin n → k) i 2) * transvection i j c *
      diagonal (Function.update (1 : Fin n → k) i 2⁻¹) = transvection i j c * transvection i j c
    rw [diag_transvection i j hij c, two_mul]
    symm
    apply transvection_mul_transvection_same
    all_goals exact hij
  have e := chi_conj χ s (glOf _ h)
  rw [hsq, map_mul] at e
  exact mul_left_cancel₀ (ne_of_gt (hpos _)) (e.trans (mul_one _).symm)

def dU : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem dU_val (D : Fin n → kˣ) :
    ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (D i : k)) := rfl

theorem perm_conj (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (M : Matrix (Fin n) (Fin n) k) :
    σ.toPEquiv.toMatrix * M * σ.toPEquiv.toMatrix = M.submatrix σ σ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hσ]
  rfl

theorem perm_sq (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) :
    σ.toPEquiv.toMatrix * σ.toPEquiv.toMatrix = (1 : Matrix (Fin n) (Fin n) k) := by
  have e := perm_conj σ hσ (1 : Matrix (Fin n) (Fin n) k)
  rwa [Matrix.mul_one, Matrix.submatrix_one_equiv] at e

def sU (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.toPEquiv.toMatrix, perm_sq σ hσ, perm_sq σ hσ⟩

theorem sU_conj_dU (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (D : Fin n → kˣ) :
    sU σ hσ * dU D * (sU σ hσ)⁻¹ = dU (D ∘ σ) := by
  apply Units.ext
  show σ.toPEquiv.toMatrix * ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * σ.toPEquiv.toMatrix =
    ((dU (D ∘ σ) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [dU_val, dU_val, perm_conj σ hσ, Matrix.submatrix_diagonal_equiv]
  rfl

theorem mulSingle_comp_swap (i j : Fin n) (d : kˣ) :
    (Pi.mulSingle i d : Fin n → kˣ) ∘ (Equiv.swap i j) = Pi.mulSingle j d := by
  funext x
  simp only [Function.comp_apply]
  by_cases hxj : x = j
  · subst hxj; simp
  · by_cases hxi : x = i
    · subst hxi
      rw [Equiv.swap_apply_left, Pi.mulSingle_eq_of_ne (Ne.symm hxj), Pi.mulSingle_eq_of_ne hxj]
    · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj, Pi.mulSingle_eq_of_ne hxi, Pi.mulSingle_eq_of_ne hxj]

theorem chi_single_eq (χ : GL (Fin n) k →* ℚ) (i j : Fin n) (d : kˣ) :
    χ (dU (Pi.mulSingle i d)) = χ (dU (Pi.mulSingle j d)) := by
  have h := chi_conj χ (sU (Equiv.swap i j) (Equiv.symm_swap i j)) (dU (Pi.mulSingle i d))
  rw [sU_conj_dU, mulSingle_comp_swap] at h
  exact h.symm

theorem chi_single (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (i : Fin n) (d : kˣ) : χ (dU (Pi.mulSingle i d)) = 1 := by
  have hn : n ≠ 0 := by rintro rfl; exact i.elim0
  have hsc : Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d = dU (fun _ => d) := by
    apply Units.ext
    rw [dU_val]
    ext a b
    simp [Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
  have hprod : (fun _ : Fin n => d) = ∏ l, Pi.mulSingle l d := (Finset.univ_prod_mulSingle (fun _ => d)).symm
  have h1 : (χ.comp dU) (fun _ => d) = 1 := by rw [MonoidHom.comp_apply, ← hsc]; exact hz d
  rw [hprod, map_prod] at h1
  simp only [MonoidHom.comp_apply] at h1
  have h2 : ∏ l : Fin n, χ (dU (Pi.mulSingle l d)) = ∏ _l : Fin n, χ (dU (Pi.mulSingle i d)) :=
    Finset.prod_congr rfl (fun l _ => chi_single_eq χ l i d)
  rw [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact (pow_eq_one_iff_of_nonneg (hpos _).le hn).mp h1

theorem chi_diag (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (D : Fin n → kˣ) : χ (dU D) = 1 := by
  have e : χ (dU D) = (χ.comp dU) (∏ i, Pi.mulSingle i (D i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod]
  exact Finset.prod_eq_one (fun i _ => chi_single χ hpos hz i (D i))

end GLChiPf

open GLChiPf in
theorem gl_character : GLChi := by
  intro k _ _ n χ hpos hz g
  obtain ⟨L, L', D, hM⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin n) (Fin n) k)
  have htd : ∀ t : Matrix.TransvectionStruct (Fin n) k, t.toMatrix.det ≠ 0 := fun t => by
    rw [t.det]; exact one_ne_zero
  have lu_val : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (((l.map fun t => glOf t.toMatrix (htd t)).prod : Matrix.GeneralLinearGroup (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = (l.map Matrix.TransvectionStruct.toMatrix).prod := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul, ih]
      try rfl
  have lu_chi : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      χ ((l.map fun t => glOf t.toMatrix (htd t)).prod) = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, List.prod_cons, map_mul, ih, chi_transvection χ hpos t (htd t), one_mul]
  have det_l : ∀ l : List (Matrix.TransvectionStruct (Fin n) k),
      (l.map Matrix.TransvectionStruct.toMatrix).prod.det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => rw [List.map_cons, List.prod_cons, Matrix.det_mul, t.det, ih, one_mul]
  have hg0 : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero
  have hdet : (g : Matrix (Fin n) (Fin n) k).det = ∏ j, D j := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, det_l, det_l, Matrix.det_diagonal, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i
    rw [hdet] at hg0
    exact Finset.prod_ne_zero_iff.mp hg0 i (Finset.mem_univ i)
  have hg : g = (L.map fun t => glOf t.toMatrix (htd t)).prod * dU (fun i => Units.mk0 (D i) (hD i)) *
      (L'.map fun t => glOf t.toMatrix (htd t)).prod := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, lu_val, lu_val, dU_val]
    exact hM
  rw [hg, map_mul, map_mul, lu_chi, lu_chi, chi_diag χ hpos hz, one_mul, one_mul]

end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

theorem indexEq_of_traceInt (h : TraceInt) : PI.AdIndexEq.IndexEq :=
  indexEq_of_open gl_character (qReflPow_of h)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
