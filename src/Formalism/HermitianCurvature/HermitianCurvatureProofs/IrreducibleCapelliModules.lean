module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarSumLemmas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BorderedDeterminants
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BranchingSystems

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightMonotonicity
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

section Dual

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem dm_mul (f g : Module.End ℂ V) : (f * g).dualMap = g.dualMap * f.dualMap := by
  ext φ x
  rfl

theorem dm_add (f g : Module.End ℂ V) : (f + g).dualMap = f.dualMap + g.dualMap := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_sub (f g : Module.End ℂ V) : (f - g).dualMap = f.dualMap - g.dualMap := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_zero : (0 : Module.End ℂ V).dualMap = 0 := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_one : (1 : Module.End ℂ V).dualMap = 1 := by
  ext φ x
  rfl

theorem dm_sum {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ V) :
    (∑ i ∈ s, f i).dualMap = ∑ i ∈ s, (f i).dualMap := by
  ext φ x
  set_option synthInstance.maxHeartbeats 100000 in
    simp [LinearMap.dualMap_apply, LinearMap.sum_apply, map_sum]

theorem dm_intCast (z : ℤ) : ((z : Module.End ℂ V)).dualMap = (z : Module.End ℂ (Module.Dual ℂ V)) := by
  ext φ x
  simp [LinearMap.dualMap_apply]

theorem dm_algebraMap (u : ℂ) :
    (algebraMap ℂ (Module.End ℂ V) u).dualMap = algebraMap ℂ (Module.End ℂ (Module.Dual ℂ V)) u := by
  ext φ x
  simp [LinearMap.dualMap_apply, Module.algebraMap_end_apply]

theorem dm_ofFn_prod : ∀ {t : ℕ} (f : Fin t → Module.End ℂ V),
    ((List.ofFn f).prod).dualMap = (List.ofFn fun i => (f i.rev).dualMap).prod
  | 0, f => by simp [dm_one]
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, dm_mul, dm_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => (f i.rev).dualMap), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

theorem glRel_dualE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) : GlRel (dualE E) := by
  intro a b c d
  simp only [dualE]
  rw [← dm_mul, ← dm_mul, ← dm_sub, hE d c b a, dm_sub]
  split_ifs <;> simp_all [dm_zero]

theorem Tm_dualE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (u : ℂ) (a b : Fin n) :
    Tm (dualE E) u a b = (Tm E u b a).dualMap := by
  simp only [Tm, dualE, dm_add]
  congr 1
  by_cases h : a = b
  · subst h; simp [dm_algebraMap]
  · rw [if_neg h, if_neg (Ne.symm h), dm_zero]

theorem arg_rev {t : ℕ} (w : ℂ) (j : Fin t) :
    w - (t : ℂ) + 1 + (((Fin.rev j : Fin t) : ℕ) : ℂ) = w - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring

theorem dm_qminorRow {n t : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin t → Fin n) (w : ℂ) :
    (qminorRow E (b ∘ Fin.rev) (a ∘ Fin.rev) w).dualMap = qminor (dualE E) a b w := by
  unfold qminor qminorRow
  rw [dm_sum]
  refine Fintype.sum_equiv (PI.UnitaryGroupMassFormula.QmStar.conjRev t) _ _ (fun σ => ?_)
  rw [dm_mul, dm_intCast, dm_ofFn_prod, PI.UnitaryGroupMassFormula.QmStar.sign_conjRev, Int.cast_comm]
  simp only [Function.comp_apply, PI.UnitaryGroupMassFormula.QmStar.conjRev_apply, Fin.rev_rev, arg_rev, Tm_dualE]

end Dual

section Weight

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_prod (H : Module.End ℂ V) : ∀ {n : ℕ} (g : Fin n → Module.End ℂ V) (e : Fin n → ℂ),
    (∀ x, H * g x = g x * H + e x • g x) →
    H * (List.ofFn g).prod = (List.ofFn g).prod * H + (∑ x, e x) • (List.ofFn g).prod
  | 0, g, e, _ => by simp
  | n + 1, g, e, h => by
    have ih := comm_prod H (n := n) (fun x => g x.succ) (fun x => e x.succ) (fun x => h x.succ)
    rw [List.ofFn_succ, List.prod_cons, ← mul_assoc, h 0, add_mul, mul_assoc, ih, Fin.sum_univ_succ, mul_add,
      add_smul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

theorem comm_pow (H f : Module.End ℂ V) (d : ℂ) (h : H * f = f * H + d • f) (k : ℕ) :
    H * f ^ k = f ^ k * H + ((k : ℂ) * d) • f ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc, h]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, Nat.cast_succ, add_smul, one_mul]
    abel

theorem comm_mono (H : Module.End ℂ V) {n : ℕ} (f : Fin n → Module.End ℂ V) (d : Fin n → ℂ)
    (h : ∀ x, H * f x = f x * H + d x • f x) (a : Fin n → ℕ) :
    H * mono f a = mono f a * H + (∑ x, (a x : ℂ) * d x) • mono f a := by
  unfold mono
  exact comm_prod H (fun x => f x ^ a x) (fun x => (a x : ℂ) * d x) (fun x => comm_pow H (f x) (d x) (h x) (a x))

theorem weight_mono {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hE : GlRel E) (c : Fin n) (m : ℂ)
    (w : V) (hw : E c.castSucc c.castSucc w = m • w) (a : Fin n → ℕ) :
    E c.castSucc c.castSucc (mono (etaK E) a w) = (m + (a c : ℂ)) • mono (etaK E) a w := by
  have hd : ∀ x, E c.castSucc c.castSucc * etaK E x =
      etaK E x * E c.castSucc c.castSucc + (if x = c then (1 : ℂ) else 0) • etaK E x := by
    intro x
    have h := hE c.castSucc c.castSucc x.castSucc (Fin.last n)
    rw [if_neg (Fin.castSucc_lt_last c).ne', sub_zero] at h
    by_cases hx : x = c
    · subst hx
      rw [if_pos rfl] at h
      rw [if_pos rfl, one_smul]
      exact eq_add_of_sub_eq' h
    · rw [if_neg (fun e => hx (Fin.castSucc_injective _ e).symm)] at h
      rw [if_neg hx, zero_smul, add_zero]
      exact sub_eq_zero.mp h
  have hc := congrArg (fun g : Module.End ℂ V => g w) (comm_mono _ (etaK E) _ hd a)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hw, map_smul] at hc
  rw [hc, add_smul]
  congr 2
  simp

end Weight

end Formalism.FourierDecayAlt.P.DegreeMapArithmetic

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr DegreeMapArithmetic

theorem dual_minor : Qr.DualMinor := by
  intro V _ _ n E hE
  refine ⟨glRel_dualE E hE, fun t a b w => ?_⟩
  rw [← dm_qminorRow, ← line_form_of_minor _ n t E hE, PI.UnitaryGroupMassFormula.QmStar.qminor_rev_rev E hE]

theorem qr_multOne_of (hS : Qr.ExistsSingMax) (hD : Qr.DualMinor) (hP : Qr.SpanSing) : Qr.MultOne := by
  intro V _ _ _ n E μ w₁ w₂ hE hIrr h1 h2 hw1
  have : Nontrivial V := hIrr.1
  obtain ⟨ν, ξ₀, -, hξ0, hHW, -⟩ := hS (Module.Dual ℂ V) (n + 1) (dualE E) (hD V (n + 1) E hE).1 ⊤
    (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
  have hdiag : ∀ (a : Fin (n + 1)) (v : V), ξ₀ (E a a v) = ν a * ξ₀ v := by
    intro a v
    have := congrArg (fun ζ : Module.Dual ℂ V => ζ v) (hHW.1 a)
    simpa [dualE, LinearMap.dualMap_apply] using this
  have hlow : ∀ a b : Fin (n + 1), b < a → ∀ v, ξ₀ (E a b v) = 0 := by
    intro a b hab v
    have := congrArg (fun ζ : Module.Dual ℂ V => ζ v) (hHW.2 b a hab)
    simpa [dualE, LinearMap.dualMap_apply] using this
  have key : ∀ w, IsHW (subA E) μ w → ∀ a : Fin n → ℕ, ξ₀ (mono (etaK E) a w) ≠ 0 →
      ∀ c, (a c : ℂ) = ν c.castSucc - μ c := by
    intro w hw a ha c
    have e1 := hdiag c.castSucc (mono (etaK E) a w)
    rw [weight_mono E hE c (μ c) w (hw.1 c) a, map_smul, smul_eq_mul] at e1
    have := mul_right_cancel₀ ha e1
    rw [← this]; ring
  have hex : ∃ a₀ : Fin n → ℕ, ξ₀ (mono (etaK E) a₀ w₁) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw1 (hP V n E ξ₀ μ w₁ hE hIrr hξ0 hlow h1 hcon)
  obtain ⟨a₀, ha₀⟩ := hex
  refine ⟨ξ₀ (mono (etaK E) a₀ w₂) / ξ₀ (mono (etaK E) a₀ w₁), ?_⟩
  set c := ξ₀ (mono (etaK E) a₀ w₂) / ξ₀ (mono (etaK E) a₀ w₁) with hc
  have hw : IsHW (subA E) μ (w₂ - c • w₁) := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · rw [map_sub, map_smul, h1.1 a, h2.1 a, smul_sub, smul_comm]
    · rw [map_sub, map_smul, h1.2 a b hab, h2.2 a b hab, smul_zero, sub_zero]
  have hz : w₂ - c • w₁ = 0 := by
    refine hP V n E ξ₀ μ _ hE hIrr hξ0 hlow hw (fun a => ?_)
    by_contra hne
    have haa : a = a₀ := by
      funext x
      have e1 := key _ hw a hne x
      have e2 := key _ h1 a₀ ha₀ x
      exact Nat.cast_injective (R := ℂ) (e1.trans e2.symm)
    subst haa
    apply hne
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ ha₀, sub_self]
  exact sub_eq_zero.mp hz

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictBoxOrder
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.StrictBoxOrder

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem box_strictAnti {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) : StrictAnti M := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ k =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have h1 := (h i.succ).2
    have h2 := (h i.castSucc).1
    rw [Fin.succ_castSucc] at h2
    exact lt_of_le_of_lt h1 h2

theorem sdec_shf {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (h : StrictAnti M) : SDec (shf β M) := by
  intro a b hab
  have h1 := h hab
  refine ⟨(M a - M b - 1).toNat, ?_⟩
  simp only [shf]
  have h2 : ((M a - M b - 1).toNat : ℤ) = M a - M b - 1 := Int.toNat_of_nonneg (by omega)
  have h3 : (((M a - M b - 1).toNat : ℕ) : ℂ) = ((M a - M b - 1 : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, h2]
  rw [h3]
  push_cast
  ring

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsWt {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Prop := ∀ c, ∃ t : ℂ, E c c v = t • v

theorem isWt_vec {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hy : IsVec E y)
    (x : Fin n) (v : V) (h : IsWt E v) : IsWt E (y x v) := by
  intro c
  obtain ⟨t, ht⟩ := h c
  have e := congrArg (fun g : Module.End ℂ V => g v) (hy c c x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, ht, map_smul] at e
  by_cases hcx : c = x
  · subst hcx
    rw [if_pos rfl, LinearMap.neg_apply, sub_eq_iff_eq_add] at e
    refine ⟨t - 1, ?_⟩
    rw [e, sub_smul, one_smul]
    abel
  · rw [if_neg hcx, LinearMap.zero_apply, sub_eq_zero] at e
    exact ⟨t, e⟩

theorem list_prod_pres (P : V → Prop) (l : List (Module.End ℂ V)) (h : ∀ f ∈ l, ∀ v, P v → P (f v)) :
    ∀ v, P v → P (l.prod v) := by
  induction l with
  | nil => intro v hv; simpa using hv
  | cons f l ih =>
    intro v hv
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f (by simp) _ (ih (fun g hg => h g (by simp [hg])) v hv)

theorem pow_pres (P : V → Prop) (f : Module.End ℂ V) (h : ∀ v, P v → P (f v)) (k : ℕ) :
    ∀ v, P v → P ((f ^ k) v) := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (h v hv)

theorem isWt_mono {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hy : IsVec E y)
    (a : Fin n → ℕ) (v : V) (h : IsWt E v) : IsWt E (mono y a v) := by
  unfold mono
  refine list_prod_pres (IsWt E) _ (fun f hf => ?_) v h
  simp only [List.mem_ofFn, Set.mem_range] at hf
  obtain ⟨x, rfl⟩ := hf
  exact pow_pres (IsWt E) (y x) (fun w hw => isWt_vec hy x w hw) (a x)

theorem core (hESM : ExistsSingMax) (hCS : CapSing) (hSR : SubRel) (hTW : TopWeightSing) (hDM : DualMinor)
    (hST : SpanTop) (hMO : MultOne) [FiniteDimensional ℂ V] {n : ℕ}
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (hgl : GlRel E) (hirr : Irr E)
    (m : Fin n → ℂ) (hm : SDec m) (O : Submodule ℂ V) (hO : Stab (subA E) O)
    (hS : Stab (subA E) (CapSp (subA E) m)) (hOq : ∀ w, ∀ v ∈ O, qdet (subA E) w v ∈ O)
    (hdis : Disjoint (CapSp (subA E) m) O) (htop : CapSp (subA E) m ⊔ O = ⊤)
    (S' : Submodule ℂ V) (hS'le : S' ≤ CapSp (subA E) m) (hS' : Stab (subA E) S') (hne : S' ≠ ⊥) :
    S' = CapSp (subA E) m := by
  by_contra hcon
  obtain ⟨hgl', -, hvec, -, -, -⟩ := hSR _ n E hgl
  obtain ⟨hglD, hmin⟩ := hDM V n (subA E) hgl'
  have hdis' := Submodule.disjoint_def.1 hdis

  have hT : S' ⊔ O ≠ ⊤ := by
    intro hT
    apply hcon
    apply le_antisymm hS'le
    intro s hs
    have h1 : s ∈ S' ⊔ O := by rw [hT]; trivial
    obtain ⟨s', hs', t, ht, rfl⟩ := Submodule.mem_sup.1 h1
    have ht2 : t ∈ CapSp (subA E) m := by
      have h2 := (CapSp (subA E) m).sub_mem hs (hS'le hs')
      simpa using h2
    rw [hdis' t ht2 ht, add_zero]; exact hs'
  have hTstab : Stab (subA E) (S' ⊔ O) := by
    intro a b v hv
    obtain ⟨s', hs', t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hS' a b _ hs') (hO a b _ ht)

  have hAnn : (S' ⊔ O).dualAnnihilator ≠ ⊥ := by
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hT) inferInstance
    intro hbot
    apply hf0
    have h1 : f ∈ (S' ⊔ O).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      have h2 : f w ∈ (S' ⊔ O).map f := Submodule.mem_map_of_mem hw
      rw [hf] at h2
      exact (Submodule.mem_bot ℂ).1 h2
    rw [hbot] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  have hAnnStab : Stab (dualE (subA E)) (S' ⊔ O).dualAnnihilator := by
    intro a b ξ hξ
    rw [Submodule.mem_dualAnnihilator] at hξ ⊢
    intro v hv
    exact hξ _ (hTstab b a v hv)
  obtain ⟨μd, ξ, hξA, hξ0, hξHW, -⟩ := hESM (Module.Dual ℂ V) n (dualE (subA E)) hglD _ hAnnStab hAnn
  rw [Submodule.mem_dualAnnihilator] at hξA

  have hξC : ξ ∈ CapSp (dualE (subA E)) m := by
    rw [mem_CapSp]; intro w
    have h1 : qdet (dualE (subA E)) w = (qdet (subA E) w).dualMap := hmin n id id w
    rw [h1]
    ext v
    have hv : v ∈ CapSp (subA E) m ⊔ O := by rw [htop]; trivial
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hv
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, map_add (f := _)]
    rw [mem_CapSp.1 hs w, hξA _ (Submodule.mem_sup_right (hOq w t ht)), hξA t (Submodule.mem_sup_right ht)]
    simp
  have hμ : ∀ j, μd j = m j + ((j : ℕ) : ℂ) :=
    (hCS (Module.Dual ℂ V) n (dualE (subA E)) m hglD
      (fun hb => hξ0 ((Submodule.mem_bot ℂ).1 (hb ▸ hξC)))).2 hm μd ξ hξC hξ0 hξHW

  have := hirr.1
  obtain ⟨ν, v₀, -, hv₀, hv₀HW, -⟩ := hESM V (n + 1) E hgl ⊤ (fun _ _ _ _ => trivial) top_ne_bot
  have hex : ∃ a, ξ (mono (yK E) a v₀) ≠ 0 := by
    by_contra hno
    push Not at hno
    refine hξ0 (hST V n E ν v₀ hgl hirr hv₀HW hv₀ ξ (fun a b hab v => ?_) hno)
    exact LinearMap.congr_fun (hξHW.2 b a hab) v
  obtain ⟨a, ha⟩ := hex
  have hv₀W : IsWt (subA E) v₀ := fun c => ⟨ν c.castSucc, hv₀HW.1 c.castSucc⟩
  have hxW : IsWt (subA E) (mono (yK E) a v₀) := isWt_mono hvec a v₀ hv₀W
  generalize mono (yK E) a v₀ = x at ha hxW
  have hxμ : ∀ c, subA E c c x = (m c + ((c : ℕ) : ℂ)) • x := by
    intro c
    obtain ⟨t, ht⟩ := hxW c
    have h1 : ξ (subA E c c x) = μd c * ξ x := LinearMap.congr_fun (hξHW.1 c) x
    rw [ht, map_smul, smul_eq_mul] at h1
    rw [ht, mul_right_cancel₀ ha h1, hμ]

  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (show x ∈ CapSp (subA E) m ⊔ O by rw [htop]; trivial)
  have hξs : ξ s ≠ 0 := by
    rw [← hst, map_add (f := _), hξA t (Submodule.mem_sup_right ht), add_zero] at ha
    exact ha
  have hsμ : ∀ c, subA E c c s = (m c + ((c : ℕ) : ℂ)) • s := by
    intro c
    have h1 := hxμ c
    rw [← hst, map_add (f := _), smul_add] at h1
    have h2 : subA E c c s - (m c + ((c : ℕ) : ℂ)) • s = -(subA E c c t - (m c + ((c : ℕ) : ℂ)) • t) := by
      rw [eq_neg_iff_add_eq_zero, ← sub_eq_zero.2 h1]
      abel
    have h3 : subA E c c s - (m c + ((c : ℕ) : ℂ)) • s ∈ CapSp (subA E) m :=
      Submodule.sub_mem _ (hS c c s hs) (Submodule.smul_mem _ _ hs)
    have h4 : subA E c c s - (m c + ((c : ℕ) : ℂ)) • s ∈ O := by
      rw [h2]
      exact O.neg_mem (O.sub_mem (hO c c t ht) (O.smul_mem _ ht))
    exact sub_eq_zero.1 (hdis' _ h3 h4)
  have hsHW := hTW V n (subA E) m hgl' hm s hs hsμ

  obtain ⟨ν', v', hv'S, hv'0, hv'HW, -⟩ := hESM V n (subA E) hgl' S' hS' hne
  have hν' := (hCS V n (subA E) m hgl'
    (fun hb => hv'0 ((Submodule.mem_bot ℂ).1 (hb ▸ hS'le hv'S)))).2 hm ν' v' (hS'le hv'S) hv'0 hv'HW
  have hν'' : ν' = fun a => m a + ((a : ℕ) : ℂ) := funext hν'
  rw [hν''] at hv'HW
  obtain ⟨c, hc⟩ := hMO V n E _ v' s hgl hirr hv'HW hsHW hv'0
  apply hξs
  rw [hc, map_smul, hξA v' (Submodule.mem_sup_left hv'S), smul_zero]

theorem sup_pres {ι : Type} (f : Module.End ℂ V) (F : ι → Submodule ℂ V) (p : ι → Prop)
    (h : ∀ j, ∀ v ∈ F j, f v ∈ F j) : ∀ v ∈ ⨆ (j) (_ : p j), F j, f v ∈ ⨆ (j) (_ : p j), F j := by
  have hle : (⨆ (j) (_ : p j), F j) ≤ (⨆ (j) (_ : p j), F j).comap f := by
    refine iSup₂_le (fun j hj => ?_)
    intro v hv
    exact (le_iSup₂ (f := fun j (_ : p j) => F j) j hj) (h j v hv)
  intro v hv
  exact hle hv

theorem box_indep (hCI : CapIndep) {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ) :
    iSupIndep (fun M : {M : Fin n → ℤ // Box L M} => CapSp E (shf β M.1)) := by
  have h := (hCI V n E β).comp
    (f := fun M : {M : Fin n → ℤ // Box L M} => (⟨M.1, box_strictAnti M.2⟩ : {M : Fin n → ℤ // StrictAnti M}))
    (by
      intro M M' hMM
      exact Subtype.ext (congrArg (fun z : {M : Fin n → ℤ // StrictAnti M} => z.1) hMM))
  exact h

end Formalism.FourierDecayAlt.P.StrictBoxOrder

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem qr_irredCap_of : Qr.ExistsSingMax → Qr.CapSing → Qr.CapStab → Qr.SubRel → Qr.TopWeightSing → Qr.DualMinor →
    Qr.SpanTop → Qr.MultOne → Qr.Decomp → Qr.CapIndep → Qr.IrredCap := by
  intro hESM hCS hCSt hSR hTW hDM hST hMO hDec hCI V _ _ _ n E β L hyp M hM S' hS'le hS'
  by_cases hne : S' = ⊥
  · exact Or.inl hne
  right
  have hgl' : GlRel (subA E) := (hSR _ n E hyp.gl).1
  have hind := StrictBoxOrder.box_indep hCI (subA E) β L
  have hsup : (⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA E) (shf β M.1)) = ⊤ := by
    rw [← (hDec V n E β L hyp).2, iSup_subtype]
  rw [iSup_split_single _ (⟨M, hM⟩ : {M : Fin n → ℤ // Box L M})] at hsup
  refine StrictBoxOrder.core hESM hCS hSR hTW hDM hST hMO E hyp.gl hyp.irr (shf β M) (StrictBoxOrder.sdec_shf β (StrictBoxOrder.box_strictAnti hM))
    (⨆ (j : {M : Fin n → ℤ // Box L M}) (_ : j ≠ ⟨M, hM⟩), CapSp (subA E) (shf β j.1)) ?_
    (hCSt V n (subA E) (shf β M) hgl').1 ?_ (hind ⟨M, hM⟩) hsup S' hS'le hS' hne
  · intro a b
    exact StrictBoxOrder.sup_pres (subA E a b) _ _ fun j v hv => (hCSt V n (subA E) (shf β j.1) hgl').1 a b v hv
  · intro w
    refine StrictBoxOrder.sup_pres (qdet (subA E) w) _ _ fun j v hv => ?_
    rw [mem_CapSp.1 hv w]
    exact Submodule.smul_mem _ _ hv

theorem qr_branchingAlg_of : Qr.Decomp → Qr.CapIndep → Qr.IrredCap → Qr.BranchingAlg := by
  intro hD hCI hIC V _ _ _ n E β L H
  obtain ⟨hne, htop⟩ := hD V n E β L H
  refine ⟨?_, fun M => ⟨hne M.1 M.2, fun S' hS' hst => hIC V n E β L H M.1 M.2 S' hS' hst⟩⟩
  have hind := StrictBoxOrder.box_indep hCI (subA E) β L
  have hsup : (⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA E) (shf β M.1)) = ⊤ :=
    iSup_subtype.trans htop
  first
  | exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  | exact DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top hind hsup

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ClosureOperators
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ClosureOperators

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def Cl {N : ℕ} (E : Fin N → Fin N → Module.End ℂ V) (L : Fin N → Fin N → Prop) (M : Submodule ℂ V) :
    Submodule ℂ V :=
  sInf {P | M ≤ P ∧ ∀ a b, L a b → ∀ q ∈ P, E a b q ∈ P}

theorem le_Cl {N : ℕ} (E : Fin N → Fin N → Module.End ℂ V) (L : Fin N → Fin N → Prop) (M : Submodule ℂ V) :
    M ≤ Cl E L M := le_sInf fun _ hP => hP.1

theorem Cl_closed {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} {L : Fin N → Fin N → Prop} {M : Submodule ℂ V}
    (a b : Fin N) (h : L a b) (q : V) (hq : q ∈ Cl E L M) : E a b q ∈ Cl E L M := by
  unfold Cl at hq ⊢
  rw [Submodule.mem_sInf] at hq ⊢
  intro P hP
  exact hP.2 a b h q (hq P hP)

theorem Cl_le {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} {L : Fin N → Fin N → Prop} {M : Submodule ℂ V}
    (P : Submodule ℂ V) (h1 : M ≤ P) (h2 : ∀ a b, L a b → ∀ q ∈ P, E a b q ∈ P) : Cl E L M ≤ P :=
  sInf_le ⟨h1, h2⟩

theorem gen {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (T L : Fin N → Fin N → Prop)
    (M : Submodule ℂ V)
    (h0 : ∀ a b, T a b → ∀ m ∈ M, E a b m ∈ Cl E L M)
    (h1 : ∀ a b c d, T a b → L c d → b = c → T a d ∨ L a d)
    (h2 : ∀ a b c d, T a b → L c d → d = a → T c b ∨ L c b) :
    ∀ a b, T a b → ∀ q ∈ Cl E L M, E a b q ∈ Cl E L M := by
  have key : Cl E L M ≤ Cl E L M ⊓ ⨅ a, ⨅ b, ⨅ (_ : T a b), (Cl E L M).comap (E a b) := by
    apply Cl_le
    · intro m hm
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      exact ⟨le_Cl E L M hm, fun a b hab => h0 a b hab m hm⟩
    · intro c d hcd q hq
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hq ⊢
      obtain ⟨hq1, hq2⟩ := hq
      refine ⟨Cl_closed c d hcd q hq1, fun a b hab => ?_⟩
      have hc := hE a b c d
      have e : E a b (E c d q) = E c d (E a b q) +
          ((if b = c then E a d else 0) - (if d = a then E c b else 0)) q := by
        rw [← hc]
        simp only [LinearMap.sub_apply, Module.End.mul_apply]
        abel
      rw [e]
      refine Submodule.add_mem _ (Cl_closed c d hcd _ (hq2 a b hab)) ?_
      rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs with hbc
        · rcases h1 a b c d hab hcd hbc with h | h
          · exact hq2 a d h
          · exact Cl_closed a d h q hq1
        · simp
      · split_ifs with hda
        · rcases h2 a b c d hab hcd hda with h | h
          · exact hq2 c b h
          · exact Cl_closed c b h q hq1
        · simp
  intro a b hab q hq
  have hk := key hq
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hk
  exact hk.2 a b hab

theorem mono_succ {n : ℕ} (f : Fin (n + 1) → Module.End ℂ V) (a : Fin (n + 1) → ℕ) :
    mono f a = f 0 ^ a 0 * mono (fun x => f x.succ) (fun x => a x.succ) := by
  simp only [mono, List.ofFn_succ, List.prod_cons]

theorem mono_zero : ∀ {n : ℕ} (f : Fin n → Module.End ℂ V), mono f (fun _ => 0) = 1 := by
  intro n
  induction n with
  | zero => intro f; simp [mono]
  | succ k ih =>
    intro f
    rw [mono_succ]
    simp only [pow_zero, one_mul]
    exact ih _

theorem mul_mono : ∀ {n : ℕ} (f : Fin n → Module.End ℂ V), (∀ a b, f a * f b = f b * f a) →
    ∀ (a : Fin n → ℕ) (x : Fin n), ∃ a' : Fin n → ℕ, f x * mono f a = mono f a' := by
  intro n
  induction n with
  | zero => intro f _ a x; exact x.elim0
  | succ k ih =>
    intro f hf a x
    cases x using Fin.cases with
    | zero =>
      refine ⟨Fin.cons (a 0 + 1) (fun y => a y.succ), ?_⟩
      rw [mono_succ, mono_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [pow_succ', mul_assoc]
    | succ y =>
      obtain ⟨a'', h''⟩ := ih (fun z => f z.succ) (fun p q => hf _ _) (fun z => a z.succ) y
      refine ⟨Fin.cons (a 0) a'', ?_⟩
      rw [mono_succ, mono_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← mul_assoc, ((show Commute (f y.succ) (f 0) from hf _ _).pow_right (a 0)).eq, mul_assoc, h'']

def MS {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range fun a : Fin n → ℕ => mono f a v)

theorem mem_MS {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) : v ∈ MS f v := by
  apply Submodule.subset_span
  exact ⟨fun _ => 0, by simp [mono_zero]⟩

theorem MS_closed {n : ℕ} (f : Fin n → Module.End ℂ V) (hf : ∀ a b, f a * f b = f b * f a) (v : V) (x : Fin n) :
    ∀ p ∈ MS f v, f x p ∈ MS f v := by
  intro p hp
  have hle : MS f v ≤ (MS f v).comap (f x) := by
    unfold MS
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', ha'⟩ := mul_mono f hf a x
    show f x (mono f a v) ∈ Submodule.span ℂ (Set.range fun a : Fin n → ℕ => mono f a v)
    rw [show f x (mono f a v) = (f x * mono f a) v from rfl, ha']
    exact Submodule.subset_span ⟨a', rfl⟩
  exact hle hp

theorem MS_le_ker {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) (ξ : Module.Dual ℂ V)
    (h : ∀ a : Fin n → ℕ, ξ (mono f a v) = 0) : MS f v ≤ LinearMap.ker ξ := by
  unfold MS
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact LinearMap.mem_ker.mpr (h a)

theorem yK_comm {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    yK E a * yK E b = yK E b * yK E a := by
  have h := hE (Fin.last n) a.castSucc (Fin.last n) b.castSucc
  rw [if_neg (Fin.castSucc_lt_last a).ne, if_neg (Fin.castSucc_lt_last b).ne, sub_zero] at h
  exact sub_eq_zero.mp h

theorem etaK_comm {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) :
    etaK E a * etaK E b = etaK E b * etaK E a := by
  have h := hE a.castSucc (Fin.last n) b.castSucc (Fin.last n)
  rw [if_neg (Fin.castSucc_lt_last b).ne', if_neg (Fin.castSucc_lt_last a).ne', sub_zero] at h
  exact sub_eq_zero.mp h

theorem exists_castSucc {n : ℕ} (a : Fin (n + 1)) (h : a ≠ Fin.last n) : ∃ a' : Fin n, a = a'.castSucc := by
  first
  | exact ⟨a.castPred h, (Fin.castSucc_castPred a h).symm⟩
  | (obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr h; exact ⟨j, hj.symm⟩)

theorem top_of_stab {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hI : Irr E) (S : Submodule ℂ V) (hS : Stab E S)
    (v : V) (hv : v ∈ S) (hv0 : v ≠ 0) : S = ⊤ := by
  refine (hI.2 S hS).resolve_left (fun h => hv0 ?_)
  rw [h] at hv
  exact (Submodule.mem_bot ℂ).mp hv

theorem trace_comm {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E) (a b : Fin N) :
    (∑ c, E c c) * E a b = E a b * ∑ c, E c c := by
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun c _ => hE c c a b), Finset.sum_sub_distrib]
  simp

theorem trace_scalar [FiniteDimensional ℂ V] {N : ℕ} {E : Fin N → Fin N → Module.End ℂ V} (hE : GlRel E)
    (hI : Irr E) : ∃ ζ : ℂ, ∀ v : V, (∑ c, E c c) v = ζ • v := by
  haveI := hI.1
  obtain ⟨ζ, hζ⟩ := Module.End.exists_eigenvalue (∑ c, E c c)
  refine ⟨ζ, fun v => ?_⟩
  have hS : Stab E (LinearMap.ker ((∑ c, E c c) - ζ • 1)) := by
    intro a b w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have e := congrArg (fun g : Module.End ℂ V => g w) (trace_comm hE a b)
    simp only [Module.End.mul_apply] at e
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hw ⊢
    rw [e, sub_eq_zero.mp hw, map_smul, sub_self]
  obtain ⟨w, hw⟩ := hζ.exists_hasEigenvector
  have hmem : w ∈ LinearMap.ker ((∑ c, E c c) - ζ • 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact hw.apply_eq_smul
  have htop := top_of_stab hI _ hS w hmem hw.2
  have hv : v ∈ LinearMap.ker ((∑ c, E c c) - ζ • 1) := by rw [htop]; trivial
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv
  exact hv

end Formalism.FourierDecayAlt.P.ClosureOperators

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr ClosureOperators

private theorem MS_le_of_mem_of_invariant {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (f : Fin n → Module.End ℂ V)
    (v : V) (P : Submodule ℂ V) (hv : v ∈ P) (hf : ∀ x, ∀ q ∈ P, f x q ∈ P) : MS f v ≤ P := by
  have key : ∀ (k : ℕ) (g : Fin k → Module.End ℂ V), (∀ x, ∀ q ∈ P, g x q ∈ P) →
      ∀ b : Fin k → ℕ, mono g b v ∈ P := by
    intro k
    induction k with
    | zero =>
      intro g _ b
      have h1 : mono g b = 1 := by simp [mono]
      rw [h1]
      exact hv
    | succ k ih =>
      intro g hg b
      rw [mono_succ, Module.End.mul_apply]
      have h2 := ih (fun x => g x.succ) (fun x q hq => hg x.succ q hq) (fun x => b x.succ)
      generalize b 0 = j
      induction j with
      | zero => rw [pow_zero, Module.End.one_apply]; exact h2
      | succ j ihj => rw [pow_succ', Module.End.mul_apply]; exact hg 0 _ ihj
  unfold MS
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  exact key n f hf b

theorem span_top_vectors : Qr.SpanTop := by
  intro V _ _ n E ν v₀ hE hI hW hv0 ξ hξ hm
  let L : Fin (n + 1) → Fin (n + 1) → Prop := fun a b => a ≠ Fin.last n ∧ b ≠ Fin.last n ∧ b < a
  let M : Submodule ℂ V := MS (yK E) v₀
  have hyc : ∀ a b, yK E a * yK E b = yK E b * yK E a := yK_comm hE
  have hMC : M ≤ Cl E L M := le_Cl E L M
  have hv₀M : v₀ ∈ M := mem_MS (yK E) v₀
  have hNL : ∀ b, ¬ L (Fin.last n) b := fun b h => h.1 rfl
  have hY : ∀ (x : Fin n), ∀ q ∈ Cl E L M, E (Fin.last n) x.castSucc q ∈ Cl E L M := by
    intro x q hq
    refine gen hE (fun a b => a = Fin.last n ∧ b ≠ Fin.last n) L M ?_ ?_ ?_ _ _
      ⟨rfl, (Fin.castSucc_lt_last x).ne⟩ q hq
    · rintro a b ⟨rfl, hb⟩ m hm'
      obtain ⟨b', rfl⟩ := exists_castSucc b hb
      exact hMC (MS_closed (yK E) hyc v₀ b' m hm')
    · rintro a b c d ⟨ha, _⟩ ⟨_, hd, _⟩ _
      exact Or.inl ⟨ha, hd⟩
    · rintro a b c d ⟨ha, _⟩ ⟨_, hd, _⟩ hda
      exact absurd (hda.trans ha) hd
  let N : Submodule ℂ V :=
    { carrier := {m | m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun a b h => by
        rw [LinearMap.map_add]
        exact add_mem (hx.2 a b h) (hy.2 a b h)⟩
      zero_mem' := ⟨zero_mem _, fun a b _ => by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun a b h => by
        rw [map_smul]; exact Submodule.smul_mem _ c (hx.2 a b h)⟩ }
  have hv₀N : v₀ ∈ N := by
    refine ⟨hMC hv₀M, ?_⟩
    intro a b hab
    rcases lt_trichotomy a b with h | rfl | h
    · rw [hW.2 a b h]; exact zero_mem _
    · rw [hW.1 a]; exact Submodule.smul_mem _ _ (hMC hv₀M)
    · have ha : a = Fin.last n := by
        by_contra ha
        exact hab ⟨ha, ne_of_lt (lt_of_lt_of_le h (Fin.le_last a)), h⟩
      subst ha
      obtain ⟨b', rfl⟩ := exists_castSucc b (ne_of_lt h)
      exact hMC (MS_closed (yK E) hyc v₀ b' v₀ hv₀M)
  have hNy : ∀ (x : Fin n), ∀ m ∈ N, yK E x m ∈ N := by
    intro x m hm
    obtain ⟨hm1, hm2⟩ : m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M := hm
    refine ⟨hY x m hm1, ?_⟩
    intro a b hab
    have hrel := LinearMap.congr_fun (hE a b (Fin.last n) x.castSucc) m
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hrel
    have key : E a b (yK E x m) = E (Fin.last n) x.castSucc (E a b m) +
        ((if b = Fin.last n then E a x.castSucc else 0) m -
          (if x.castSucc = a then E (Fin.last n) b else 0) m) := by
      show E a b (E (Fin.last n) x.castSucc m) = _
      rw [sub_eq_iff_eq_add.mp hrel, add_comm]
    rw [key]
    refine add_mem (hY x _ (hm2 a b hab)) (sub_mem ?_ ?_)
    · split_ifs with hb
      · by_cases hL : L a x.castSucc
        · exact Cl_closed a x.castSucc hL m hm1
        · exact hm2 a x.castSucc hL
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs with hxa
      · exact hm2 (Fin.last n) b (hNL b)
      · rw [LinearMap.zero_apply]; exact zero_mem _
  have hMN : M ≤ N := MS_le_of_mem_of_invariant (yK E) v₀ N hv₀N hNy
  have hStab : Stab E (Cl E L M) := by
    intro a b q hq
    by_cases hab : L a b
    · exact Cl_closed a b hab q hq
    · refine gen hE (fun a b => ¬ L a b) L M ?_ (fun a b c d _ _ _ => (em (L a d)).symm)
        (fun a b c d _ _ _ => (em (L c b)).symm) a b hab q hq
      intro a b h m hm'
      have h' : m ∈ Cl E L M ∧ ∀ a b, ¬ L a b → E a b m ∈ Cl E L M := hMN hm'
      exact h'.2 a b h
  have htop : Cl E L M = ⊤ := top_of_stab hI _ hStab v₀ (hMC hv₀M) hv0
  have hker : Cl E L M ≤ LinearMap.ker ξ := by
    apply Cl_le
    · exact MS_le_ker (yK E) v₀ ξ hm
    · intro a b hab q _
      obtain ⟨ha, hb, hba⟩ := hab
      obtain ⟨a', rfl⟩ := exists_castSucc a ha
      obtain ⟨b', rfl⟩ := exists_castSucc b hb
      rw [LinearMap.mem_ker]
      exact hξ a' b' (Fin.castSucc_lt_castSucc_iff.mp hba) q
  ext v
  have hv : v ∈ Cl E L M := by rw [htop]; exact Submodule.mem_top
  rw [LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp (hker hv)

theorem span_singular_vectors : Qr.SpanSing := by
  intro V _ _ _ n E ξ₀ μ w hE hI hξ0 hlow hW hm
  by_contra hw
  obtain ⟨ζ, hζ⟩ := trace_scalar hE hI
  let M : Submodule ℂ V := MS (etaK E) w
  have hec : ∀ a b, etaK E a * etaK E b = etaK E b * etaK E a := etaK_comm hE
  have hwM : w ∈ M := mem_MS (etaK E) w
  have hMη : ∀ (x : Fin n), ∀ q ∈ M, E x.castSucc (Fin.last n) q ∈ M :=
    fun x q hq => MS_closed (etaK E) hec w x q hq
  have hw_up : ∀ a b : Fin (n + 1), a ≤ b → E a b w ∈ M := by
    intro a b hab
    by_cases hb : b = Fin.last n
    · subst hb
      by_cases ha : a = Fin.last n
      · subst ha
        have htr := hζ w
        rw [LinearMap.sum_apply, Fin.sum_univ_castSucc] at htr
        have hdiag : ∀ i : Fin n, E i.castSucc i.castSucc w = μ i • w := fun i => hW.1 i
        have hE' : E (Fin.last n) (Fin.last n) w = ζ • w - ∑ i : Fin n, μ i • w := by
          rw [← htr]
          simp only [hdiag]
          abel
        rw [hE']
        exact sub_mem (Submodule.smul_mem _ _ hwM) (sum_mem fun i _ => Submodule.smul_mem _ _ hwM)
      · obtain ⟨a', rfl⟩ := exists_castSucc a ha
        exact hMη a' w hwM
    · obtain ⟨b', rfl⟩ := exists_castSucc b hb
      have ha : a ≠ Fin.last n := by
        rintro rfl
        exact absurd hab (not_le.mpr (Fin.castSucc_lt_last b'))
      obtain ⟨a', rfl⟩ := exists_castSucc a ha
      rcases (Fin.castSucc_le_castSucc_iff.mp hab).lt_or_eq with h | h
      · rw [show E a'.castSucc b'.castSucc w = subA E a' b' w from rfl, hW.2 a' b' h]
        exact zero_mem _
      · subst h
        rw [show E a'.castSucc a'.castSucc w = subA E a' a' w from rfl, hW.1 a']
        exact Submodule.smul_mem _ _ hwM
  let N : Submodule ℂ V :=
    { carrier := {m | m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun a b h => by
        rw [LinearMap.map_add]
        exact add_mem (hx.2 a b h) (hy.2 a b h)⟩
      zero_mem' := ⟨zero_mem _, fun a b _ => by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, fun a b h => by
        rw [map_smul]; exact Submodule.smul_mem _ c (hx.2 a b h)⟩ }
  have hNη : ∀ (x : Fin n), ∀ m ∈ N, etaK E x m ∈ N := by
    intro x m hm
    obtain ⟨hm1, hm2⟩ : m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M := hm
    refine ⟨hMη x m hm1, ?_⟩
    intro a b hab
    have hrel := LinearMap.congr_fun (hE a b x.castSucc (Fin.last n)) m
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hrel
    have key : E a b (etaK E x m) = E x.castSucc (Fin.last n) (E a b m) +
        ((if b = x.castSucc then E a (Fin.last n) else 0) m -
          (if Fin.last n = a then E x.castSucc b else 0) m) := by
      show E a b (E x.castSucc (Fin.last n) m) = _
      rw [sub_eq_iff_eq_add.mp hrel, add_comm]
    rw [key]
    refine add_mem (hMη x _ (hm2 a b hab)) (sub_mem ?_ ?_)
    · split_ifs with hb
      · exact hm2 a (Fin.last n) (Fin.le_last a)
      · rw [LinearMap.zero_apply]; exact zero_mem _
    · split_ifs with ha
      · subst ha
        have hb : b = Fin.last n := le_antisymm (Fin.le_last b) hab
        subst hb
        exact hm2 x.castSucc (Fin.last n) (Fin.le_last _)
      · rw [LinearMap.zero_apply]; exact zero_mem _
  have hwN : w ∈ N := ⟨hwM, hw_up⟩
  have hMN : M ≤ N := MS_le_of_mem_of_invariant (etaK E) w N hwN hNη
  let L : Fin (n + 1) → Fin (n + 1) → Prop := fun a b => b < a
  have hStab : Stab E (Cl E L M) := by
    intro a b q hq
    rcases lt_or_ge b a with hab | hab
    · exact Cl_closed a b hab q hq
    · refine gen hE (fun a b => a ≤ b) L M ?_ (fun a b c d _ _ _ => le_or_gt a d)
        (fun a b c d _ _ _ => le_or_gt c b) a b hab q hq
      intro a b h m hm'
      have h' : m ∈ M ∧ ∀ a b : Fin (n + 1), a ≤ b → E a b m ∈ M := hMN hm'
      exact le_Cl E L M (h'.2 a b h)
  have htop := top_of_stab hI _ hStab w (le_Cl E L M hwM) hw
  apply hξ0
  have hker : Cl E L M ≤ LinearMap.ker ξ₀ := by
    apply Cl_le
    · exact MS_le_ker (etaK E) w ξ₀ hm
    · intro a b hab q _
      rw [LinearMap.mem_ker]
      exact hlow a b hab q
  ext v
  have hv : v ∈ Cl E L M := by rw [htop]; exact Submodule.mem_top
  rw [LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp (hker hv)

end Formalism.FourierDecayAlt.P
end
end

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem capelli_singular : Qr.CapSing := qr_capSing_of singular_dominant exists_singular_maximal_vector

theorem top_weight_singular : Qr.TopWeightSing := qr_topWeightSing_of exists_singular_maximal_vector capelli_singular

theorem vector_descent : Qr.VecDown := qr_vecDown_of quantum_minor_polynomial polynomial_vanishing

theorem raising_nonzero : Qr.RaiseNZ := qr_raiseNZ_of covariant_raising

theorem lowering_nonzero : Qr.LowerNZ := qr_lowerNZ_of vector_descent

theorem branching_decomposition : Qr.Decomp :=
  qr_decomp_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations covariant_raising vector_descent
    raising_nonzero lowering_nonzero

theorem multiplicity_one : Qr.MultOne := qr_multOne_of exists_singular_maximal_vector dual_minor span_singular_vectors

theorem irreducible_capelli_modules : Qr.IrredCap :=
  qr_irredCap_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations top_weight_singular
    dual_minor span_top_vectors multiplicity_one branching_decomposition capelli_independence

theorem branching_algebraic : Qr.BranchingAlg := qr_branchingAlg_of branching_decomposition capelli_independence irreducible_capelli_modules

end Formalism.FourierDecayAlt.P
