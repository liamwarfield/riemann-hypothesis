module

public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.PfTrunc

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.YbatStep
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section Tens

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def zSub (K V : Type*) [Field K] [AddCommGroup V] [Module K V] {n : ℕ} (j : Fin n) : Submodule K (Fin n → V) :=
  LinearMap.ker (LinearMap.proj j : (Fin n → V) →ₗ[K] V)

theorem mem_zSub (j : Fin n) (w : Fin n → V) : w ∈ zSub K V j ↔ w j = 0 := by
  simp [zSub]

theorem ev_pf_ne (E : GLOps n K V) (a x y : Fin n) (hx : x ≠ a) (hy : y ≠ a) (c T : ℕ) (w : Fin n → V) :
    (pf (tensOps E) x y c T w) a = pf E x y c T (w a) := by
  refine pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) ⊤ x y (fun _ _ => trivial)
    (fun w _ => ?_) (fun w => ?_) c T w trivial
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hx.symm, add_zero]
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]

theorem ev_pf_a (E : GLOps n K V) (a y : Fin n) (hy : y ≠ a) (c T : ℕ) (w : Fin n → V) (hw : w y = 0) :
    (pf (tensOps E) a y c T w) a = pf E a y c T (w a) := by
  refine pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) (zSub K V y) a y (fun w hw => ?_)
    (fun w hw => ?_) (fun w => ?_) c T w ((mem_zSub y w).2 hw)
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hy, hw, map_zero, add_zero]
  · rw [mem_zSub] at hw
    rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_pos rfl, hw, add_zero]
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]

theorem z_pf (E : GLOps n K V) (j x y : Fin n) (hx : j ≠ x) (hy : j ≠ y) (c T : ℕ) (w : Fin n → V) (hw : w j = 0) :
    (pf (tensOps E) x y c T w) j = 0 := by
  rw [← mem_zSub (K := K)]
  refine pf_mem (tensOps E) (zSub K V j) x y (fun w hw => ?_) (fun w hw => ?_) c T w ((mem_zSub j w).2 hw)
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hx, hw, map_zero, add_zero]
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hy, hw, map_zero, add_zero]

theorem zz_pf (E : GLOps n K V) (b c : Fin n) (s T : ℕ) (w : Fin n → V) (hb : w b = 0) (hc : w c = 0) :
    (pf (tensOps E) b c s T w) b = 0 ∧ (pf (tensOps E) b c s T w) c = 0 := by
  have key : ∀ x y : Fin n, (x = b ∨ x = c) → (y = b ∨ y = c) → ∀ w ∈ zSub K V b ⊓ zSub K V c,
      tensOps E x y w ∈ zSub K V b ⊓ zSub K V c := by
    intro x y _ hy w hw
    rw [Submodule.mem_inf, mem_zSub, mem_zSub] at hw ⊢
    have hwy : w y = 0 := by rcases hy with rfl | rfl; exacts [hw.1, hw.2]
    rw [tensOps_apply, tensOps_apply, hw.1, hw.2, hwy]
    simp
  have := pf_mem (tensOps E) (zSub K V b ⊓ zSub K V c) b c (key b c (Or.inl rfl) (Or.inr rfl))
    (key c b (Or.inr rfl) (Or.inl rfl)) s T w
    (by rw [Submodule.mem_inf, mem_zSub, mem_zSub]; exact ⟨hb, hc⟩)
  rwa [Submodule.mem_inf, mem_zSub, mem_zSub] at this

end Tens

theorem ybat_step (sg ta : ℕ) (h : YBat sg ta) : YBat (sg + 1) ta := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have hA : IsGLRep (tensOps E) := tens_isGLRep hE
  obtain ⟨T', hT0, hT2⟩ : ∃ T' : ℕ, T ≤ T' ∧ Module.finrank K (Fin n → V) ≤ T' :=
    ⟨max T (Module.finrank K (Fin n → V)), le_max_left _ _, le_max_right _ _⟩
  have hT1 : Module.finrank K V ≤ T' := hT.trans hT0
  have hw0 : (Pi.single a x : Fin n → V) ∈ weightSp (tensOps E) (ν + Pi.single a 1) := tens_single_wt E ν a x hx
  have e1 : (s : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) a - (ν + Pi.single a 1 : Fin n → ℤ) b + sg + 1 := by
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm, hs]
    push_cast
    ring
  have e2 : (t : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) b - (ν + Pi.single a 1 : Fin n → ℤ) c + ta + 1 := by
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hab.symm, Pi.single_eq_of_ne hac.symm, ht]
    ring
  have key := h K (Fin n → V) n (tensOps E) hA a b c hab hac hbc (ν + Pi.single a 1) s t e1 e2 T' hT2 _ hw0
  have key' := congrArg (fun w : Fin n → V => w a) key
  have z0b : (Pi.single a x : Fin n → V) b = 0 := by rw [Pi.single_apply, if_neg hab.symm]
  have z0c : (Pi.single a x : Fin n → V) c = 0 := by rw [Pi.single_apply, if_neg hac.symm]
  have z0a : (Pi.single a x : Fin n → V) a = x := by rw [Pi.single_apply, if_pos rfl]
  obtain ⟨z1b, z1c⟩ := zz_pf E b c t T' _ z0b z0c
  have z2b := z_pf E b a c hab.symm hbc (s + t) T' _ z1b
  have y1c := z_pf E c a b hac.symm hbc.symm s T' _ z0c
  rw [ev_pf_a E a b hab.symm s T' _ z2b, ev_pf_a E a c hac.symm (s + t) T' _ z1c,
    ev_pf_ne E a b c hab.symm hac.symm t T', ev_pf_ne E a b c hab.symm hac.symm t T',
    ev_pf_a E a c hac.symm (s + t) T' _ y1c, ev_pf_a E a b hab.symm s T' _ z0b, z0a] at key'
  rw [pf_trunc E hE a b hab s T T' hT hT1, pf_trunc E hE a c hac (s + t) T T' hT hT1,
    pf_trunc E hE b c hbc t T T' hT hT1]
  exact key'

theorem restYB_of (base : YBat 0 0) (symm : ∀ sg ta, YBat sg ta → YBat ta sg) : RestYB := by
  have h1 : ∀ sg, YBat sg 0 := by
    intro sg
    induction sg with
    | zero => exact base
    | succ k ih => exact ybat_step k 0 ih
  intro sg ta
  induction ta with
  | zero => exact h1 sg
  | succ k ih => exact symm _ _ (ybat_step k sg (symm _ _ ih))

end Formalism.MainNotions.G.ExtremalProjector
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.TruncatedChains.YbatBase
noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def resOps {m : ℕ} (E : GLOps n K V) (φ : Fin m → Fin n) : GLOps m K V := fun i j => E (φ i) (φ j)

theorem res_mem {m : ℕ} (E : GLOps n K V) (φ : Fin m → Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    x ∈ weightSp (resOps E φ) (ν ∘ φ) := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i
  exact hx (φ i)

theorem res_rep {m : ℕ} {E : GLOps n K V} (hE : IsGLRep E) (φ : Fin m → Fin n) (hφ : Function.Injective φ) :
    IsGLRep (resOps E φ) := by
  refine ⟨fun a b c d => ?_, fun x => ?_, ?_⟩
  · have h := hE.1 (φ a) (φ b) (φ c) (φ d)
    simpa only [resOps, hφ.eq_iff] using h
  · obtain ⟨W, hW, hx, hst⟩ := hE.2.1 x
    exact ⟨W, hW, hx, fun a b y hy => hst (φ a) (φ b) y hy⟩
  · rw [eq_top_iff, ← hE.2.2]
    exact iSup_le fun mu => le_iSup_of_le (mu ∘ φ) fun x hx => res_mem E φ mu x hx

end

theorem ybat_base (D : Formalism.BasicNotions.D7) (hK : RestKill) (hP : RestPair) (hP' : RestPair') : YBat 0 0 := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have hs' : (s : ℤ) = ν a - ν b + 1 := by push_cast at hs; linarith
  have ht' : (t : ℤ) = ν b - ν c + 1 := by push_cast at ht; linarith
  have hu1 : ((s + t : ℕ) : ℤ) - (ν a - ν c) - 1 = (s : ℤ) - (ν a - ν b) := by push_cast; linarith
  have hu2 : ((s + t : ℕ) : ℤ) - (ν a - ν c) - 1 = (t : ℤ) - (ν b - ν c) := by push_cast; linarith
  have hsh := gl_rep_shifts_weights hE
  have hx1 : pf E b c t T x ∈ weightSp E ν := pf_wt hsh ν b c t T x hx
  have hx2 : pf E a c (s + t) T (pf E b c t T x) ∈ weightSp E ν := pf_wt hsh ν a c (s + t) T _ hx1
  have hz1 : pf E a b s T x ∈ weightSp E ν := pf_wt hsh ν a b s T x hx
  have hz2 : pf E a c (s + t) T (pf E a b s T x) ∈ weightSp E ν := pf_wt hsh ν a c (s + t) T _ hz1
  have hLw : pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) ∈ weightSp E ν := pf_wt hsh ν a b s T _ hx2
  have hRw : pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) ∈ weightSp E ν := pf_wt hsh ν b c t T _ hz2
  have hL_ab : E a b (pf E a b s T (pf E a c (s + t) T (pf E b c t T x))) = 0 :=
    hK K V n E hE a b hab ν s hs' T hT _ hx2
  have hL_bc : E b c (pf E a b s T (pf E a c (s + t) T (pf E b c t T x))) = 0 := by
    rw [hP K V n E hE a b c hab hac hbc ν s (s + t) hu1 T hT _ hx1, hK K V n E hE b c hbc ν t ht' T hT x hx,
      map_zero, map_zero]
  have hR_bc : E b c (pf E b c t T (pf E a c (s + t) T (pf E a b s T x))) = 0 :=
    hK K V n E hE b c hbc ν t ht' T hT _ hz2
  have hR_ab : E a b (pf E b c t T (pf E a c (s + t) T (pf E a b s T x))) = 0 := by
    rw [hP' K V n E hE a b c hab hac hbc ν t (s + t) hu2 T hT _ hz1, hK K V n E hE a b hab ν s hs' T hT x hx,
      map_zero, map_zero]
  set Lv := pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) with hLv
  set Rv := pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) with hRv
  have hφ : Function.Injective ![a, b, c] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hE' := res_rep hE ![a, b, c] hφ
  have hv' : Lv - Rv ∈ weightSp (resOps E ![a, b, c]) (ν ∘ ![a, b, c]) :=
    res_mem E ![a, b, c] ν _ (Submodule.sub_mem _ hLw hRw)
  have hvab : E a b (Lv - Rv) = 0 := by rw [map_sub, hL_ab, hR_ab, sub_zero]
  have hvbc : E b c (Lv - Rv) = 0 := by rw [map_sub, hL_bc, hR_bc, sub_zero]
  have hvac : E a c (Lv - Rv) = 0 := by
    have h := hE.1 a b b c
    rw [if_pos rfl, if_neg hac.symm, sub_zero] at h
    rw [← h, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hvbc, hvab, map_zero, map_zero,
      sub_zero]
  have hraise : ∀ i j : Fin 3, i < j → resOps E ![a, b, c] i j (Lv - Rv) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | exact hvab
      | exact hvac
      | exact hvbc
  have hlow : ∀ (i j : Fin 3), j < i → ∀ (cc : ℕ) (y : V),
      pf E (![a, b, c] j) (![a, b, c] i) cc T y - y ∈ nMinus (resOps E ![a, b, c]) := by
    intro i j hji cc y
    obtain ⟨w, hw⟩ := pf_sub E (![a, b, c] j) (![a, b, c] i) cc T y
    rw [← hw]
    exact lowering_operator_mem_nMinus (resOps E ![a, b, c]) hji w
  have hLx : Lv - x ∈ nMinus (resOps E ![a, b, c]) := by
    have e : Lv - x = (pf E a b s T (pf E a c (s + t) T (pf E b c t T x)) - pf E a c (s + t) T (pf E b c t T x)) +
        (pf E a c (s + t) T (pf E b c t T x) - pf E b c t T x) + (pf E b c t T x - x) := by
      rw [hLv]; abel
    rw [e]
    exact add_mem (add_mem (hlow 1 0 (by decide) s _) (hlow 2 0 (by decide) (s + t) _)) (hlow 2 1 (by decide) t x)
  have hRx : Rv - x ∈ nMinus (resOps E ![a, b, c]) := by
    have e : Rv - x = (pf E b c t T (pf E a c (s + t) T (pf E a b s T x)) - pf E a c (s + t) T (pf E a b s T x)) +
        (pf E a c (s + t) T (pf E a b s T x) - pf E a b s T x) + (pf E a b s T x - x) := by
      rw [hRv]; abel
    rw [e]
    exact add_mem (add_mem (hlow 2 1 (by decide) t _) (hlow 2 0 (by decide) (s + t) _)) (hlow 1 0 (by decide) s x)
  have hvn : Lv - Rv ∈ nMinus (resOps E ![a, b, c]) := by
    have h := Submodule.sub_mem _ hLx hRx
    rwa [sub_sub_sub_cancel_right] at h
  exact sub_eq_zero.mp (hwv_mem_nMinus_eq_zero D (resOps E ![a, b, c]) hE' (ν ∘ ![a, b, c]) (Lv - Rv) hv' hraise hvn)

end Formalism.MainNotions.G.ExtremalProjector
end
end
