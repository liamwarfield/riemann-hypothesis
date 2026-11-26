module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.YEPEComm
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AofUpdate
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

structure LinD : Prop where
  Tt_add : ∀ v i j (F F' : X.Fm j), X.Tt v i j (F + F') = X.Tt v i j F + X.Tt v i j F'
  Tt_smul : ∀ v i j (a : X.G.Kf) (F : X.Fm j), X.Tt v i j (a • F) = a • X.Tt v i j F
  yv_add : ∀ v (F F' : X.Fm 0), X.yv v (F + F') = X.yv v F + X.yv v F'
  yv_smul : ∀ v (a : X.G.Kf) (F : X.Fm 0), X.yv v (a • F) = a • X.yv v F
  yv_comm : ∀ v v' (F : X.Fm 0), X.yv v (X.yv v' F) = X.yv v' (X.yv v F)

variable {X}

theorem Zop_add (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (F F' : X.Fm j) :
    X.Zop v u m j (F + F') = X.Zop v u m j F + X.Zop v u m j F' := by
  unfold Sys.Zop Sys.Ttu
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL.Tt_add, smul_add, smul_add]

theorem Zop_smul (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (a : X.G.Kf) (F : X.Fm j) :
    X.Zop v u m j (a • F) = a • X.Zop v u m j F := by
  unfold Sys.Zop Sys.Ttu
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL.Tt_smul]
  simp only [smul_smul]
  congr 1
  ring

theorem Zop_zero (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) : X.Zop v u m j 0 = 0 := by
  have h := Zop_smul hL v u m j 0 0
  simpa using h

variable (X)

def ZL (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (vs : List X.Pl) (F : X.Fm j) : X.Fm j :=
  vs.foldr (fun v F' => X.Zop v (u v) (m v) j F') F

def Aof (i0 : X.Pl → ℕ) (vs : List X.Pl) : ℝ := ∑ v, if v ∈ vs ∧ i0 v = 0 then (X.alEven v : ℝ) else 0

def Gen (j : ℕ) (vs : List X.Pl) : Set (X.Fm (j + 1)) :=
  {T | ∃ (a : X.G.Kf) (i0 : X.Pl → ℕ) (G' : X.Fm j), G' ∈ X.Int j ∧ (∀ v, i0 v ≤ X.G.P.r) ∧
    (∀ v, v ∉ vs → i0 v = 0) ∧ X.vGeK a (Aof X i0 vs) ∧ T = a • TtL X (j + 1) i0 vs (X.Kz j G')}

variable {X}

theorem ZL_smul (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (vs : List X.Pl) (a : X.G.Kf) (F : X.Fm j) :
    ZL X u m j vs (a • F) = a • ZL X u m j vs F := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show X.Zop v (u v) (m v) j (ZL X u m j vs (a • F)) = a • X.Zop v (u v) (m v) j (ZL X u m j vs F)
    rw [ih, Zop_smul hL]

theorem TtL_congr (j : ℕ) (i0 i0' : X.Pl → ℕ) (vs : List X.Pl) (h : ∀ v ∈ vs, i0 v = i0' v) (F : X.Fm j) :
    TtL X j i0 vs F = TtL X j i0' vs F := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show X.Tt v (i0 v) j (TtL X j i0 vs F) = X.Tt v (i0' v) j (TtL X j i0' vs F)
    rw [h v (by simp), ih (fun w hw => h w (by simp [hw]))]

theorem Aof_update (i0 : X.Pl → ℕ) (vs : List X.Pl) (v : X.Pl) (hv : v ∉ vs) (i : ℕ) :
    Aof X (Function.update i0 v i) (v :: vs) = Aof X i0 vs + (if i = 0 then (X.alEven v : ℝ) else 0) := by
  unfold Aof
  have hs : (if i = 0 then (X.alEven v : ℝ) else 0) =
      ∑ w, if w = v ∧ i = 0 then (X.alEven w : ℝ) else 0 := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : w = v
  · subst hw
    simp [hv]
  · simp [hw, Function.update_apply]

theorem Zop_gen (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ)
    (hj : j < X.mm) (hu : ∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0)
    (hc0 : ∀ l ≤ X.G.P.r, X.vGeK (X.cl v m (j + 1) l) 0)
    (hcr : X.vGeK (X.cl v m (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hv : v ∉ vs) :
    ∀ T ∈ Submodule.span X.G.O (Gen X j vs), X.Zop v u m (j + 1) T ∈ Submodule.span X.G.O (Gen X j (v :: vs)) := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, i0, G', hG', hr, h0, ha, rfl⟩ := hx
    rw [Zop_smul hL]
    unfold Sys.Zop
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun l hl => ?_
    rw [Finset.mem_range] at hl
    apply Submodule.subset_span
    have hupd : Function.update i0 v (X.G.P.r - l) v = X.G.P.r - l := by simp
    have hTt : TtL X (j + 1) (Function.update i0 v (X.G.P.r - l)) (v :: vs) (X.Kz j G') =
        X.Tt v (X.G.P.r - l) (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G')) := by
      show X.Tt v (Function.update i0 v (X.G.P.r - l) v) (j + 1)
          (TtL X (j + 1) (Function.update i0 v (X.G.P.r - l)) vs (X.Kz j G')) = _
      rw [hupd, TtL_congr (j + 1) _ i0 vs (fun w hw => Function.update_of_ne (ne_of_mem_of_not_mem hw hv) _ _)]
    refine ⟨a * ((-1) ^ l * X.cl v m (j + 1) l * (∏ l' ∈ Icc 1 (j + 1), u l') ^ (-((X.G.P.r - l : ℕ) : ℤ))),
      Function.update i0 v (X.G.P.r - l), G', hG', ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw
        rw [hupd]
        omega
      · rw [Function.update_of_ne hw]
        exact hr w
    · intro w hw
      rw [List.mem_cons, not_or] at hw
      rw [Function.update_of_ne hw.1]
      exact h0 w hw.2
    · rw [Aof_update i0 vs v hv (X.G.P.r - l)]
      have hU : X.vEqK (∏ l' ∈ Icc 1 (j + 1), u l') 0 :=
        vEqK_prod_units X hfr (eO_pos X v) _ _ fun l' hl' => hu l' (by
          rw [Finset.mem_Icc] at hl' ⊢
          omega)
      have hUk := (vEqK_zpow X hfr hU (-((X.G.P.r - l : ℕ) : ℤ))).1
      have hcl : X.vGeK (X.cl v m (j + 1) l) (if X.G.P.r - l = 0 then (X.alEven v : ℝ) else 0) := by
        split_ifs with h
        · have hlr : l = X.G.P.r := by omega
          rw [hlr]
          exact hcr
        · exact hc0 l (by omega)
      have key := vGeK_mul X hfr ha (vGeK_mul X hfr (vGeK_mul X hfr (vGeK_negOnePow X l) hcl) hUk)
      convert key using 1
      ring
    · rw [hTt]
      simp only [Sys.Ttu, smul_smul]
  | zero =>
    rw [Zop_zero hL]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Zop_add hL]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul X.G.Kf a x, Zop_smul hL, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

theorem ZL_mem (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (hj : j < X.mm)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hnd : vs.Nodup)
    (G : X.Fm j) (hG : G ∈ X.Int j) :
    ZL X u m (j + 1) vs (X.Kz j G) ∈ Submodule.span X.G.O (Gen X j vs) := by
  induction vs with
  | nil =>
    apply Submodule.subset_span
    refine ⟨1, fun _ => 0, G, hG, fun _ => Nat.zero_le _, fun _ _ => rfl, ?_, ?_⟩
    · have h0 : Aof X (fun _ => 0) [] = 0 := by
        simp [Aof]
      rw [h0]
      exact vGeK_one X
    · rw [one_smul]
      rfl
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    exact Zop_gen hfr hL v (u v) (m v) j hj (hu v) (hc0 v) (hcr v) vs hnd.1 _ (ih hnd.2)

theorem ZL_bound {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y)
    (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (hj : j < X.mm)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hnd : vs.Nodup)
    (gP : X.Pl → ℝ) (h1 : ∀ v ∈ vs, gP v ≤ X.gv v (j + 1)) (h2 : ∀ v, v ∉ vs → Y.LowAt j v (gP v))
    (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (ZL X u m (j + 1) vs (X.Kz j G)) (∑ v, gP v - X.dG j) := by
  have key : ∀ T ∈ Submodule.span X.G.O (Gen X j vs), X.vGe (j + 1) T (∑ v, gP v - X.dG j) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, i0, G', hG', hr, h0, ha, rfl⟩ := hx
      obtain ⟨gQ, hgQ⟩ : ∃ f : X.Pl → ℝ,
          f = fun v => gP v - (if v ∈ vs ∧ i0 v = 0 then (X.alEven v : ℝ) else 0) := ⟨_, rfl⟩
      have hP : ∀ v, PlaceB X Y j v (i0 v) (gQ v) := by
        intro v
        by_cases hv : v ∈ vs
        · by_cases hi : i0 v = 0
          · left
            refine ⟨hi, Or.inr ?_⟩
            simp only [hgQ, hv, hi, and_self, if_true]
            linarith [h1 v hv]
          · right
            refine ⟨by omega, hr v, ?_⟩
            simp only [hgQ, hv, hi, and_false, if_false, sub_zero]
            exact h1 v hv
        · left
          refine ⟨h0 v hv, Or.inl ?_⟩
          simp only [hgQ, hv, false_and, if_false, sub_zero]
          exact h2 v hv
      have hTt := form_of_place hF hE j hj i0 vs gQ hnd hr h0 hP G' hG'
      have hsum : ∑ v, gQ v = ∑ v, gP v - Aof X i0 vs := by
        simp only [hgQ, Aof, Finset.sum_sub_distrib]
      have hs := vGe_smul X hfr ha hTt
      rw [hsum] at hs
      convert hs using 1
      ring
    | zero => exact vGe_zero X _ _
    | add x y _ _ hx hy => exact vGe_add X hx hy
    | smul a x _ hx =>
      have ha : X.vGeK (algebraMap X.G.O X.G.Kf a) 0 := (vGeK_zero_iff X).2 ((mem_intK X).2 ⟨a, rfl⟩)
      have hs := vGe_smul X hfr ha hx
      rw [zero_add, algebraMap_smul] at hs
      exact hs
  exact key _ (ZL_mem hfr hL u m j hj hu hc0 hcr vs hnd G hG)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

def yE (hL : LinD X) (v : X.Pl) : Module.End X.G.Kf (X.Fm 0) :=
  { toFun := X.yv v, map_add' := hL.yv_add v, map_smul' := fun a F => hL.yv_smul v a F }

def PE (hL : LinD X) (vs : List X.Pl) : Module.End X.G.Kf (X.Fm 0) := (vs.map (yE hL)).prod

theorem yE_comm (hL : LinD X) (v v' : X.Pl) : Commute (yE hL v) (yE hL v') :=
  LinearMap.ext fun F => hL.yv_comm v v' F

theorem yE_PE_comm (hL : LinD X) (v : X.Pl) (ws : List X.Pl) : Commute (yE hL v) (PE hL ws) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hy
  exact yE_comm hL v w

theorem PE_comm (hL : LinD X) (vs ws : List X.Pl) : Commute (PE hL vs) (PE hL ws) := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
  exact yE_PE_comm hL v ws

theorem PE_cons (hL : LinD X) (v : X.Pl) (vs : List X.Pl) : PE hL (v :: vs) = yE hL v * PE hL vs := by
  simp [PE]

theorem PE_append (hL : LinD X) (vs ws : List X.Pl) : PE hL (vs ++ ws) = PE hL vs * PE hL ws := by
  simp [PE]

theorem PE_perm (hL : LinD X) {vs ws : List X.Pl} (h : vs.Perm ws) : PE hL vs = PE hL ws := by
  apply List.Perm.prod_eq' (h.map _)
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 ha
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hb
  exact yE_comm hL v w

theorem PE_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) :
    ∀ F ∈ S, PE hL vs F ∈ S := by
  induction vs with
  | nil => intro F hF; simpa [PE] using hF
  | cons v vs ih =>
    intro F hF
    rw [PE_cons]
    exact hy v _ (ih F hF)

theorem PE_pow_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) (n : ℕ) :
    ∀ F ∈ S, (PE hL vs ^ n) F ∈ S := by
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    rw [pow_succ']
    exact PE_mem hL hy vs _ (ih F hF)

theorem fold_eq (hL : LinD X) (n : ℕ) (vs : List X.Pl) (z : X.Fm 0) :
    vs.foldr (fun v F' => (X.yv v)^[n] F') z = (PE hL vs ^ n) z := by
  induction vs with
  | nil => simp [PE]
  | cons v vs ih =>
    rw [PE_cons, (yE_PE_comm hL v vs).mul_pow, List.foldr_cons, ih, Module.End.mul_apply,
      Module.End.pow_apply (yE hL v)]
    rfl

theorem yv_FQ (hL : LinD X) (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) (v : X.Pl) :
    ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0 := by
  intro F hF
  unfold Sys.FQ at hF ⊢
  induction hF using Submodule.span_induction with
  | zero =>
    have := hL.yv_smul v 0 0
    simp only [zero_smul] at this
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy' => rw [hL.yv_add]; exact Submodule.add_mem _ hx hy'
  | smul c x _ hx => rw [hL.yv_smul]; exact Submodule.smul_mem _ _ hx
  | mem x hx => exact Submodule.subset_span (hy v x hx)

variable (X)

def PrS (j : ℕ) (vs : List X.Pl) : ℤ :=
  ∑ v, if v ∈ vs then PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j else 0

variable {X}

theorem PrS_cons (j : ℕ) (v : X.Pl) (vs : List X.Pl) (hv : v ∉ vs) :
    PrS X j (v :: vs) = PrS X j vs + PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j := by
  unfold PrS
  have : PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j =
      ∑ v', if v' = v then PrZ X.t X.G.P.r (X.G.P.lam0 v') (X.w v') j else 0 := by
    rw [Finset.sum_ite_eq' univ v]
    simp
  rw [this, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v' _
  by_cases h : v' = v
  · subst h
    simp [hv]
  · simp [h]

theorem ZL_chain (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ)
    (hCi : ∀ v, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hyQ : ∀ v, ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0) (vs : List X.Pl) (hnd : vs.Nodup) (F : X.Fm 0) (hF : F ∈ X.FQ 0) :
    ZL X u m (j + 1) vs (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrS X (j + 1) vs)) • X.chainK (j + 1) (PE hL vs F) := by
  induction vs with
  | nil => simp [ZL, PrS, PE]
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    show X.Zop v (u v) (m v) (j + 1) (ZL X u m (j + 1) vs (X.chainK (j + 1) F)) = _
    rw [ih hnd.2, Zop_smul hL, hCi v _ (PE_mem hL (S := (X.FQ 0 : Set (X.Fm 0))) hyQ vs F hF), smul_smul,
      ← zpow_add₀ hp, PrS_cons _ _ _ hnd.1, PE_cons]
    rfl

theorem vGeK_vsc (g : ℝ) : X.vGeK (X.vsc g) g := (vGeK_iff X).2 ⟨1, by simp⟩

def bbJ (X : Sys p) (Lv : List X.Pl) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool) (j : ℕ) : ℝ :=
  ∑ v, (if v ∈ Lv.filter (Q j) then Gn v (j + 1) else G0n v (j + 1)) - X.dG j -
        (PrS X (j + 1) (Lv.filter (Q j)) : ℝ)

theorem main_ind {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X)
    (hF : FormB X Y) (hE : EntCondition X Y) (u m : X.Pl → ℕ → X.G.Kf)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ j < X.mm, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, ∀ j < X.mm, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v))
    (hCi : ∀ v, ∀ j < X.mm, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0)
    (Lv : List X.Pl) (hnd : Lv.Nodup) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool)
    (h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1))
    (h2 : ∀ v, ∀ j < X.mm, Y.LowAt j v (G0n v (j + 1))) :
    ∀ m' ≤ X.mm, ∀ F1 ∈ X.Int 0, X.vGe m' (X.chainK m' ((PE hL Lv ^ m') F1))
      (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) := by
  intro m'
  induction m' with
  | zero =>
    intro _ F1 hF1
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact (vGe_zero_iff X).2 hF1
  | succ m' ih =>
    intro hm F1 hF1
    have hj : m' < X.mm := hm
    set B := Lv.filter (Q m') with hB
    set C := Lv.filter (fun x => !Q m' x) with hC
    have e1 : PE hL Lv = PE hL B * PE hL C := by
      rw [← PE_append]
      exact (PE_perm hL (List.filter_append_perm (Q m') Lv)).symm
    have e2 : PE hL Lv ^ (m' + 1) = PE hL B * (PE hL Lv ^ m' * PE hL C) := by
      have e0 : PE hL Lv ^ (m' + 1) = (PE hL B * PE hL C) * PE hL Lv ^ m' := by rw [pow_succ', ← e1]
      rw [e0, mul_assoc, ((PE_comm hL C Lv).pow_right m').eq]
    have hF1' : PE hL C F1 ∈ X.Int 0 := PE_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy C F1 hF1
    set W := (PE hL Lv ^ m') (PE hL C F1) with hW
    have hWi : W ∈ X.Int 0 := PE_pow_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy Lv m' _ hF1'
    have hWQ : W ∈ X.FQ 0 := Submodule.subset_span hWi
    have hBnd : B.Nodup := hnd.filter _
    have e3 := ZL_chain hp hL u m m' (fun v => hCi v m' hj) (yv_FQ hL hy) B hBnd W hWQ
    have e4 : X.chainK (m' + 1) ((PE hL Lv ^ (m' + 1)) F1) =
        ((p : X.G.Kf) ^ (-(PrS X (m' + 1) B))) • ZL X u m (m' + 1) B (X.chainK (m' + 1) W) := by
      rw [e3, smul_smul, ← zpow_add₀ hp, neg_add_cancel, zpow_zero, one_smul, e2]
      rfl
    obtain ⟨G', hG', hG'e⟩ := (vGe_iff X).1 (ih (le_of_lt hj) _ hF1')
    have e5 : X.chainK (m' + 1) W = X.vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) • X.Kz m' G' := by
      show X.Kz m' (X.chainK m' W) = _
      rw [← hG'e, map_smul]
    rw [e4, e5, ZL_smul hL]
    have hb := ZL_bound hfr hL hF hE u m m' hj hu (fun v => hc0 v m' hj) (fun v => hcr v m' hj) B hBnd
      (fun v => if v ∈ B then Gn v (m' + 1) else G0n v (m' + 1))
      (fun v hv => by simp only [hv, if_true]; exact h1 v (List.mem_of_mem_filter hv) m' hj)
      (fun v hv => by simp only [hv, if_false]; exact h2 v m' hj) G' hG'
    have h3 := vGe_smul X hfr (vGeK_ppow X hfr (-(PrS X (m' + 1) B))) (vGe_smul X hfr (vGeK_vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j)) hb)
    rw [Finset.sum_range_succ]
    refine vGe_mono X hfr (le_of_eq ?_) h3
    conv_lhs => rw [bbJ]
    push_cast
    ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem sum_Icc_shift (f : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Icc 1 m, f j = ∑ j ∈ range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_ind {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (f : ι → ℝ) :
    ∑ v ∈ A, f v = ∑ v, if v ∈ A then f v else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem basic₂ {ι : Type} [Fintype ι] [DecidableEq ι] (mm : ℕ) (VV BB : Finset ι) (hBB : BB ⊆ VV)
    (Gn G0n PRn Prr : ι → ℕ → ℝ) (S : ι → ℝ) (dG : ℕ → ℝ) (inB : ℕ → ι → Prop) [∀ j v, Decidable (inB j v)]
    (hin : ∀ j v, inB j v ↔ v ∈ BB ∧ G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    (hPR : ∀ v ∈ VV, ∀ j < mm, Prr v (j + 1) ≤ PRn v (j + 1))
    (hS : ∀ v ∈ VV, ∑ j ∈ range mm, max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 ≤ S v) :
    ∑ j ∈ range mm, (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) +
        ∑ v ∈ univ \ VV, G0n v (j + 1)) - ∑ j ∈ range mm, dG j ≤
      ∑ v ∈ VV \ BB, S v + ∑ j ∈ range mm, (∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1)) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
  have hS' : ∑ j ∈ range mm, ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0)
      ≤ ∑ v ∈ VV \ BB, S v := by
    rw [Finset.sum_comm, sum_ind (VV \ BB) S]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV \ BB
    · simp only [hv, ↓reduceIte]
      exact hS v (Finset.mem_sdiff.1 hv).1
    · simp [hv]
  have key : ∀ j ∈ range mm,
      (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) + ∑ v ∈ univ \ VV, G0n v (j + 1)) - dG j ≤
      ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
      ((∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1))) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
    intro j hj
    have hj' : j < mm := Finset.mem_range.1 hj
    suffices h : ∑ v, ((if v ∈ VV then max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) else 0) +
        (if v ∈ univ \ VV then G0n v (j + 1) else 0) + (if inB j v then Prr v (j + 1) else 0)) ≤
        ∑ v, ((if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
        (if inB j v then Gn v (j + 1) else G0n v (j + 1))) by
      rw [sum_ind VV, sum_ind (univ \ VV)]
      simp only [Finset.sum_add_distrib] at h
      linarith
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV
    · have hv2 : v ∉ univ \ VV := by simp [hv]
      by_cases hb : v ∈ BB
      · have hv3 : v ∉ VV \ BB := by simp [hb]
        by_cases hi : inB j v
        · have h1 := ((hin j v).1 hi).2
          have h2 := hPR v hv j hj'
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_left h1]
          linarith
        · have h1 : ¬ (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1)) := fun h => hi ((hin j v).2 ⟨hb, h⟩)
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_right (le_of_lt (not_le.1 h1))]
          linarith
      · have hv3 : v ∈ VV \ BB := Finset.mem_sdiff.2 ⟨hv, hb⟩
        have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
        simp only [hv, hv2, hv3, hi, ↓reduceIte]
        have hm : max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) ≤
            max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 + G0n v (j + 1) := by
          have := le_max_left (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          have := le_max_right (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          exact max_le (by linarith) (by linarith)
        linarith
    · have hv2 : v ∈ univ \ VV := by simp [hv]
      have hb : v ∉ BB := fun h => hv (hBB h)
      have hv3 : v ∉ VV \ BB := by simp [hv]
      have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
      simp only [hv, hv2, hv3, hi, ↓reduceIte]
      linarith
  have hsum := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢
  linarith

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem PrZ_cast (v : X.Pl) (j : ℕ) :
    ((PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j : ℤ) : ℝ) = X.Conclusion₂ v j := by
  simp only [Sys.Conclusion₂, PrZ, Pr]
  push_cast
  congr 1
  obtain ⟨k, hk⟩ := (X.G.P.setting v).even
  rw [hk]
  have h2 : ((k + k : ℕ) : ℤ) / 2 = (k : ℤ) := by omega
  rw [h2]
  push_cast
  ring

theorem lift_bound_of_integrality (D : Formalism.BasicNotions.D7) {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0)
    (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y) (h4 : Conclusion4 D X)
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV hG hLow hPr hS F hF
  choose u m hu hm hrest using h4
  have hπ : (algebraMap X.G.O X.G.Kf X.vp) ≠ 0 := by
    intro h0
    exact X.unif.ne_zero ((IsFractionRing.injective X.G.O X.G.Kf) (h0.trans (map_zero _).symm))
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨BB, hBB, Lv, hnd, hLv, F0, hF0, rfl⟩ := hx
    obtain ⟨F1, hF1, rfl⟩ := hF0
    let Q : ℕ → X.Pl → Bool := fun j v => decide (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    have hmemL : ∀ v, v ∈ Lv ↔ v ∈ BB := fun v => by rw [← hLv, List.mem_toFinset]
    have h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1) := fun v hv j hj =>
      hG v (hBB ((hmemL v).1 hv)) (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hmi := main_ind hfr hp hL hF hE u m hu (fun v j hj => (hrest v j hj).2.1)
      (fun v j hj => (hrest v j hj).2.2.1) (fun v j hj => (hrest v j hj).1) hy Lv hnd Gn G0n Q h1 hLow
      X.mm le_rfl F1 hF1
    have hnum : (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) ≤ ∑ v ∈ VV \ BB, S v + ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j := by
      rw [sum_Icc_shift]
      have hb := basic₂ X.mm VV BB hBB Gn G0n PRn (fun v j => X.Conclusion₂ v j) S (fun j => (X.dG j : ℝ))
        (fun j v => v ∈ Lv.filter (Q j))
        (fun j v => by simp only [List.mem_filter, hmemL, Q, decide_eq_true_eq])
        (fun v hv j hj => hPr v hv (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
        (fun v hv => by rw [← sum_Icc_shift (fun j => max (Gn v j - PRn v j - G0n v j) 0)]; exact hS v hv)
      refine hb.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bbJ, PrS]
      push_cast [PrZ_cast]
      rfl
    unfold Sys.vGe scale at hmi ⊢
    obtain ⟨I, hI, hIeq⟩ := hmi
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hIeq ⊢
    rw [fold_eq hL]
    set g := ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j with hg
    set T : ℝ := (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) with hT
    have hceil : ⌈T * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ := by
      rw [Int.ceil_le]
      push_cast
      have h8 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
      have h6 : (∑ v ∈ VV \ BB, S v) * (X.eO : ℝ) ≤ ∑ v ∈ VV \ BB, (⌈S v * (X.eO : ℝ)⌉ : ℝ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => Int.le_ceil _
      have h7 := Int.le_ceil (g * (X.eO : ℝ))
      have h9 := mul_le_mul_of_nonneg_right hnum h8
      nlinarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ - ⌈T * (X.eO : ℝ)⌉ :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨X.vp ^ n • I, Submodule.smul_mem _ _ hI, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [map_smul, map_smul, ← hIeq, ← algebraMap_smul X.G.Kf (X.vp ^ n) I, smul_smul, smul_smul]
    congr 1
    unfold Sys.vsc
    rw [map_pow, ← zpow_natCast, ← zpow_add₀ hπ, ← zpow_add₀ hπ, hn]
    congr 1
    ring
  | zero =>
    unfold Sys.vGe
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    unfold Sys.vGe at *
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    unfold Sys.vGe at *
    rw [← algebraMap_smul X.G.Kf a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
