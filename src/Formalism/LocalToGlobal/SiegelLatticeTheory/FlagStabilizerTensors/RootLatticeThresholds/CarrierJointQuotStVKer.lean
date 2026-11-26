module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotGeo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStRel

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVGeo
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

section Tri

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem shear_mp (i : ι) (ε : ℂ) (hε : MeasurePreserving (fun x : ℂ => ε * x) volume volume)
    (h : (ι → ℂ) → ℂ) (hm : Measurable h) (hi : ∀ c x, h (Function.update c i x) = h c) :
    MeasurePreserving (fun c : ι → ℂ => Function.update c i (ε * c i + h c)) volume volume := by
  let p : ι → Prop := fun j => j ≠ i
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) p
  have he : MeasurePreserving e (volume : Measure (ι → ℂ))
      ((volume : Measure ({j // p j} → ℂ)).prod (volume : Measure ({j // ¬ p j} → ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℂ)) p
  have he2 : ∀ (q : ({j // p j} → ℂ) × ({j // ¬ p j} → ℂ)) x,
      e.symm q x = if hx : p x then q.1 ⟨x, hx⟩ else q.2 ⟨x, hx⟩ := fun q x => rfl
  let h' : ({j // p j} → ℂ) → ℂ := fun y => h (e.symm (y, fun _ => 0))
  have hh'm : Measurable h' := hm.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hh : ∀ c, h c = h' (e c).1 := by
    intro c
    have : e.symm ((e c).1, fun _ => 0) = Function.update c i 0 := by
      funext x
      rw [he2]
      by_cases hx : x = i
      · subst hx; simp [p]
      · rw [dif_pos hx, Function.update_of_ne hx]; rfl
    simp only [h', this, hi]
  let g : ({j // p j} → ℂ) → ({j // ¬ p j} → ℂ) → ({j // ¬ p j} → ℂ) := fun y x j => ε * x j + h' y
  have hS : MeasurePreserving (fun q : ({j // p j} → ℂ) × ({j // ¬ p j} → ℂ) => (id q.1, g q.1 q.2))
      ((volume : Measure ({j // p j} → ℂ)).prod (volume : Measure ({j // ¬ p j} → ℂ)))
      ((volume : Measure ({j // p j} → ℂ)).prod (volume : Measure ({j // ¬ p j} → ℂ))) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id _) ?_ (ae_of_all _ fun y => ?_)
    · exact Measurable.of_eval fun j =>
        (measurable_const.mul ((measurable_pi_apply j).comp measurable_snd)).add (hh'm.comp measurable_fst)
    · exact (measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ))
        (fun _ => (measurePreserving_add_right volume (h' y)).comp hε)).map_eq
  have heq : (fun c : ι → ℂ => Function.update c i (ε * c i + h c)) =
      e.symm ∘ (fun q => (id q.1, g q.1 q.2)) ∘ e := by
    funext c x
    simp only [Function.comp_apply]
    rw [he2]
    by_cases hx : x = i
    · subst hx
      rw [dif_neg (by simp [p]), Function.update_self]
      simp only [g]; rw [hh c]; rfl
    · rw [dif_pos hx, Function.update_of_ne hx]
      rfl
  rw [heq]
  exact he.symm.comp (hS.comp he)

theorem tri_mp (ρ : ι → ℕ) (ε : ι → ℂ) (hε : ∀ p, MeasurePreserving (fun x : ℂ => ε p * x) volume volume)
    (g : ι → (ι → ℂ) → ℂ) (hgm : ∀ p, Measurable (g p))
    (hg : ∀ p c c', (∀ q, ρ q < ρ p → c q = c' q) → g p c = g p c') :
    MeasurePreserving (fun c p => ε p * c p + g p c) volume volume := by
  let F : Finset ι → (ι → ℂ) → (ι → ℂ) := fun s c p => if p ∈ s then ε p * c p + g p c else c p
  have key : ∀ s, MeasurePreserving (F s) volume volume := by
    intro s
    induction s using Finset.induction_on_max_value ρ with
    | empty =>
      have : F ∅ = id := by funext c p; simp [F]
      rw [this]; exact MeasurePreserving.id _
    | insert a s has hmax ih =>
      have hT := shear_mp a (ε a) (hε a) (g a) (hgm a) (fun c x => hg a _ _ fun q hq => by
        rw [Function.update_of_ne]; intro h; rw [h] at hq; exact lt_irrefl _ hq)
      have : F (insert a s) = F s ∘ fun c => Function.update c a (ε a * c a + g a c) := by
        funext c p
        simp only [F, Function.comp_apply, Finset.mem_insert]
        by_cases hp : p = a
        · subst hp; simp [has]
        · rw [Function.update_of_ne hp]
          by_cases hs : p ∈ s
          · rw [if_pos (Or.inr hs), if_pos hs]
            congr 1
            refine hg p _ _ fun q hq => ?_
            rw [Function.update_of_ne]
            intro hqa; rw [hqa] at hq; exact absurd (hmax p hs) (not_le.2 hq)
          · rw [if_neg (by simp [hp, hs]), if_neg hs]
      rw [this]; exact ih.comp hT
  have : (fun c p => ε p * c p + g p c) = F Finset.univ := by funext c p; simp [F]
  rw [this]; exact key _

theorem tri_mp' (ρ : ι → ℕ) (ε : ι → ℂ) (hε : ∀ p, MeasurePreserving (fun x : ℂ => ε p * x) volume volume)
    (f : (ι → ℂ) → (ι → ℂ)) (hfm : Measurable f) (G : ι → (ι → ℂ) → (ι → ℂ) → ℂ)
    (hf : ∀ c p, f c p = ε p * c p + G p c (f c))
    (hG : ∀ p c d c' d', (∀ q, ρ q < ρ p → c q = c' q ∧ d q = d' q) → G p c d = G p c' d') :
    MeasurePreserving f volume volume := by
  have low : ∀ L c c', (∀ q, ρ q < L → c q = c' q) → ∀ q, ρ q < L → f c q = f c' q := by
    intro L
    induction L using Nat.strong_induction_on with
    | _ L ih =>
      intro c c' hc q hq
      rw [hf c q, hf c' q, hc q hq]
      congr 1
      refine hG q _ _ _ _ fun q' hq' => ⟨hc q' (by omega), ?_⟩
      exact ih (ρ q) hq c c' (fun q'' h'' => hc q'' (by omega)) q' hq'
  have hfg : f = fun c p => ε p * c p + (f c p - ε p * c p) := by funext c p; ring
  rw [hfg]
  refine tri_mp ρ ε hε (fun p c => f c p - ε p * c p)
    (fun p => ((measurable_pi_apply p).comp hfm).sub (measurable_const.mul (measurable_pi_apply p))) ?_
  intro p c c' hc
  have e1 : f c p - ε p * c p = G p c (f c) := by rw [hf c p]; ring
  have e2 : f c' p - ε p * c' p = G p c' (f c') := by rw [hf c' p]; ring
  simp only [e1, e2]
  exact hG p _ _ _ _ fun q hq => ⟨hc q hq, low (ρ p) c c' hc q hq⟩

end Tri

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def extC (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (a b : Fin (D.R.rS + 1)) : ℂ :=
  if h : a < b ∧ blkOf w.1 a.1 = blkOf w.1 b.1 then c ⟨(a, b), h⟩ else 0

def coordMul (w : Point D.host.E (D.R.rS + 1)) (c d : FreeE w → ℂ) : FreeE w → ℂ :=
  fun p => c p + d p + ∑ m, extC w c p.1.1 m * extC w d m p.1.2

def gapE (w : Point D.host.E (D.R.rS + 1)) (p : FreeE w) : ℕ := p.1.2.val - p.1.1.val

theorem extC_measurable (w : Point D.host.E (D.R.rS + 1)) (a b : Fin (D.R.rS + 1)) :
    Measurable fun c : FreeE w → ℂ => extC w c a b := by
  unfold extC
  by_cases h : a < b ∧ blkOf w.1 a.1 = blkOf w.1 b.1
  · simp only [dif_pos h]
    exact measurable_pi_apply _
  · simp only [dif_neg h]
    exact measurable_const

theorem extC_of_not_lt (w : Point D.host.E (D.R.rS + 1)) (c : FreeE w → ℂ) (a b : Fin (D.R.rS + 1)) (h : ¬ a < b) :
    extC w c a b = 0 := by
  unfold extC
  rw [dif_neg (fun h' => h h'.1)]

theorem extC_congr (w : Point D.host.E (D.R.rS + 1)) (c c' : FreeE w → ℂ) (a b : Fin (D.R.rS + 1)) (L : ℕ)
    (hL : b.val - a.val < L) (hc : ∀ q, gapE w q < L → c q = c' q) : extC w c a b = extC w c' a b := by
  unfold extC
  split_ifs with h
  · exact hc ⟨(a, b), h⟩ hL
  · rfl

theorem nV_one (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ NV X u v := by
  show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)))
  have : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := by simp [uMat]
  rw [this]; exact ⟨Formalism.L2.SG.Pf.inFl_one _, fun y _ => by simp⟩

theorem nV_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s t : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ NV X u v) (ht : t ∈ NV X u v) : s * t ∈ NV X u v := by
  show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat (s * t))
  have : uMat (s * t) = uMat s * uMat t := by simp [uMat]
  rw [this]
  exact ⟨Formalism.L2.SG.Pf.inFl_mul hs.1 ht.1,
    fun y hy => Formalism.L2.SG.Pf.fl_mul (Formalism.L2.SG.Pf.fl_map_le hs.1.1 D.R.rS) (hs.2 y hy) (ht.2 y hy)⟩

theorem nV_inv (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ NV X u v) : s⁻¹ ∈ NV X u v := by
  show Formalism.L2.SG.HidaSetting.InN _ _ _ (uMat s⁻¹)
  have : uMat s⁻¹ * uMat s = 1 := by simp [uMat]
  exact ⟨Formalism.L2.SG.Pf.inFl_inv this hs.1,
    fun y hy => Formalism.L2.SG.Pf.fl_inv this (Formalism.L2.SG.Pf.fl_le_map hs.1.1 D.R.rS) (hs.2 y hy)⟩

theorem stV_one (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ StV X u u' γ v := by
  refine ⟨nV_one X u v, ?_⟩
  simp only [mul_one, inv_mul_cancel]
  exact nV_one X u' v

theorem stV_mul (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F)
    (s t : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ StV X u u' γ v) (ht : t ∈ StV X u u' γ v) :
    s * t ∈ StV X u u' γ v := by
  refine ⟨nV_mul X u v s t hs.1 ht.1, ?_⟩
  have e : (γ v)⁻¹ * (s * t) * γ v = ((γ v)⁻¹ * s * γ v) * ((γ v)⁻¹ * t * γ v) := by group
  rw [e]
  exact nV_mul X u' v _ _ hs.2 ht.2

theorem stV_inv (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F)
    (s : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ StV X u u' γ v) : s⁻¹ ∈ StV X u u' γ v := by
  refine ⟨nV_inv X u v s hs.1, ?_⟩
  have e : (γ v)⁻¹ * s⁻¹ * γ v = ((γ v)⁻¹ * s * γ v)⁻¹ := by group
  rw [e]
  exact nV_inv X u' v _ hs.2

theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (c • y) = c * Formalism.L2.SG.HidaSetting.hJ ε x y := by
  simp [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem stCoordV_one (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) : stCoordV X u' w γ v 1 = 0 := by
  funext p
  rcases p with ⟨⟨a, b⟩, hab, hbl⟩
  simp only [stCoordV, mul_one, inv_mul_cancel]
  have h1 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := by simp [uMat]
  rw [h1, Matrix.one_mulVec]
  apply mul_eq_zero_of_right
  simp only [frm, famSc]
  rw [hJ_smul_r]
  apply mul_eq_zero_of_right
  induction b using Fin.lastCases with
  | last =>
    rw [fam_last, Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hermitian_f_z_zero, map_zero]
  | cast b' =>
    rw [fam_castSucc, Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hE_f_e, if_neg, map_zero]
    intro h
    have h2 := congrArg Fin.val h
    simp only at h2
    rw [Fin.lt_def] at hab
    simp at hab
    omega

def StVLaw (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    ∀ y ∈ StV X u u' (gamW X u u' w) v, ∀ y' ∈ StV X u u' (gamW X u u' w) v,
      stCoordV X u' w (gamW X u u' w) v (y * y') =
        coordMul w (stCoordV X u' w (gamW X u u' w) v y) (stCoordV X u' w (gamW X u u' w) v y')

section LawLoc

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_T_e (e f : Fin r → Fin n → ℂ) (z' : Fin n → ℂ)
    (hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (f a) (e b) = if b = a then 1 else 0)
    (hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z' = 0) (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : Formalism.L2.SG.HidaSetting.InS e z' T) (a c : Fin r) :
    Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) = (if c = a then 1 else 0) +
      (if a.castSucc < c.castSucc then Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) else 0) := by
  have h := flag_expand ε e f z' hfe hfz' T hT c.castSucc
  rw [fam_castSucc] at h
  have h2 := congrArg (Formalism.L2.SG.HidaSetting.hJ ε (f a)) h
  rw [hJ_add_r', hJ_sum_r', hfe] at h2
  rw [Finset.sum_eq_single a] at h2
  · rw [hfe, if_pos rfl, mul_one] at h2
    exact h2
  · intro d _ hda; rw [hfe, if_neg hda, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem flag_mul_coef (e f : Fin r → Fin n → ℂ) (z' : Fin n → ℂ)
    (hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (f a) (e b) = if b = a then 1 else 0)
    (hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z' = 0) (T T' : Matrix (Fin n) (Fin n) ℂ)
    (hT : Formalism.L2.SG.HidaSetting.InS e z' T) (hT' : Formalism.L2.SG.HidaSetting.InS e z' T') (a : Fin r) (b : Fin (r + 1))
    (hab : a.castSucc < b) :
    Formalism.L2.SG.HidaSetting.hJ ε (f a) ((T * T') *ᵥ fam e z' b) =
      Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ fam e z' b) + Formalism.L2.SG.HidaSetting.hJ ε (f a) (T' *ᵥ fam e z' b) +
      ∑ c : Fin r, if a.castSucc < c.castSucc ∧ c.castSucc < b then
        Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) * Formalism.L2.SG.HidaSetting.hJ ε (f c) (T' *ᵥ fam e z' b) else 0 := by
  have h := flag_expand ε e f z' hfe hfz' T' hT' b
  have h1 := congrArg (fun x => T *ᵥ x) h
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul] at h1
  rw [← Matrix.mulVec_mulVec, h1, hJ_add_r', hJ_sum_r', add_assoc]
  congr 1
  have hterm : ∀ c : Fin r, (if c.castSucc < b then Formalism.L2.SG.HidaSetting.hJ ε (f c) (T' *ᵥ fam e z' b) else 0) *
      Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) =
      (if c = a then Formalism.L2.SG.HidaSetting.hJ ε (f a) (T' *ᵥ fam e z' b) else 0) +
      (if a.castSucc < c.castSucc ∧ c.castSucc < b then
        Formalism.L2.SG.HidaSetting.hJ ε (f a) (T *ᵥ e c) * Formalism.L2.SG.HidaSetting.hJ ε (f c) (T' *ᵥ fam e z' b) else 0) := by
    intro c
    have hc := hJ_T_e ε e f z' hfe hfz' T hT a c
    by_cases hca : c = a
    · subst hca
      rw [if_neg (lt_irrefl _), add_zero, if_pos rfl] at hc
      rw [if_pos hab, hc, if_pos rfl, if_neg (fun h => lt_irrefl _ h.1)]; ring
    · rw [if_neg hca, zero_add] at hc
      rw [if_neg hca, zero_add]
      by_cases hac : a.castSucc < c.castSucc
      · by_cases hcb : c.castSucc < b
        · rw [if_pos hcb, if_pos ⟨hac, hcb⟩]; ring
        · rw [if_neg hcb, if_neg (fun h => hcb h.2), zero_mul]
      · rw [if_neg hac] at hc
        rw [hc, mul_zero, if_neg (fun h => hac h.1)]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end LawLoc

theorem blkOf_mono {K : Type*} : ∀ (bs : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf bs i ≤ blkOf bs j
  | [], _, _, _ => by simp [blkOf]
  | (t, s) :: bs, i, j, h => by
    simp only [blkOf]
    split_ifs with h1 h2 h2
    · exact le_refl _
    · omega
    · omega
    · have := blkOf_mono bs (i - s) (j - s) (by omega); omega

theorem rdE_pos_c : (0 : ℝ) < D.host.rdE :=
  Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))) _

theorem stCoordV_apply (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (y : Formalism.REAL.UJ (X.B.I.ε v)) (p : FreeE w) :
    stCoordV X u' w γ v y p = ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) * ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.1))⁻¹) *
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR ⟨p.1.1.1, by have := p.2.1; omega⟩))
        (uMat ((γ v)⁻¹ * y * γ v) *ᵥ
          fam (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) p.1.2) := by
  simp only [stCoordV, frm, famSc, Matrix.mulVec_smul, hJ_smul_r]
  ring

theorem stVLaw_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StVLaw X u u' := by
  classical
  intro w _ v y hy y' hy'
  set γ := gamW X u u' w
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)
  set f : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)
  set z' := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')
  have hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (f a) (e b) = if b = a then 1 else 0 := by
    intro a b
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hE_f_e]
    split_ifs <;> simp
  have hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (f a) z' = 0 := by
    intro a
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hermitian_f_z_zero, map_zero]
  have hT : Formalism.L2.SG.HidaSetting.InS e z' (uMat ((γ v)⁻¹ * y * γ v)) := hy.2.1
  have hT' : Formalism.L2.SG.HidaSetting.InS e z' (uMat ((γ v)⁻¹ * y' * γ v)) := hy'.2.1
  have hprod : uMat ((γ v)⁻¹ * (y * y') * γ v) = uMat ((γ v)⁻¹ * y * γ v) * uMat ((γ v)⁻¹ * y' * γ v) := by
    have e1 : (γ v)⁻¹ * (y * y') * γ v = ((γ v)⁻¹ * y * γ v) * ((γ v)⁻¹ * y' * γ v) := by group
    rw [e1]; simp [uMat]
  have hx : (D.host.rdE : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (rdE_pos_c (D := D)).ne'
  let S : ℕ → ℕ → ℂ := fun a b => (D.host.rdE : ℂ) ^ (D.R.rS - a) * ((D.host.rdE : ℂ) ^ (D.R.rS - b))⁻¹
  have hS : ∀ a c b, S a c * S c b = S a b := by
    intro a c b
    simp only [S]
    rw [mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hx)]
  funext p
  have hab : p.1.1 < p.1.2 := p.2.1
  have hbl : blkOf w.1 p.1.1.1 = blkOf w.1 p.1.2.1 := p.2.2
  obtain ⟨a', ha'⟩ : ∃ a' : Fin D.R.rS, a'.castSucc = p.1.1 :=
    ⟨⟨p.1.1.val, by have h : p.1.1.val < p.1.2.val := hab; have := p.1.2.2; omega⟩, Fin.ext rfl⟩
  have hfa : (⟨p.1.1.1, by have h : p.1.1.val < p.1.2.val := hab; have := p.1.2.2; omega⟩ : Fin D.R.rS) = a' :=
    Fin.ext (congrArg Fin.val ha').symm
  simp only [coordMul]
  rw [stCoordV_apply X u' w γ v (y * y'), stCoordV_apply X u' w γ v y, stCoordV_apply X u' w γ v y', hprod]
  simp only [hfa]
  have hF := flag_mul_coef (X.B.I.ε v) e f z' hfe hfz' _ _ hT hT' a' p.1.2 (by rw [ha']; exact hab)
  rw [ha'] at hF
  rw [hF, Fin.sum_univ_castSucc, extC_of_not_lt w _ (Fin.last _) p.1.2 (fun h => absurd (Fin.le_last _) (not_le.2 h)),
    mul_zero, add_zero, mul_add, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : p.1.1 < c.castSucc ∧ c.castSucc < p.1.2
  · rw [if_pos hc]
    have hb1 : blkOf w.1 p.1.1.1 = blkOf w.1 c.castSucc.1 := by
      have h1 := blkOf_mono w.1 p.1.1.1 c.castSucc.1 (le_of_lt hc.1)
      have h2 := blkOf_mono w.1 c.castSucc.1 p.1.2.1 (le_of_lt hc.2)
      omega
    have hb2 : blkOf w.1 c.castSucc.1 = blkOf w.1 p.1.2.1 := by rw [← hb1]; exact hbl
    have hfc : (⟨c.castSucc.val, by have h : c.castSucc.val < p.1.2.val := hc.2; have := p.1.2.2; omega⟩ : Fin D.R.rS) = c :=
      Fin.ext rfl
    unfold extC
    rw [dif_pos ⟨hc.1, hb1⟩, dif_pos ⟨hc.2, hb2⟩]
    refine Eq.trans ?_ (congrArg₂ (· * ·) (stCoordV_apply X u' w γ v y _).symm (stCoordV_apply X u' w γ v y' _).symm)
    dsimp only
    simp only [hfa, hfc, fam_castSucc]
    have h3 := hS p.1.1.1 c.castSucc.1 p.1.2.1
    simp only [S] at h3
    rw [← h3]
    simp only [e, f, z']
    ring
  · rw [if_neg hc, mul_zero]
    by_cases hac : p.1.1 < c.castSucc
    · have hcb : ¬ c.castSucc < p.1.2 := fun h => hc ⟨hac, h⟩
      rw [extC_of_not_lt w _ _ _ hcb, mul_zero]
    · rw [extC_of_not_lt w _ _ _ hac, zero_mul]

def StVChart (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    ∃ φ : (FreeE w → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Continuous φ ∧
      (∀ c, φ c ∈ StV X u u' (gamW X u u' w) v) ∧
      (∀ y ∈ StV X u u' (gamW X u u' w) v, φ (stCoordV X u' w (gamW X u u' w) v y) = y) ∧
      (∀ c, stCoordV X u' w (gamW X u u' w) v (φ c) = c)

theorem mp_one_mul : MeasurePreserving (fun x : ℂ => (1 : ℂ) * x) volume volume := by
  have e : (fun x : ℂ => (1 : ℂ) * x) = id := funext fun x => one_mul x
  rw [e]
  exact MeasurePreserving.id _

theorem mp_neg_one_mul : MeasurePreserving (fun x : ℂ => (-1 : ℂ) * x) volume volume := by
  have e : (fun x : ℂ => (-1 : ℂ) * x) = fun x => -x := funext fun x => by ring
  rw [e]
  exact Measure.measurePreserving_neg volume

theorem stVGeo_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hC : StVChart X u u')
    (hLw : StVLaw X u u') : StVGeo X u u' := by
  classical
  intro w hw v
  obtain ⟨φ, hφ, hφS, hφκ, hκφ⟩ := hC w hw v
  have law := hLw w hw v
  set γ := gamW X u u' w with hγ
  set κ := stCoordV X u' w γ v with hκ
  refine ⟨⟨stV_one X u u' γ v, fun s hs t ht => stV_mul X u u' γ v s t hs ht,
    fun s hs => stV_inv X u u' γ v s hs⟩, φ, hφ, hφS, hφκ, hκφ, ?_, ?_⟩
  ·
    intro s hs
    have e1 : (fun c => κ (s * φ c)) = fun c p => (1 : ℂ) * c p +
        (κ s p + ∑ m, extC w (κ s) p.1.1 m * extC w c m p.1.2) := by
      funext c p
      rw [law s hs (φ c) (hφS c), hκφ c, coordMul]
      ring
    rw [e1]
    refine tri_mp (gapE w) (fun _ => 1) (fun _ => mp_one_mul) _ (fun p => measurable_const.add
      (Finset.measurable_sum _ fun m _ => measurable_const.mul (extC_measurable w m p.1.2))) ?_
    intro p c c' hc
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases ham : p.1.1 < m
    · rw [extC_congr w c c' m p.1.2 (gapE w p) ?_ hc]
      have := p.2.1
      rw [Fin.lt_def] at ham this
      simp only [gapE]
      omega
    · rw [extC_of_not_lt w _ _ _ ham, zero_mul, zero_mul]
  ·
    have hκ1 : κ 1 = 0 := stCoordV_one X u' w γ v
    refine tri_mp' (gapE w) (fun _ => -1) (fun _ => mp_neg_one_mul) (fun c => κ (φ c)⁻¹)
      ((stCoordV_continuous X u' w γ v).comp hφ.inv).measurable
      (fun p c d => - ∑ m, extC w d p.1.1 m * extC w c m p.1.2) ?_ ?_
    · intro c p
      have h := law (φ c)⁻¹ (stV_inv X u u' γ v _ (hφS c)) (φ c) (hφS c)
      rw [inv_mul_cancel, hκ1, hκφ c] at h
      have hp := congrFun h p
      simp only [coordMul, Pi.zero_apply] at hp
      linear_combination -hp
    · intro p c d c' d' hcd
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hp := p.2.1
      rw [Fin.lt_def] at hp
      by_cases ham : p.1.1 < m
      · by_cases hmb : m < p.1.2
        · rw [Fin.lt_def] at ham hmb
          rw [extC_congr w d d' p.1.1 m (gapE w p) (by simp only [gapE]; omega) (fun q hq => (hcd q hq).2),
            extC_congr w c c' m p.1.2 (gapE w p) (by simp only [gapE]; omega) (fun q hq => (hcd q hq).1)]
        · rw [extC_of_not_lt w c m p.1.2 hmb, extC_of_not_lt w c' m p.1.2 hmb, mul_zero, mul_zero]
      · rw [extC_of_not_lt w d _ _ ham, extC_of_not_lt w d' _ _ ham, zero_mul, zero_mul]

theorem stVGeo_of_chart (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hC : StVChart X u u') :
    StVGeo X u u' := stVGeo_of X u u' hC (stVLaw_holds X u u')

def StVKer (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F, ∀ y ∈ StV X u u' (gamW X u u' w) v,
    stCoordV X u' w (gamW X u u' w) v y = 0 → y = 1

def StVSec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F,
    ∃ φ : (FreeE w → ℂ) → Formalism.REAL.UJ (X.B.I.ε v), Continuous φ ∧
      (∀ c, φ c ∈ StV X u u' (gamW X u u' w) v) ∧ (∀ c, stCoordV X u' w (gamW X u u' w) v (φ c) = c)

theorem stVChart_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hK : StVKer X u u')
    (hS : StVSec X u u') : StVChart X u u' := by
  intro w hw v
  obtain ⟨φ, hφ, hφS, hκφ⟩ := hS w hw v
  refine ⟨φ, hφ, hφS, fun y hy => ?_, hκφ⟩
  have law := stVLaw_holds X u u' w hw v
  have hinj : ∀ y ∈ StV X u u' (gamW X u u' w) v, ∀ y' ∈ StV X u u' (gamW X u u' w) v,
      stCoordV X u' w (gamW X u u' w) v y = stCoordV X u' w (gamW X u u' w) v y' → y = y' := by
    intro y hy y' hy' he
    have hi := stV_inv X u u' (gamW X u u' w) v y' hy'
    have h1 := law y'⁻¹ hi y hy
    have h2 := law y'⁻¹ hi y' hy'
    rw [inv_mul_cancel, stCoordV_one, ← he] at h2
    rw [← h2] at h1
    have := hK w hw v (y'⁻¹ * y) (stV_mul X u u' _ v _ _ hi hy) h1
    rw [inv_mul_eq_one] at this
    exact this.symm
  exact hinj _ (hφS _) y hy (hκφ _)

theorem stVGeo_of_ker_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hK : StVKer X u u')
    (hS : StVSec X u u') : StVGeo X u u' := stVGeo_of_chart X u u' (stVChart_of X u u' hK hS)

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem blkOf_ptPar {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x : ℕ), x < (bs.map Prod.snd).sum →
    blkOf bs (ptPar bs x) = blkOf bs x
  | [], x, hx => by simp at hx
  | (t, s) :: bs, x, hx => by
    simp only [List.map_cons, List.sum_cons] at hx
    rw [ptPar_cons]
    by_cases hxs : x < s
    · rw [if_pos hxs]; simp only [blkOf]; rw [if_pos (by omega), if_pos hxs]
    · rw [if_neg hxs]; simp only [blkOf]
      rw [if_neg (by omega), if_neg hxs, show s + ptPar bs (x - s) - s = ptPar bs (x - s) by omega,
        blkOf_ptPar bs (x - s) (by omega)]

theorem ptPar_lt_of_blk {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (x y : ℕ), x < (bs.map Prod.snd).sum →
    y < (bs.map Prod.snd).sum → blkOf bs x < blkOf bs y → ptPar bs x < ptPar bs y
  | [], x, _, hx, _, _ => by simp at hx
  | (t, s) :: bs, x, y, hx, hy, h => by
    simp only [List.map_cons, List.sum_cons] at hx hy
    simp only [blkOf] at h
    rw [ptPar_cons, ptPar_cons]
    by_cases hxs : x < s
    · by_cases hys : y < s
      · rw [if_pos hxs, if_pos hys] at h; omega
      · rw [if_pos hxs, if_neg hys]; omega
    · by_cases hys : y < s
      · rw [if_neg hxs, if_pos hys] at h; omega
      · rw [if_neg hxs, if_neg hys] at h ⊢
        have := ptPar_lt_of_blk bs (x - s) (y - s) (by omega) (by omega) (by omega)
        omega

def StVFix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ v : InfinitePlace X.B.I.F, ∀ y ∈ StV X u u' (gamW X u u' w) v,
    (∀ a, uMat y *ᵥ fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) a =
      fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) a) →
    (∀ b, uMat y *ᵥ (uMat (gamW X u u' w v) *ᵥ
        fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) =
      uMat (gamW X u u' w v) *ᵥ
        fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) →
    y = 1

private theorem flag_fix_lemma {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (f a) (e b) = if b = a then 1 else 0)
    (hfz : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z = 0) (hfz' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (f a) z' = 0)
    (S Si G T : Matrix (Fin n) (Fin n) ℂ) (hSi : Formalism.L2.SG.HidaSetting.InS e z Si)
    (hT : Formalism.L2.SG.HidaSetting.InS e z' T)
    (hadj : ∀ x y, Formalism.L2.SG.HidaSetting.hJ ε x (S *ᵥ y) = Formalism.L2.SG.HidaSetting.hJ ε (Si *ᵥ x) y)
    (hrel : S * G = G * T) (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hZ : ∀ c b, Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hfree : ∀ (c : Fin r) (b : Fin (r + 1)), c.castSucc < b →
      π c.castSucc < π b ∨ Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) = 0) :
    (∀ b, T *ᵥ fam e z' b = fam e z' b) ∧ (∀ a, Si *ᵥ fam e z a = fam e z a) := by
  have hA := relA_loc ε e f z z' hfe hfz hfz' S Si G T hSi hT hadj hrel
  have hTc : ∀ (c : Fin r) (b : Fin (r + 1)), c.castSucc < b →
      Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) = 0 := by
    intro c b hcb
    rcases hfree c b hcb with hlt | h0
    · have h := hA (π c.castSucc) b
      have hL : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then
          conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z (π c.castSucc))) * Zhat ε (fam e z) (fam e z') G c'.castSucc b
          else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro c' _
        split_ifs with h1
        · have hz : Zhat ε (fam e z) (fam e z') G c'.castSucc b = 0 := by
            by_contra hne
            rw [(hZ _ _).1 hne] at h1
            exact lt_irrefl _ (lt_trans h1 hlt)
          rw [hz, mul_zero]
        · rfl
      have hR : (∑ c' : Fin r, if c'.castSucc < b then
          Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc else 0) =
          Formalism.L2.SG.HidaSetting.hJ ε (f c) (T *ᵥ fam e z' b) * Zhat ε (fam e z) (fam e z') G (π c.castSucc) c.castSucc := by
        rw [Finset.sum_eq_single c]
        · rw [if_pos hcb]
        · intro c' _ hc'
          split_ifs
          · have hz : Zhat ε (fam e z) (fam e z') G (π c.castSucc) c'.castSucc = 0 := by
              by_contra hne
              have h2 := (hZ _ _).1 hne
              have h3 : c.castSucc = c'.castSucc := by rw [← hπ c.castSucc, h2, hπ]
              exact hc' (Fin.castSucc_injective _ h3).symm
            rw [hz, mul_zero]
          · rfl
        · intro h; exact absurd (Finset.mem_univ c) h
      rw [hL, hR] at h
      exact (mul_eq_zero.1 h.symm).resolve_right ((hZ _ _).2 rfl)
    · exact h0
  have hSc : ∀ (c : Fin r) (a : Fin (r + 1)), c.castSucc < a →
      Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a) = 0 := by
    intro c a hca
    have h := hA a (π c.castSucc)
    have hR : (∑ c' : Fin r, if c'.castSucc < π c.castSucc then
        Formalism.L2.SG.HidaSetting.hJ ε (f c') (T *ᵥ fam e z' (π c.castSucc)) * Zhat ε (fam e z) (fam e z') G a c'.castSucc else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c' _
      split_ifs with h1
      · rw [hTc c' _ h1, zero_mul]
      · rfl
    have hL : (∑ c' : Fin r, if c'.castSucc < a then
        conj (Formalism.L2.SG.HidaSetting.hJ ε (f c') (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) else 0) =
        conj (Formalism.L2.SG.HidaSetting.hJ ε (f c) (Si *ᵥ fam e z a)) * Zhat ε (fam e z) (fam e z') G c.castSucc (π c.castSucc) := by
      rw [Finset.sum_eq_single c]
      · rw [if_pos hca]
      · intro c' _ hc'
        split_ifs
        · have hz : Zhat ε (fam e z) (fam e z') G c'.castSucc (π c.castSucc) = 0 := by
            by_contra hne
            have h2 := (hZ _ _).1 hne
            rw [hπ] at h2
            exact hc' (Fin.castSucc_injective _ h2)
          rw [hz, mul_zero]
        · rfl
      · intro h; exact absurd (Finset.mem_univ c) h
    rw [hL, hR] at h
    have h4 := (mul_eq_zero.1 h).resolve_right ((hZ _ _).2 (hπ _).symm)
    simpa using h4
  refine ⟨fun b => ?_, fun a => ?_⟩
  · rw [flag_expand ε e f z' hfe hfz' T hT b]
    conv_rhs => rw [← add_zero (fam e z' b)]
    congr 1
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with h1
    · rw [hTc c b h1, zero_smul]
    · rw [zero_smul]
  · rw [flag_expand ε e f z hfe hfz Si hSi a]
    conv_rhs => rw [← add_zero (fam e z a)]
    congr 1
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with h1
    · rw [hSc c a h1, zero_smul]
    · rw [zero_smul]

theorem stVKer_of_fix (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hFx : StVFix X u u') :
    StVKer X u u' := by
  intro w hw v y hy h0
  have hγ : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dite_eq_left hw.1]
    exact hw.1.choose_spec
  have hfe : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR b)) = if b = a then 1 else 0 := by
    intro a b
    change Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a)))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.eX b))) = _
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.eX b), Formalism.L2.SG.PoincareInHH.Cut.hT_f_e X a b]
    split_ifs <;> simp
  have hfz : ∀ (u₀ : D.what₂.Word) a, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v)
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u₀)) = 0 := by
    intro u₀ a
    change Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.fY a)))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.crd (X.zu u₀))) = 0
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v (X.fY a) (X.zu u₀), (X.zu_orth u₀ a).2, map_zero]
  have hy' := hy
  obtain ⟨hyN, hyN'⟩ := hy'
  have hSi : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) (uMat y⁻¹) := by
    obtain ⟨h1, _⟩ := nV_inv X u v y hyN
    exact h1
  have hT : Formalism.L2.SG.HidaSetting.InS (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v)) := by
    obtain ⟨h1, _⟩ := hyN'
    exact h1
  have hrel : uMat y * uMat (gamW X u u' w v) =
      uMat (gamW X u u' w v) * uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) := by
    rw [← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul, ← Formalism.L2.SG.PoincareInHH.Cut.uMat_mul]
    congr 1
    group
  have hlen : ∀ b : Fin (D.R.rS + 1), b.1 < (w.1.map Prod.snd).sum := fun b => by
    rw [w.2.2]; exact b.2
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.1, by have h := ptPar_lt w.1 b.1 (hlen b); rwa [w.2.2] at h⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.1 (hlen a))
  have hZ : ∀ c b, Zhat (X.B.I.ε v) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))) (fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
      (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u'))) (uMat (gamW X u u' w v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    have h1 := congrFun (congrFun (hγ v) c) b
    simp only [RealObj.ZhatO, ZX, frm, famSc_one, ptC, Matrix.map_apply, ptMat] at h1
    rw [ptEntry_eq w.1 c.1 b.1 (hlen b)] at h1
    have hsgn : ((-1 : ℂ) ^ (D.R.rS - b.1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    constructor
    · intro hne
      by_contra hcb
      have hv : c.1 ≠ ptPar w.1 b.1 := fun h => hcb (Fin.ext h)
      rw [if_neg hv, map_zero, map_zero] at h1
      exact hne ((mul_eq_zero.1 h1).resolve_left hsgn)
    · intro hcb hz
      have hv : c.1 = ptPar w.1 b.1 := congrArg Fin.val hcb
      rw [if_pos hv, hz, mul_zero] at h1
      exact ptSc_ne w.1 (fun x hx => w.2.1 x hx) b.1 (hlen b) (by simpa using h1.symm)
  have hfree : ∀ (c : Fin D.R.rS) (b : Fin (D.R.rS + 1)), c.castSucc < b →
      π c.castSucc < π b ∨ Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c))
        (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) *ᵥ
          fam (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) b) = 0 := by
    intro c b hcb
    by_cases hbl : blkOf w.1 c.castSucc.1 = blkOf w.1 b.1
    · right
      have hp := congrFun h0 ⟨(c.castSucc, b), hcb, hbl⟩
      simp only [stCoordV, frm, famSc, Matrix.mulVec_smul, hJ_smul_r, Fin.val_castSucc,
        Fin.eta] at hp
      have hrd : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (rdE_pos_c (D := D)).ne'
      rcases mul_eq_zero.1 hp with h | h
      · exact absurd h (pow_ne_zero _ hrd)
      · rcases mul_eq_zero.1 h with h' | h'
        · exact absurd h' (inv_ne_zero (pow_ne_zero _ hrd))
        · exact h'
    · left
      have hle : blkOf w.1 c.castSucc.1 ≤ blkOf w.1 b.1 := blkOf_mono w.1 _ _ (le_of_lt hcb)
      exact ptPar_lt_of_blk w.1 _ _ (hlen _) (hlen _) (lt_of_le_of_ne hle hbl)
  obtain ⟨hTfix, hSfix⟩ := flag_fix_lemma (X.B.I.ε v) (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR c))
    (fun c => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.fR c)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u))
    (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')) hfe (hfz u) (hfz u') (uMat y) (uMat y⁻¹)
    (uMat (gamW X u u' w v)) (uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v)) hSi hT
    (fun x x' => Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj y x x') hrel π hπ hZ hfree
  have hyy : uMat y * uMat y⁻¹ = 1 := by
    have h := Formalism.L2.SG.PoincareInHH.Cut.uMat_inv_mul y⁻¹
    rwa [inv_inv] at h
  refine hFx w hw v y hy (fun a => ?_) (fun b => ?_)
  · rw [← hSfix a, Matrix.mulVec_mulVec, hyy, Matrix.one_mulVec, hSfix a]
  · rw [Matrix.mulVec_mulVec, hrel, ← Matrix.mulVec_mulVec, hTfix b]

theorem stVGeo_of_fix_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hFx : StVFix X u u')
    (hS : StVSec X u u') : StVGeo X u u' :=
  stVGeo_of_ker_sec X u u' (stVKer_of_fix X u u' hFx) hS

end Formalism.L2.SG.Pf.Carrier.JointQuot
