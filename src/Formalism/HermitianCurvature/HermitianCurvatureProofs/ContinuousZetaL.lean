module

public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MrelConjTranspose
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftVectorZeroBlock
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def shS (l : Fin ρ) : Fin (1 + ρ) := ⟨l.val + 1, by omega⟩

theorem consC_sh (t : ℂ) (c : Fin ρ → ℂ) (l : Fin ρ) : consC t c (shS l) = c l := by
  simp [consC, shS]

theorem consC_zero (t : ℂ) (c : Fin ρ → ℂ) : consC t c ⟨0, by omega⟩ = t := by
  simp [consC]

theorem omX_consC {t : ℂ} (ht : t ≠ 0) (c : Fin ρ → ℂ) : consC t c ∈ OmX (1 + ρ) ↔ c ∈ OmX ρ := by
  simp only [OmX, Set.mem_setOf_eq]
  constructor
  · intro h l
    have := h (shS l)
    rwa [consC_sh] at this
  · intro h l
    unfold consC
    split_ifs with hl
    · exact ht
    · exact h _

def trF {E : Type*} (t : ℂ) (Φ : Fn k (1 + ρ) E) : Fn k ρ E := fun c g => Φ (consC t c) (ιLev k 1 ρ g)

theorem ιLev_comp (g : Mx k 0) : ιLev k 1 ρ (ιLev k ρ 0 g) = ιLev k (1 + ρ) 0 g := by
  ext p q
  simp only [ιLev]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk] <;> omega)

theorem liftVec_comp (v : Fin (2 * 0 + k + 1) → ℂ) : liftVec k 1 ρ (liftVec k ρ 0 v) = liftVec k (1 + ρ) 0 v := by
  funext p
  simp only [liftVec]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk] <;> omega)

def blk0 (z : Fin (2 * ρ + k + 1) → ℂ) : Fin (2 * 0 + k + 1) → ℂ := fun j => z ⟨ρ + j.val, by omega⟩

theorem lift_vector_zero_block {z : Fin (2 * ρ + k + 1) → ℂ} (hz : inWb k ρ z) : liftVec k ρ 0 (blk0 z) = z := by
  funext p
  have hp := p.isLt
  unfold liftVec blk0
  split_ifs with h
  · congr 1
    ext
    simp only [Fin.val_mk]
    omega
  · exact (hz p (by omega)).symm

theorem ιLev_inj {g g' : Mx k ρ} (h : ιLev k 1 ρ g = ιLev k 1 ρ g') : g = g' := by
  ext a b
  have h1 := congrFun (congrFun h ⟨a.val + 1, by omega⟩) ⟨b.val + 1, by omega⟩
  have ha : a.val ≤ 2 * ρ + k := by have := a.isLt; omega
  have hb : b.val ≤ 2 * ρ + k := by have := b.isLt; omega
  simpa [ιLev, ha, hb] using h1

theorem glev_image_last (r : ℕ) : Glev k r (Fin.last r) = ιLev k r 0 '' UH (Hpk k 0) :=
  QnGlevImageW.glevImage_of PI.QnLevBasicsW.level_group_homomorphism PI.QnLevBasicsW.level_group_unitary_hermitian k r 0

theorem glev_iota (g : Mx k ρ) : ιLev k 1 ρ g ∈ Glev k (1 + ρ) (Fin.last (1 + ρ)) ↔ g ∈ Glev k ρ (Fin.last ρ) := by
  rw [glev_image_last, glev_image_last]
  constructor
  · rintro ⟨g0, hg0, he⟩
    exact ⟨g0, hg0, ιLev_inj ((ιLev_comp g0).trans he)⟩
  · rintro ⟨g0, hg0, rfl⟩
    exact ⟨g0, hg0, (ιLev_comp g0).symm⟩

theorem fvec_last (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem zeta_iota (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : Mx k ρ) :
    zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (ιLev k 1 ρ g) =
      zetaL k ρ z z' (Fin.last ρ) g := by
  unfold zetaL
  rw [fvec_last, fvec_last, fvec_last, fvec_last, PIQnLT.mulVec_liftVec, PIQnLT.herm_liftVec]

theorem tz_iota (z : Fin (2 * ρ + k + 1) → ℂ) : Tz k (1 + ρ) (liftVec k 1 ρ z) = Tz k ρ z := by
  unfold Tz; rw [PIQnLT.herm_liftVec]

theorem ggl_iota (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : Mx k ρ) :
    GGl k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (ιLev k 1 ρ g) = GGl k ρ z z' g := by
  unfold GGl; rw [zeta_iota, tz_iota, tz_iota]

theorem domR_iota {t : ℂ} (ht : t ≠ 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    (consC t c, ιLev k 1 ρ g) ∈ DomR k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') ↔ (c, g) ∈ DomR k ρ z z' := by
  show (consC t c ∈ OmX (1 + ρ) ∧ ιLev k 1 ρ g ∈ Glev k (1 + ρ) (Fin.last (1 + ρ)) ∧
      0 < GGl k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (ιLev k 1 ρ g)) ↔
    (c ∈ OmX ρ ∧ g ∈ Glev k ρ (Fin.last ρ) ∧ 0 < GGl k ρ z z' g)
  rw [omX_consC ht, glev_iota, ggl_iota]

theorem contDiff_consC (t : ℂ) : ContDiff ℝ ∞ (consC (ρ := ρ) t) := by
  refine contDiff_pi.2 (fun l => ?_)
  by_cases h : l.val = 0
  · simp only [consC, h, ↓reduceDIte]
    exact contDiff_const
  · simp only [consC, h, ↓reduceDIte]
    exact contDiff_pi.1 contDiff_id _

theorem contDiff_ιLev : ContDiff ℝ ∞ (ιLev k 1 ρ) := by
  refine contDiff_pi.2 (fun p => contDiff_pi.2 (fun q => ?_))
  unfold ιLev
  split_ifs
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_id _) _
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem trF_mem {t : ℂ} (ht : t ≠ 0) {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)}
    {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)} {Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    trF t Φ ∈ RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)) := by
  obtain ⟨h0, hs, he⟩ := hΦ
  refine ⟨fun x hx => h0 _ fun h => hx ((domR_iota ht z z' x.1 x.2).1 h), fun x₀ hx₀ => ?_,
    fun x hx h hh h' hh' => ?_⟩
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hs _ ((domR_iota ht z z' x₀.1 x₀.2).2 hx₀)
    let e : (Fin ρ → ℂ) × Mx k ρ → (Fin (1 + ρ) → ℂ) × Mx k (1 + ρ) := fun x => (consC t x.1, ιLev k 1 ρ x.2)
    have he_c : ContDiff ℝ ∞ e :=
      ((contDiff_consC t).comp contDiff_fst).prodMk (contDiff_ιLev.comp contDiff_snd)
    refine ⟨e ⁻¹' U, F ∘ e, hU.preimage he_c.continuous, hxU, hF.comp he_c.contDiffOn (fun x hx => hx),
      fun x hx hg => ?_⟩
    exact hΦF (e x) hx ((glev_iota x.2).2 hg)
  · have hx' := (domR_iota ht z z' x.1 x.2).2 hx
    show Φ (consC t x.1) (ιLev k 1 ρ (h * x.2 * h')) = _
    rw [(PI.QnLevBasicsW.level_group_homomorphism k 1 ρ).2, (PI.QnLevBasicsW.level_group_homomorphism k 1 ρ).2]
    exact he _ hx' _ (PI.QnLevBasicsW.level_group_unitary_weyl k 1 ρ z h hh) _ (PI.QnLevBasicsW.level_group_unitary_weyl k 1 ρ z' h' hh')

def trL {t : ℂ} (ht : t ≠ 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp))
    (π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)) :
    RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π' →ₗ[ℂ]
      RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)) where
  toFun Φ := ⟨trF t (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)), trF_mem ht Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem trL_apply {t : ℂ} (ht : t ≠ 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp))
    (π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)) (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    ((trL ht z z' π π' Φ : RadSp k ρ z z' _ _) : Fn k ρ (Wq →L[ℂ] Wp)) = trF t (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) := rfl

theorem tL_iota {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : inWb k ρ z) (hz' : inWb k ρ z') (Y : ℂ) (a b : Fin 2) (f : Mx k (1 + ρ) → E) {g : Mx k ρ}
    (hg : g ∈ Glev k ρ (Fin.last ρ)) :
    tL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) Y a b f (ιLev k 1 ρ g) =
      tL k ρ z z' (Fin.last ρ) Y a b (fun x => f (ιLev k 1 ρ x)) g := by
  rw [glev_image_last] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨z0, rfl⟩ : ∃ z0, z = liftVec k ρ 0 z0 := ⟨blk0 z, (lift_vector_zero_block hz).symm⟩
  obtain ⟨z0', rfl⟩ : ∃ z0', z' = liftVec k ρ 0 z0' := ⟨blk0 z', (lift_vector_zero_block hz').symm⟩
  have e1 := Formalism.FourierDecayAlt.P.level_transfer E k (1 + ρ) 0 z0 z0' Y a b f g0 hg0
  have e2 := Formalism.FourierDecayAlt.P.level_transfer E k ρ 0 z0 z0' Y a b (fun x => f (ιLev k 1 ρ x)) g0 hg0
  have e3 : (fun x => f (ιLev k 1 ρ (ιLev k ρ 0 x))) = fun x => f (ιLev k (1 + ρ) 0 x) :=
    funext fun x => by rw [ιLev_comp]
  rw [liftVec_comp, liftVec_comp, ιLev_comp]
  calc _ = _ := e1
    _ = _ := by rw [← e3]; exact e2.symm

theorem diff_rad {r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') (g : Mx k r) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    DifferentiableAt ℝ (fun c' => Φ c' g) c := by
  by_cases hx : (c, g) ∈ DomR k r z z'
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 (c, g) hx
    have hU' : IsOpen ((fun c' => (c', g)) ⁻¹' U) := hU.preimage (continuous_id.prodMk continuous_const)
    have hd : DifferentiableAt ℝ (fun c' => F (c', g)) c :=
      ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)).comp c
        ((differentiableAt_id).prodMk (differentiableAt_const _))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hU'.mem_nhds (show (c, g) ∈ U from hxU)] with c' hc'
    exact hΦF (c', g) hc' hx.2.1
  · have h0 : (fun c' => Φ c' g) = fun _ => 0 := by
      funext c'
      refine hΦ.1 (c', g) fun h => hx ⟨hc, h.2.1, h.2.2⟩
    rw [h0]; exact differentiableAt_const _

def insL : (Fin ρ → ℂ) →L[ℝ] (Fin (1 + ρ) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := consC 0
      map_add' := fun u v => by
        ext l; simp only [consC, Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun a v => by
        ext l; simp only [consC, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }

theorem insL_apply (v : Fin ρ → ℂ) : insL v = consC 0 v := rfl

theorem hasFDerivAt_consC (t : ℂ) (c : Fin ρ → ℂ) : HasFDerivAt (consC t) (insL (ρ := ρ)) c := by
  have e : consC (ρ := ρ) t = fun c' => insL c' + consC t 0 := by
    funext c' l
    simp only [insL_apply, consC, Pi.add_apply]
    split_ifs <;> simp
  rw [e]
  exact (insL (ρ := ρ)).hasFDerivAt.add_const _

theorem insL_single (l : Fin ρ) (x : ℂ) : insL (Pi.single l x) = Pi.single (shS l) x := by
  rw [insL_apply]
  funext j
  by_cases hj : j = shS l
  · subst hj
    simp [consC, shS]
  · rw [Pi.single_eq_of_ne hj]
    unfold consC
    split_ifs with h0
    · rfl
    · apply Pi.single_eq_of_ne
      intro e
      apply hj
      have := congrArg Fin.val e
      simp at this
      ext
      simp [shS]
      omega

theorem fderiv_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (t : ℂ) (f : (Fin (1 + ρ) → ℂ) → E)
    (c : Fin ρ → ℂ) (hf : DifferentiableAt ℝ f (consC t c)) (l : Fin ρ) (x : ℂ) :
    fderiv ℝ (fun c' => f (consC t c')) c (Pi.single l x) = fderiv ℝ f (consC t c) (Pi.single (shS l) x) := by
  have h := hf.hasFDerivAt.comp c (hasFDerivAt_consC t c)
  rw [show (fun c' => f (consC t c')) = f ∘ consC t from rfl, h.fderiv, ContinuousLinearMap.comp_apply, insL_single]

theorem opL_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℂ} (ht : t ≠ 0)
    (f : (Fin (1 + ρ) → ℂ) → E) (c : Fin ρ → ℂ) (hf : consC t c ∈ OmX (1 + ρ) → DifferentiableAt ℝ f (consC t c))
    (l : Fin ρ) (i : Fin 6) :
    opL l i (fun c' => f (consC t c')) c = opL (shS l) i f (consC t c) := by
  fin_cases i
  · show pOp l (fun c' => f (consC t c')) c = pOp (shS l) f (consC t c)
    unfold pOp
    by_cases hc : c ∈ OmX ρ
    · have hc' := (omX_consC ht c).2 hc
      rw [if_pos hc, if_pos hc', consC_sh]
      unfold wirt
      rw [fderiv_consC t f c (hf hc'), fderiv_consC t f c (hf hc')]
    · rw [if_neg hc, if_neg (fun h => hc ((omX_consC ht c).1 h))]
  · show cOp l (fun c' => f (consC t c')) c = cOp (shS l) f (consC t c)
    simp only [cOp, consC_sh]
  · show ciOp l (fun c' => f (consC t c')) c = ciOp (shS l) f (consC t c)
    simp only [ciOp, consC_sh]
  · show pbOp l (fun c' => f (consC t c')) c = pbOp (shS l) f (consC t c)
    unfold pbOp
    by_cases hc : c ∈ OmX ρ
    · have hc' := (omX_consC ht c).2 hc
      rw [if_pos hc, if_pos hc', consC_sh]
      unfold wirtBar
      rw [fderiv_consC t f c (hf hc'), fderiv_consC t f c (hf hc')]
    · rw [if_neg hc, if_neg (fun h => hc ((omX_consC ht c).1 h))]
  · show cbOp l (fun c' => f (consC t c')) c = cbOp (shS l) f (consC t c)
    simp only [cbOp, consC_sh]
  · show cbiOp l (fun c' => f (consC t c')) c = cbiOp (shS l) f (consC t c)
    simp only [cbiOp, consC_sh]

end Formalism.FourierDecayAlt.P.PBH
end
end

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

section rel

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def Rel (T : V →ₗ[ℂ] V') (A : Pr V) (A' : Pr V') : Prop :=
  A'.1 ∘ₗ T = T ∘ₗ A.1 ∧ A'.2.unop ∘ₗ T = T ∘ₗ A.2.unop

variable {T : V →ₗ[ℂ] V'}

private theorem rel_iff_forall_apply {A : Pr V} {A' : Pr V'} :
    Rel T A A' ↔ ∀ v, A'.1 (T v) = T (A.1 v) ∧ A'.2.unop (T v) = T (A.2.unop v) := by
  unfold Rel
  constructor
  · intro h v
    exact ⟨LinearMap.congr_fun h.1 v, LinearMap.congr_fun h.2 v⟩
  · intro h
    exact ⟨LinearMap.ext fun v => (h v).1, LinearMap.ext fun v => (h v).2⟩

theorem rel_mk {X : Module.End ℂ V} {Xs : Module.End ℂ V} {X' Xs' : Module.End ℂ V'}
    (h1 : ∀ v, X' (T v) = T (X v)) (h2 : ∀ v, Xs' (T v) = T (Xs v)) : Rel T (mkP X Xs) (mkP X' Xs') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨h1 v, h2 v⟩

theorem rel_add {A B : Pr V} {A' B' : Pr V'} (hA : Rel T A A') (hB : Rel T B B') : Rel T (A + B) (A' + B') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show A'.1 (T v) + B'.1 (T v) = T (A.1 v + B.1 v)
    rw [map_add (f := _), (hA v).1, (hB v).1]
  · show A'.2.unop (T v) + B'.2.unop (T v) = T (A.2.unop v + B.2.unop v)
    rw [map_add (f := _), (hA v).2, (hB v).2]

theorem rel_neg {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (-A) (-A') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show -A'.1 (T v) = T (-A.1 v)
    rw [map_neg, (hA v).1]
  · show -A'.2.unop (T v) = T (-A.2.unop v)
    rw [map_neg, (hA v).2]

theorem rel_zero : Rel T (0 : Pr V) (0 : Pr V') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨(map_zero T).symm, (map_zero T).symm⟩

theorem rel_mul {A B : Pr V} {A' B' : Pr V'} (hA : Rel T A A') (hB : Rel T B B') : Rel T (A * B) (A' * B') := by
  rw [rel_iff_forall_apply] at *
  intro v
  constructor
  · show A'.1 (B'.1 (T v)) = T (A.1 (B.1 v))
    rw [(hB v).1, (hA _).1]
  · show B'.2.unop (A'.2.unop (T v)) = T (B.2.unop (A.2.unop v))
    rw [(hA v).2, (hB _).2]

theorem rel_algebraMap (s : ℂ) : Rel T (algebraMap ℂ (Pr V) s) (algebraMap ℂ (Pr V') s) := by
  rw [rel_iff_forall_apply]
  intro v
  constructor
  · show (algebraMap ℂ (Module.End ℂ V') s) (T v) = T ((algebraMap ℂ (Module.End ℂ V) s) v)
    simp [Module.algebraMap_end_apply]
  · show (algebraMap ℂ (Module.End ℂ V') (conj s)) (T v) = T ((algebraMap ℂ (Module.End ℂ V) (conj s)) v)
    simp [Module.algebraMap_end_apply]

theorem rel_one : Rel T (1 : Pr V) (1 : Pr V') := by
  rw [rel_iff_forall_apply]
  intro v
  exact ⟨rfl, rfl⟩

theorem rel_smul (s : ℂ) {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (s • A) (s • A') := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact rel_mul (rel_algebraMap s) hA

theorem rel_star {A : Pr V} {A' : Pr V'} (hA : Rel T A A') : Rel T (star A) (star A') := by
  rw [rel_iff_forall_apply] at *
  intro v
  exact ⟨(hA v).2, (hA v).1⟩

theorem rel_sum {ι : Type*} (s : Finset ι) {A : ι → Pr V} {A' : ι → Pr V'} (h : ∀ i ∈ s, Rel T (A i) (A' i)) :
    Rel T (∑ i ∈ s, A i) (∑ i ∈ s, A' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rel_zero : Rel T (0 : Pr V) (0 : Pr V'))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact rel_add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

def MRel (T : V →ₗ[ℂ] V') (M : Matrix (Fin 2) (Fin 2) (Pr V)) (M' : Matrix (Fin 2) (Fin 2) (Pr V')) : Prop :=
  ∀ a b, Rel T (M a b) (M' a b)

theorem mrel_mul {M N : Matrix (Fin 2) (Fin 2) (Pr V)} {M' N' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') (hN : MRel T N N') : MRel T (M * N) (M' * N') := by
  intro a b
  simp only [Matrix.mul_apply]
  exact rel_sum _ (fun c _ => rel_mul (hM a c) (hN c b))

theorem mrel_conjTranspose {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') : MRel T Mᴴ M'ᴴ := by
  intro a b
  exact rel_star (hM b a)

theorem mrel_one : MRel T (1 : Matrix (Fin 2) (Fin 2) (Pr V)) 1 := by
  intro a b
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact rel_one
  · exact rel_zero

theorem mrel_smul (s : ℂ) {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    (hM : MRel T M M') : MRel T (s • M) (s • M') := by
  intro a b
  exact rel_smul s (hM a b)

theorem mrel_Tm (Y : ℂ) {p c ci : Pr V} {p' c' ci' : Pr V'} (hp : Rel T p p') (hc : Rel T c c') (hci : Rel T ci ci') :
    MRel T (Formalism.YangianSpanCharacter.T.Tm Y p c ci) (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact rel_add (rel_algebraMap Y) hp
  · exact rel_neg hc
  · exact hci
  · exact rel_zero

end rel

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem t_tr {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))) (Y : ℂ) (a b : Fin 2)
    (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    Xs.t Y a b (trL ht z z' π π' Φ) = trL ht z z' π π' (X.t Y a b Φ) := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ DomR k ρ z z'
  · have hx' := (domR_iota ht z z' c g).2 hx
    rw [Xs.t_apply Y a b _ (c, g) hx, trL_apply]
    show _ = (X.t Y a b Φ).1 (consC t c) (ιLev k 1 ρ g)
    rw [X.t_apply Y a b Φ _ hx']
    exact (tL_iota (E := Wq →L[ℂ] Wp) hz hz' Y a b ((Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) (consC t c)) hx.2.1).symm
  · rw [(Xs.t Y a b (trL ht z z' π π' Φ)).2.1 (c, g) hx, trL_apply]
    exact ((X.t Y a b Φ).2.1 _ (fun h => hx ((domR_iota ht z z' c g).1 h))).symm

theorem op_tr {t : ℂ} (ht : t ≠ 0)
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))) (l : Fin ρ) (i : Fin 6)
    (Φ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π') :
    Xs.op l i (trL ht z z' π π' Φ) = trL ht z z' π π' (X.op (shS l) i Φ) := by
  apply Subtype.ext
  rw [Xs.op_apply, trL_apply, trL_apply, X.op_apply]
  funext c g
  exact opL_consC ht (fun c' => (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) c' (ιLev k 1 ρ g)) c
    (fun h => diff_rad Φ.2 _ h) l i

end ops

section chain

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_rel {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (Wd.Ts (P5.site L (shS l)) Y) (Wd.Ts (P5.site Ls l) Y) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine mrel_Tm Y ?_ ?_ ?_
  · show Rel _ (L.p (shS l)) (Ls.p l)
    rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · show Rel _ (L.c (shS l)) (Ls.c l)
    rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · show Rel _ (L.ci (shS l)) (Ls.ci l)
    rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem tprod_rel {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (Y : ℂ) :
    ∀ m n : ℕ, ρ - n = m → MRel (trL ht z z' π π') (P5.tprod L Y (n + 1)) (P5.tprod Ls Y n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have e1 : P5.tprod L Y (n + 1) = 1 := by rw [P5.tprod, dite_eq_right (by omega)]
    have e2 : P5.tprod Ls Y n = 1 := by rw [P5.tprod, dite_eq_right (by omega)]
    rw [e1, e2]
    exact mrel_one
  | succ m ih =>
    intro n hn
    have e1 : P5.tprod L Y (n + 1) = P5.tprod L Y (n + 1 + 1) * Wd.Ts (P5.site L ⟨n + 1, by omega⟩) Y := by
      rw [P5.tprod, dite_eq_left (by omega)]
    have e2 : P5.tprod Ls Y n = P5.tprod Ls Y (n + 1) * Wd.Ts (P5.site Ls ⟨n, by omega⟩) Y := by
      rw [P5.tprod, dite_eq_left (by omega)]
    rw [e1, e2]
    refine mrel_mul (ih (n + 1) (by omega)) ?_
    have e : (⟨n + 1, by omega⟩ : Fin (1 + ρ)) = shS ⟨n, by omega⟩ := rfl
    rw [e]
    exact site_rel ht hL hLs _ Y

theorem qqi_rel {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st 1 Y) (P5.QQi Ls sts 0 Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    refine mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  have h1 : ((1 : Fin (1 + ρ + 1)) : ℕ) = 0 + 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have h0 : ((0 : Fin (ρ + 1)) : ℕ) = 0 := rfl
  rw [h1, h0]
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ 0 rfl)) hQ) (tprod_rel ht hL hLs _ _ 0 rfl)

end chain

end Formalism.FourierDecayAlt.P.PBH
end
end

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

theorem glev_last_eq (r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  simp only [Glev, B2.UWb, Fin.val_last]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => h2 a a.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a _ => h2 a⟩

theorem image_glev : ιLev k 1 ρ '' Glev k ρ (Fin.last ρ) = Glev k (1 + ρ) (Fin.last (1 + ρ)) := by
  rw [glev_last_eq, glev_last_eq, Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec k ρ]

theorem map_levM_smul {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs) :
    ∃ c : NNReal, μs.map (B2.levM k ρ) = c • μ := by
  rw [glev_last_eq] at hμs hμ
  have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k ρ
  obtain ⟨_, hν⟩ := Formalism.FourierDecayAlt.P.levi_haar_measure_exists k ρ _ μs hU hμs
  have e : ιLev k 1 ρ '' B2.UWb k ρ = B2.UWb k (1 + ρ) := by
    rw [← glev_last_eq, ← glev_last_eq, image_glev]
  rw [e] at hν
  exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (1 + ρ) _ μ _ (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k (1 + ρ)) hμ hν.conc
    hν.left hν.finite_compact

theorem zeta_levM (z z' : Fin (2 * ρ + k + 1) → ℂ) (x : Mt k ρ) :
    zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of (B2.levM k ρ x)) =
      zetaL k ρ z z' (Fin.last ρ) (Matrix.of x) := by
  have hf : ∀ (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ), fvec k r v (Fin.last r) = v := fun r v => by
    simp [fvec]
  change herm (Hpk k (1 + ρ)) (ιLev k 1 ρ (Matrix.of x) *ᵥ fvec k (1 + ρ) (liftVec k 1 ρ z') (Fin.last (1 + ρ)))
      (fvec k (1 + ρ) (liftVec k 1 ρ z) (Fin.last (1 + ρ))) =
    herm (Hpk k ρ) (Matrix.of x *ᵥ fvec k ρ z' (Fin.last ρ)) (fvec k ρ z (Fin.last ρ))
  rw [hf, hf, hf, hf, Formalism.FourierDecayAlt.P.B2x5.lev_lift, Formalism.FourierDecayAlt.P.B2x4.herm_lift]

theorem measurable_levM : Measurable (B2.levM k ρ) := by
  exact (Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ).measurable

theorem continuous_zetaL (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => zetaL k r z z' (Fin.last r) (Matrix.of x) := by
  exact (LinearMap.continuous_of_finiteDimensional (Formalism.FourierDecayAlt.P.Qx5.zetaLin k r z z' (Fin.last r))).comp continuous_id

theorem map_levM_eq {z z' : Fin (2 * ρ + k + 1) → ℂ} {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (wt : ℂ → ℝ≥0∞) (hfin : ∀ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ < (⊤ : ℝ≥0∞))
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, wt ζ * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ z z' (Fin.last ρ) (Matrix.of x)) ∂μs = ∫⁻ ζ, wt ζ * ψ ζ) :
    μs.map (B2.levM k ρ) = μ := by
  obtain ⟨c, hc⟩ := map_levM_smul hμ hμs
  have key : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → c • ∫⁻ ζ, wt ζ * ψ ζ = ∫⁻ ζ, wt ζ * ψ ζ := by
    intro ψ hψ
    have hm : Measurable fun y : Mt k (1 + ρ) =>
        ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of y)) :=
      hψ.comp (continuous_zetaL (1 + ρ) _ _).measurable
    rw [← hlaw ψ hψ, ← lintegral_smul_measure, ← hc, lintegral_map hm measurable_levM]
    simp_rw [zeta_levM]
    rw [hlaws ψ hψ, hlaw ψ hψ]
  by_cases hR : ∃ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ ≠ 0
  · obtain ⟨R, hR⟩ := hR
    have hψ : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞)) :=
      measurable_one.indicator Metric.isClosed_closedBall.measurableSet
    have h1 := key _ hψ
    have e : ∫⁻ ζ, wt ζ * (Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) ζ =
        ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
      congr 1
      funext ζ
      by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R <;> simp [hζ]
    rw [e, ENNReal.smul_def] at h1
    have h2 : (c : ℝ≥0∞) * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ = 1 * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [one_mul]
      exact h1
    have hc1 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hR (hfin R).ne).mp h2
    rw [hc, ENNReal.coe_eq_one.mp hc1, one_smul]
  · push_neg at hR
    have h0 : ∫⁻ ζ, wt ζ = 0 := by
      rw [← setLIntegral_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ)]
      refine le_antisymm ((lintegral_iUnion_le _ _).trans ?_) zero_le'
      simp [hR]
    have hμ0 : μ = 0 := by
      have h3 := hlaw (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    have hμs0 : μs = 0 := by
      have h3 := hlaws (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    rw [hμ0, hμs0, Measure.map_zero]

end Formalism.FourierDecayAlt.P.PBH
