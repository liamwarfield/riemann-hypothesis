module

public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Lemmata.GeneralBFactSecondTerForm.Imports

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AnisotropicColumnSums
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace AnisotropicColumnSums

theorem chat_gen (t n : ℕ) (h : t = n + 1) (A : Type) [Ring A] [Algebra ℂ A] (Eop : Fin t → Fin t → A)
    (P Q : Matrix (Fin t) (Fin t) ℂ) (la : Fin t) (hla : la.val = n) (ι : Fin n → Fin t)
    (hι : ∀ a, (ι a).val = a.val) (hE : GlRel Eop) (hQP : Q * P = 1) (hPQ : P * Q = 1) (u : ℂ) (β : Fin t → ℂ)
    (hβ : ∀ j, j ≠ la → (β ᵥ* P) j = 0) :
    chatA Eop u (fun p => P p la) β = (β ᵥ* P) la • qminor (Econj Eop P Q) ι ι u := by
  subst h
  have e1 : la = Fin.last n := Fin.ext hla
  subst e1
  have e2 : ι = skip1 (Fin.last n) := by
    funext a
    apply Fin.ext
    have := a.isLt
    simp [skip1, hι]
  rw [e2]
  exact first_contraction_adapted A n Eop P Q hE hQP hPQ u β hβ

variable {k r : ℕ}

theorem sum_last {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    ∑ d, herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) w * v (posL k r (Fin.last r) d) = herm (Hpk k r) v w := by
  have hinj : ∀ c c' : Fin (mdim k r (Fin.last r)), posL k r (Fin.last r) c = posL k r (Fin.last r) c' → c = c' := by
    intro c c' h
    ext
    simp only [posL, Fin.ext_iff] at h
    omega
  have hsurj : ∀ p, Qx2.inV k r (Fin.last r) p → ∃ c, posL k r (Fin.last r) c = p := by
    intro p hp
    simp only [Qx2.inV, Fin.val_last] at hp
    refine ⟨⟨p.val - r, ?_⟩, ?_⟩
    · simp only [mdim, Fin.val_last]
      omega
    · ext
      simp only [posL, Fin.val_last]
      omega
  have hv' : v = ∑ d, v (posL k r (Fin.last r) d) • bvec (posL k r (Fin.last r) d) := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hq : Qx2.inV k r (Fin.last r) q
    · obtain ⟨d0, rfl⟩ := hsurj q hq
      rw [Fintype.sum_eq_single d0]
      · simp
      · intro d hd
        have hne : posL k r (Fin.last r) d0 ≠ posL k r (Fin.last r) d := fun h => hd (hinj _ _ h).symm
        simp [hne]
    · rw [Finset.sum_eq_zero]
      · apply hv
        simp only [Qx2.inV, Fin.val_last] at hq
        omega
      · intro d _
        have hne : q ≠ posL k r (Fin.last r) d := by
          rintro rfl
          apply hq
          have hd := d.isLt
          simp only [Qx2.inV, posL, mdim, Fin.val_last] at hd ⊢
          omega
        simp [hne]
  conv_rhs => rw [hv']
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

def bcol (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ)
    (j : Fin (mdim k r (Fin.last r))) : Fin (2 * r + k + 1) → ℂ :=
  if h : j.val < k then Bs ⟨j.val, h⟩ else x

def nrm (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r (Fin.last r))) : ℂ :=
  if j.val < k then 1 else (herm (Hpk k r) x x)⁻¹

theorem mdim_last : mdim k r (Fin.last r) = k + 1 := by
  simp [mdim]

theorem bcol_inWb {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bcol k r x Bs j) := by
  unfold bcol
  split_ifs
  · exact hB.1 _
  · exact hx

theorem herm_bcol_eq_ite {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j) x = if j.val < k then 0 else herm (Hpk k r) x x := by
  unfold bcol
  by_cases h : j.val < k
  · rw [dite_eq_left h, if_pos h]
    exact hB.2.2 _ x (List.mem_singleton_self x)
  · rw [dite_eq_right h, if_neg h]

private theorem herm_eq_star_herm_swap (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, Qx2.hpk_h, ← Matrix.dotProduct_mulVec]

theorem gram {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hxx : herm (Hpk k r) x x ≠ 0) (hB : IsFrameOf k r [x] Bs) (j j' : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j') (bcol k r x Bs j) * nrm k r x j = if j = j' then 1 else 0 := by
  obtain ⟨hBw, hBo, hBx⟩ := hB
  have hx0 : ∀ a, herm (Hpk k r) (Bs a) x = 0 := fun a => hBx a x (List.mem_singleton_self x)
  have hx0' : ∀ a, herm (Hpk k r) x (Bs a) = 0 := fun a => by rw [herm_eq_star_herm_swap, hx0, star_zero]
  have hj : j.val < k + 1 := by
    have := j.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  have hj' : j'.val < k + 1 := by
    have := j'.isLt
    simp only [mdim, Fin.val_last] at this
    omega
  unfold bcol nrm
  by_cases h1 : j.val < k <;> by_cases h2 : j'.val < k
  · rw [dite_eq_left h2, dite_eq_left h1, if_pos h1, mul_one, hBo]
    by_cases hjj : j = j'
    · subst hjj
      simp
    · have hne : ¬ j'.val = j.val := fun h => hjj (Fin.ext h.symm)
      simp [hjj, hne]
  · rw [dite_eq_right h2, dite_eq_left h1, if_pos h1, mul_one, hx0', if_neg]
    rintro rfl
    exact h2 h1
  · rw [dite_eq_left h2, dite_eq_right h1, if_neg h1, hx0, zero_mul, if_neg]
    rintro rfl
    exact h1 h2
  · have hjj : j = j' := by
      ext
      omega
    rw [dite_eq_right h2, dite_eq_right h1, if_neg h1, if_pos hjj, mul_inv_cancel₀ hxx]

end AnisotropicColumnSums

open AnisotropicColumnSums in
theorem qr_chatFrame_of : Formalism.FourierDecayAlt.Qr.FrameMinor → Formalism.FourierDecayAlt.Qr.ChatFrame := by
  intro hFM E _ _ k r D hD x Bs hx hxx hB u φ g hg
  set P : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun c j => bcol k r x Bs j (posL k r (Fin.last r) c) with hP
  set Q : Matrix (Fin (mdim k r (Fin.last r))) (Fin (mdim k r (Fin.last r))) ℂ :=
    Matrix.of fun j d => herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) (bcol k r x Bs j) * nrm k r x j with hQ
  have hQP : Q * P = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply, ← gram hxx hB j j', ← sum_last (bcol_inWb hx hB j'), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hP, hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let la : Fin (mdim k r (Fin.last r)) := ⟨k, by rw [mdim_last]; omega⟩
  let ι : Fin k → Fin (mdim k r (Fin.last r)) := fun a => ⟨a.val, by rw [mdim_last]; omega⟩
  have hβP : ∀ j, ((fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) ᵥ* P) j =
      if j.val < k then 0 else herm (Hpk k r) x x := by
    intro j
    rw [← herm_bcol_eq_ite hB j, ← sum_last (bcol_inWb hx hB j)]
    rfl
  have hcol : (fun j => x (posL k r (Fin.last r) j)) = fun p => P p la := by
    funext p
    simp [hP, bcol, la]
  have key := chat_gen (mdim k r (Fin.last r)) k mdim_last (Module.End ℂ (SV k r (Fin.last r) D E))
    (EV k r (Fin.last r) D E) P Q la rfl ι (fun _ => rfl) (relation_representation E k r 0 (Fin.last r) D hD).1 hQP hPQ u
    (fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) (by
      intro j hj
      rw [hβP, if_pos]
      have h1 : j.val < k + 1 := lt_of_lt_of_eq j.isLt mdim_last
      have : j.val ≠ k := fun e => hj (Fin.ext e)
      omega)
  rw [hcol, key, hβP, if_neg (by simp [la])]
  have hm := hFM E k r k D hD Bs hB.1 P Q ι (fun a b e => Fin.ext (by have e' := congrArg Fin.val e; exact e'))
    (by
      intro a c
      simp [hP, bcol, ι])
    (by
      intro b d
      simp [hQ, bcol, nrm, ι])
    u φ g hg
  rw [← hm]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CommonEigenvectors

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem eig_in [FiniteDimensional ℂ V] (T : Module.End ℂ V) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hT : ∀ x ∈ G, T x ∈ G) : ∃ (μ : ℂ) (x : V), x ∈ G ∧ x ≠ 0 ∧ T x = μ • x := by
  haveI : Nontrivial G := Submodule.nontrivial_iff_ne_bot.2 hG
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T.restrict hT)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, x, x.2, fun h => hx.2 (Subtype.ext h), ?_⟩
  have h1 := Module.End.mem_eigenspace_iff.1 hx.1
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem common [FiniteDimensional ℂ V] {ι : Type} [DecidableEq ι] (D : ι → Module.End ℂ V)
    (hc : ∀ a b, D a * D b = D b * D a) (s : Finset ι) (G : Submodule ℂ V) (hG : G ≠ ⊥)
    (hst : ∀ a, ∀ x ∈ G, D a x ∈ G) :
    ∃ (G' : Submodule ℂ V) (ν : ι → ℂ), G' ≤ G ∧ G' ≠ ⊥ ∧ (∀ a, ∀ x ∈ G', D a x ∈ G') ∧
      ∀ a ∈ s, ∀ x ∈ G', D a x = ν a • x := by
  induction s using Finset.induction_on with
  | empty => exact ⟨G, 0, le_rfl, hG, hst, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨G₁, ν, h1, h2, h3, h4⟩ := ih
    obtain ⟨μ, x, hx1, hx2, hx3⟩ := eig_in (D a) G₁ h2 (h3 a)
    refine ⟨G₁ ⊓ LinearMap.ker (D a - μ • 1), Function.update ν a μ, le_trans inf_le_left h1, ?_, ?_, ?_⟩
    · intro hbot
      apply hx2
      have hm : x ∈ G₁ ⊓ LinearMap.ker (D a - μ • 1) :=
        Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (by simp [hx3])⟩
      rw [hbot] at hm
      simpa using hm
    · intro c y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      have hcomm : D a (D c y) = D c (D a y) := by
        have := congrArg (fun T => T y) (hc a c)
        simpa using this
      exact Submodule.mem_inf.2 ⟨h3 c y hy1, LinearMap.mem_ker.2 (by simp [hcomm, hy2'])⟩
    · intro b hb y hy
      obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.1 hy
      have hy2' : D a y = μ • y := by simpa [sub_eq_zero] using LinearMap.mem_ker.1 hy2
      rcases Finset.mem_insert.1 hb with rfl | hb
      · simp [hy2']
      · have hba : b ≠ a := fun h => ha (h ▸ hb)
        simp [Function.update_apply, hba, h4 b hb y hy1]

def hop {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ V :=
  ∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) • E c c

theorem diag_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c a b : Fin n) (x : V) :
    E c c (E a b x) = E a b (E c c x) + ((if c = a then E a b x else 0) - (if b = c then E a b x else 0)) := by
  have h : E c c (E a b x) - E a b (E c c x) = ((if c = a then E c b else 0) - (if b = c then E a c else 0)) x :=
    congrArg (fun T => T x) (hE c c a b)
  rw [sub_eq_iff_eq_add'] at h
  rw [h, LinearMap.sub_apply]
  congr 1
  split_ifs <;> subst_vars <;> simp

theorem hop_move {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (a b : Fin n) (x : V) :
    hop E (E a b x) = E a b (hop E x) + (((b : ℕ) : ℂ) - ((a : ℕ) : ℂ)) • E a b x := by
  unfold hop
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, diag_move hE, smul_add, smul_sub,
    smul_ite, smul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← sub_smul]
  congr 2
  ring

theorem hop_weight {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {θ : Fin n → ℂ} {x : V}
    (hx : ∀ a, E a a x = θ a • x) :
    hop E x = (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c) • x := by
  unfold hop
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.smul_apply, hx, smul_smul]

theorem hval_re {n : ℕ} (θ : Fin n → ℂ) :
    (∑ c : Fin n, ((n : ℂ) - ((c : ℕ) : ℂ)) * θ c).re = hval θ := by
  unfold hval
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [Complex.mul_re]

end Formalism.FourierDecayAlt.P.CommonEigenvectors

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr CommonEigenvectors

theorem exists_singular_maximal_vector : Qr.ExistsSingMax := by
  intro V _ _ _ n E hE S hS hS0
  have hcomm : ∀ a b : Fin n, E a a * E b b = E b b * E a a := by
    intro a b
    have h := hE a a b b
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := by
    intro a b x hx
    exact hS a b x hx
  obtain ⟨G', ν0, hG'S, hG'0, -, hG'ν⟩ :=
    common (fun a => E a a) hcomm Finset.univ S hS0 (fun a => hstab a a)
  obtain ⟨x0, hx0G, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hG'0
  let W : Set (Fin n → ℂ) := {θ | ∃ x ∈ S, x ≠ 0 ∧ ∀ a, E a a x = θ a • x}
  have hWne : W.Nonempty := ⟨ν0, x0, hG'S hx0G, hx00, fun a => hG'ν a (Finset.mem_univ a) x0 hx0G⟩
  have hWfin : W.Finite := by
    refine (Set.Finite.pi (t := fun a => {μ | (E a a).HasEigenvalue μ})
      fun a => Module.End.finite_hasEigenvalue (E a a)).subset ?_
    rintro θ ⟨x, -, hx0, hx⟩
    exact Set.mem_univ_pi.2 fun a =>
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hx a), hx0⟩
  obtain ⟨ν, ⟨v, hvS, hv0, hv⟩, hmax⟩ := Set.exists_max_image W hval hWfin hWne
  refine ⟨ν, v, hvS, hv0, ⟨hv, fun a b hab => ?_⟩, fun θ x hxS hx0 hx => hmax θ ⟨x, hxS, hx0, hx⟩⟩
  by_contra hy
  set y := E a b v with hydef
  have hyS : y ∈ S := hstab a b v hvS
  let θ' : Fin n → ℂ := fun c => ν c + ((if c = a then 1 else 0) - (if b = c then 1 else 0))
  have hy' : ∀ c, E c c y = θ' c • y := by
    intro c
    rw [hydef, diag_move hE, hv c, map_smul]
    simp only [θ', add_smul, sub_smul, ite_smul, one_smul, zero_smul]
  have hle := hmax θ' ⟨y, hyS, hy, hy'⟩
  have k1 := hop_weight hy'
  have k2 := hop_move hE a b v
  rw [hop_weight hv, map_smul, ← hydef, ← add_smul, k1] at k2
  have k3 := smul_left_injective ℂ hy k2
  have hv' : hval θ' = hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    rw [← hval_re, ← hval_re, k3]
    simp
  have hba : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by
    have := Fin.lt_iff_val_lt_val.1 hab
    exact_mod_cast this
  linarith

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem singular_dominant : Qr.SingDom := by
  intro V _ _ _ n E ν v hE hv hv0 a b hab
  obtain ⟨hd, hr⟩ := hv
  have hab' : a ≠ b := ne_of_lt hab
  by_cases h0 : E a a - E b b = 0
  · refine ⟨0, ?_⟩
    have h1 : (E a a - E b b) v = 0 := by rw [h0]; rfl
    rw [LinearMap.sub_apply, hd, hd, ← sub_smul] at h1
    simpa [hv0] using h1
  · have e0 := hE a b b a
    have e1 := hE a a a b
    have e2 := hE b b a b
    have e3 := hE a a b a
    have e4 := hE b b b a
    simp [hab', hab'.symm] at e0 e1 e2 e3 e4
    have t : IsSl2Triple (E a a - E b b) (E a b) (E b a) :=
      { h_ne_zero := h0
        lie_e_f := by rw [Ring.lie_def, e0]
        lie_h_e_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E a b - E a b * (E a a - E b b)
              = (E a a * E a b - E a b * E a a) - (E b b * E a b - E a b * E b b) := by noncomm_ring
            _ = 2 • E a b := by rw [e1, e2]; abel
        lie_h_f_nsmul := by
          rw [Ring.lie_def]
          calc (E a a - E b b) * E b a - E b a * (E a a - E b b)
              = (E a a * E b a - E b a * E a a) - (E b b * E b a - E b a * E b b) := by noncomm_ring
            _ = -(2 • E b a) := by rw [e3, e4]; abel }
    have pv : t.HasPrimitiveVectorWith v (ν a - ν b) :=
      { ne_zero := hv0
        lie_h := by
          show (E a a - E b b) v = (ν a - ν b) • v
          rw [LinearMap.sub_apply, hd, hd, sub_smul]
        lie_e := by
          show E a b v = 0
          exact hr a b hab }
    exact pv.exists_nat

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem map_eq_of_cpol {n : ℕ} (m m' : Fin n → ℂ) (h : ∀ w, cpol m w = cpol m' w) :
    Multiset.map m univ.val = Multiset.map m' univ.val := by
  have key : ∀ (f : Fin n → ℂ) (w : ℂ), cpol f w = Polynomial.eval w
      ((Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - f j) univ.val)).prod) := by
    intro f w
    rw [Multiset.map_map, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp [cpol, Finset.prod, Function.comp_def]
  have hp : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m j) univ.val)).prod =
      (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m' j) univ.val)).prod :=
    Polynomial.funext (fun w => by rw [← key, ← key, h])
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  have h2 := congrArg (Multiset.map (fun z : ℂ => -z)) hr
  simpa [Multiset.map_map, Function.comp_def] using h2

theorem sdec_re {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : StrictAnti fun a => (m a).re := by
  intro a b hab
  obtain ⟨N, hN⟩ := hm a b hab
  have h := congrArg Complex.re hN
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  show (m b).re < (m a).re
  linarith

theorem sdec_inj {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : Function.Injective m := by
  intro a b hab
  exact (sdec_re hm).injective (congrArg Complex.re hab)

theorem sdec_shift {n : ℕ} {ν : Fin n → ℂ} (h : ∀ a b : Fin n, a < b → ∃ N : ℕ, ν a - ν b = (N : ℂ)) :
    SDec fun k => ν k - ((k : ℕ) : ℂ) := by
  intro a b hab
  obtain ⟨N, hN⟩ := h a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.1 hab)
  refine ⟨N + d, ?_⟩
  have h1 : ν a = ν b + N := by rw [← hN]; ring
  show ν a - ((a : ℕ) : ℂ) - (ν b - ((b : ℕ) : ℂ)) = _
  rw [hd, h1]
  push_cast
  ring

theorem sdec_shf {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (hM : StrictAnti M) : SDec (shf β M) := by
  intro a b hab
  have h := hM hab
  refine ⟨(M a - M b - 1).toNat, ?_⟩
  have h1 : (((M a - M b - 1).toNat : ℤ) : ℂ) = ((M a - M b - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at h1
  rw [h1]
  simp only [shf]
  push_cast
  ring

theorem hval_shift {n : ℕ} (ν : Fin n → ℂ) (a b : Fin n) :
    hval (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  unfold hval
  have h : ∀ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) *
      (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ).re =
      ((n : ℝ) - ((c : ℕ) : ℝ)) * (ν c).re + (if c = a then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) -
        (if c = b then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) := by
    intro c
    split_ifs <;> simp <;> ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

section mod

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem indep_char {ι : Type*} (C : ℂ → Module.End ℂ V) (χ : ι → ℂ → ℂ) (hχ : Function.Injective χ)
    (p : ι → Submodule ℂ V) (hp : ∀ i v, v ∈ p i ↔ ∀ w, C w v = χ i w • v) : iSupIndep p := by
  first | exact Bl.general_b_fact_second_ter_form.goal1 .. | (apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption)

theorem hw_cpol {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m ν : Fin n → ℂ} {v : V} (hE : GlRel E)
    (hv : v ∈ CapSp E m) (hv0 : v ≠ 0) (hw : IsHW E ν v) (w : ℂ) :
    cpol m w = cpol (fun k => ν k - ((k : ℕ) : ℂ)) w := by
  have h1 := quantumDetHighestWeight_holds V n E ν v hE hw w
  rw [mem_CapSp.1 hv w] at h1
  have h2 := smul_left_injective ℂ hv0 h1
  rw [h2]
  unfold cpol
  refine Finset.prod_congr rfl fun k _ => ?_
  ring

end mod

end Formalism.FourierDecayAlt.P.HighestWeightPolynomials

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials

theorem separating_polynomials : Qr.SepPoly := by
  intro n m m' h hm'
  have hmap := map_eq_of_cpol m m' h
  have hnd : (Multiset.map m univ.val).Nodup := by
    rw [hmap]
    exact Multiset.Nodup.map (sdec_inj hm') univ.nodup
  refine ⟨fun a b hab => Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab, ?_⟩
  intro hm
  have hmem : ∀ a, ∃ b, m' b = m a := by
    intro a
    have h1 : m a ∈ Multiset.map m univ.val := Multiset.mem_map_of_mem m (Finset.mem_univ a)
    rw [hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hmem' : ∀ a, ∃ b, m b = m' a := by
    intro a
    have h1 : m' a ∈ Multiset.map m' univ.val := Multiset.mem_map_of_mem m' (Finset.mem_univ a)
    rw [← hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hr : (fun a => (m a).re) = fun a => (m' a).re := by
    rw [← StrictAnti.range_inj (sdec_re hm) (sdec_re hm')]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem a
      exact ⟨b, by simp only [hb]⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem' a
      exact ⟨b, by simp only [hb]⟩
  funext a
  obtain ⟨b, hb⟩ := hmem a
  have h1 : (m' b).re = (m' a).re := by rw [hb]; exact congrFun hr a
  rw [← hb, (sdec_re hm').injective h1]

theorem capelli_stabilizer : Qr.CapStab := by
  intro V _ _ n E m hE
  refine ⟨fun a b v hv => ?_, fun X hX v hv => ?_⟩
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds (Module.End ℂ V) n E hE w a b
    have h2 := LinearMap.congr_fun h v
    simp only [Module.End.mul_apply] at h2
    rw [h2, hv w, map_smul]
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h : Commute X (qdet E w) := QuantumMinorCommutation.commute_qminor E id id w X (fun s s' => hX _ _)
    have h2 := LinearMap.congr_fun h.eq v
    simp only [Module.End.mul_apply] at h2
    rw [← h2, hv w, map_smul]

theorem qr_capSing_of (hD : Qr.SingDom) (hX : Qr.ExistsSingMax) : Qr.CapSing := by
  intro V _ _ _ n E m hE hne
  obtain ⟨ν, v, hv, hv0, hw, _⟩ := hX V n E hE (CapSp E m) (capelli_stabilizer V n E m hE).1 hne
  refine ⟨(separating_polynomials n m _ (hw_cpol hE hv hv0 hw) (sdec_shift (hD V n E ν v hE hw hv0))).1, ?_⟩
  intro hm ν' v' hv' hv0' hw' j
  have h := (separating_polynomials n m _ (hw_cpol hE hv' hv0' hw') (sdec_shift (hD V n E ν' v' hE hw' hv0'))).2 hm
  have h2 : m j = ν' j - ((j : ℕ) : ℂ) := congrFun h j
  rw [h2]
  ring

theorem qr_topWeightSing_of (hX : Qr.ExistsSingMax) (hS : Qr.CapSing) : Qr.TopWeightSing := by
  intro V _ _ _ n E m hE hm x hx hw
  refine ⟨hw, fun a b hab => ?_⟩
  by_contra hne
  have hstab := (capelli_stabilizer V n E m hE).1
  have hx' : E a b x ∈ CapSp E m := hstab a b x hx
  have hbot : CapSp E m ≠ ⊥ := fun h => hne (by rw [h] at hx'; exact (Submodule.mem_bot ℂ).1 hx')
  obtain ⟨ν, v, hv, hv0, hhw, hmax⟩ := hX V n E hE (CapSp E m) hstab hbot
  have hν := (hS V n E m hE hbot).2 hm ν v hv hv0 hhw
  have hwt : ∀ c, E c c (E a b x) = (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) • E a b x := by
    intro c
    have h := LinearMap.congr_fun (hE c c a b) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [hw c, map_smul, sub_eq_iff_eq_add] at h
    rw [h, hν c]
    by_cases h1 : c = a
    · subst h1
      have h2 : ¬ (b = c) := fun h => (ne_of_gt hab) h
      have h3 : ¬ (c = b) := fun h => h2 h.symm
      simp only [if_true, if_neg h2, if_neg h3, LinearMap.zero_apply]
      module
    · by_cases h2 : b = c
      · subst h2
        simp only [if_true, if_neg h1, LinearMap.zero_apply]
        module
      · have h3 : ¬ (c = b) := fun h => h2 h.symm
        simp only [if_neg h1, if_neg h2, if_neg h3, LinearMap.zero_apply]
        module
  have h := hmax _ (E a b x) hx' hne hwt
  rw [hval_shift] at h
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.2 (Fin.lt_def.1 hab)
  linarith

theorem capelli_independence : Qr.CapIndep := by
  intro V _ _ n E β
  refine indep_char (qdet E) (fun M : {M : Fin n → ℤ // StrictAnti M} => cpol (shf β M.1)) ?_ _
    (fun M v => mem_CapSp)
  intro M M' h
  have h1 := (separating_polynomials n (shf β M.1) (shf β M'.1) (fun w => congrFun h w) (sdec_shf β M'.2)).2
    (sdec_shf β M.2)
  apply Subtype.ext
  funext j
  have h2 := congrFun h1 j
  simp only [shf, add_right_inj] at h2
  exact_mod_cast h2

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

lemma flagSpan_vanish (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : v ∈ C2.flagSpan k r z a) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    have hbr : b.val < r := by have := a.isLt; rw [Fin.lt_def] at hb; omega
    simp only [fvec, dif_pos hbr, bvec, Pi.single_apply, eI]
    rw [if_neg]
    intro e; rw [Fin.lt_def] at hb; have := congrArg Fin.val e; simp at this; omega
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma mulVec_bvec (M : B.Mat k r) (x : Fin (2 * r + k + 1)) : M *ᵥ bvec x = fun i => M i x := by
  funext i; simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def wpart (s : B.Mat k r) : B.Mat k r := fun i j =>
  if r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k then s i j else if i = j then 1 else 0

lemma zero_block (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0)
    (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    ∀ n : ℕ, ∀ a : Fin r, a.val = n → s (esI k r a) j = 0 := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha
    have e := congrFun (congrFun hU (eI k r a)) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at e
    simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
    have hH : Hpk k r (eI k r a) j = 0 := by
      rw [GBasic.Hpk_eq, if_neg]
      intro h'; have := congrArg Fin.val h'
      rw [GBasic.sig_lo _ _ _ (by simp [eI])] at this; simp [eI] at this; omega
    rw [hH, Finset.sum_eq_single (eI k r a)] at e
    · rw [hcol a _ (by simp [eI]), if_pos rfl, star_one, one_mul] at e
      have hsig : GBasic.sig k r (eI k r a) = esI k r a := by
        apply Fin.ext; rw [GBasic.sig_lo _ _ _ (by simp [eI])]; simp [eI, esI]
      have hsg : GBasic.sgn k r (eI k r a) = 1 := by
        unfold GBasic.sgn; rw [if_neg]; simp [eI]; omega
      rw [hsig, hsg, one_mul] at e
      exact e
    · intro p _ hp
      by_cases hpa : a.val ≤ p.val
      · rw [hcol a p hpa, if_neg hp, star_zero, zero_mul]
      · push_neg at hpa
        have hpr : p.val < r := by omega
        have hsig : GBasic.sig k r p = esI k r ⟨p.val, hpr⟩ := by
          apply Fin.ext; rw [GBasic.sig_lo _ _ _ hpr]; simp [esI]
        rw [hsig, ih p.val (by omega) ⟨p.val, hpr⟩ rfl, mul_zero, mul_zero]
    · simp

end FlagSpanVanishing

namespace FlagSpanVanishing

open C2x5 C2x7

variable {k r : ℕ}

lemma sig_notW (x : Fin (2 * r + k + 1)) (hx : ¬ (r ≤ x.val ∧ x.val ≤ r + k)) :
    ¬ (r ≤ (GBasic.sig k r x).val ∧ (GBasic.sig k r x).val ≤ r + k) := by
  have := GBasic.sig_val k r x
  have hx' := x.isLt
  split_ifs at this <;> omega

lemma sig_fixes_middle_block (x : Fin (2 * r + k + 1)) (hx : r ≤ x.val ∧ x.val ≤ r + k) : GBasic.sig k r x = x :=
  GBasic.sig_mid k r x hx.1 hx.2

lemma wpart_uh (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0) :
    wpart s ∈ UH (Hpk k r) := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  show (wpart s)ᴴ * Hpk k r * wpart s = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have e := congrFun (congrFun hU i) j
      rw [Matrix.mul_assoc, Matrix.mul_apply] at e
      simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_fixes_middle_block p hp]
        simp only [wpart, if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hi.1 hi.2))),
          if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hj.1 hj.2)))]
      · have h1 : wpart s p i = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hp ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [e] at hp; exact hp hi
        rw [h1, star_zero, zero_mul]
        by_cases hpr : p.val < r
        · have : r + k < (GBasic.sig k r p).val := by rw [GBasic.sig_lo _ _ _ hpr]; omega
          rw [hA _ j this hj.1 hj.2, mul_zero, mul_zero]
        · have : r + k < p.val := by omega
          rw [hA p i this hi.1 hi.2, star_zero, zero_mul]
    · rw [Finset.sum_eq_single (GBasic.sig k r j)]
      · have h1 : wpart s (GBasic.sig k r j) i = 0 := by
          simp only [wpart]
          rw [if_neg (fun h => sig_notW j hj ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [← e] at hi; exact sig_notW j hj hi
        rw [h1, star_zero, zero_mul, GBasic.Hpk_eq, if_neg]
        intro e; rw [sig_fixes_middle_block i hi] at e; rw [e] at hj; exact hj hi
      · intro p _ hp
        have : wpart s (GBasic.sig k r p) j = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hj ⟨h.2.2.1, h.2.2.2⟩), if_neg]
          intro e; apply hp; rw [← e, GBasic.sig_sig]
        rw [this, mul_zero, mul_zero]
      · simp
  · rw [Finset.sum_eq_single i]
    · have h1 : wpart s i i = 1 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.1, h.2.1⟩)]; simp
      have h2 : wpart s (GBasic.sig k r i) j = if GBasic.sig k r i = j then 1 else 0 := by
        simp only [wpart]; rw [if_neg (fun h => sig_notW i hi ⟨h.1, h.2.1⟩)]
      rw [h1, star_one, one_mul, h2, GBasic.Hpk_eq]
      by_cases e : GBasic.sig k r i = j
      · rw [if_pos e, if_pos e.symm, mul_one]
      · rw [if_neg e, if_neg (fun h => e h.symm), mul_zero]
    · intro p _ hp
      have : wpart s p i = 0 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.2.2.1, h.2.2.2⟩), if_neg hp]
      rw [this, star_zero, zero_mul]
    · simp

end FlagSpanVanishing

open C2x5 C2x7 FlagSpanVanishing

theorem standard_flag_property : C2.SFlag := by
  intro k r z hz
  ext s
  constructor
  · rintro ⟨hs, hfl⟩
    have hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
        s i (eI k r a) = if i = eI k r a then 1 else 0 := by
      intro a i hi
      have h := flagSpan_vanish z (Fin.castSucc a) _ (hfl (Fin.castSucc a)) i (by simpa using hi)
      have hf : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by rw [fvec, dif_pos (by simp)]; rfl
      rw [hf, mulVec_bvec, Pi.sub_apply, sub_eq_zero] at h
      rw [h]; simp [bvec, Pi.single_apply]
    have hzc : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (s *ᵥ z) i = z i := by
      intro i hi
      have h := flagSpan_vanish z (Fin.last r) _ (hfl (Fin.last r)) i (by simpa using hi)
      have hf : fvec k r z (Fin.last r) = z := by rw [fvec, dite_eq_right (by simp)]
      rw [hf, Pi.sub_apply, sub_eq_zero] at h; exact h
    have hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0 := by
      intro p j hp hj1 hj2
      have hpa : 2 * r + k - p.val < r := by omega
      have e : esI k r ⟨2 * r + k - p.val, hpa⟩ = p := Fin.ext (by simp [esI]; omega)
      rw [← e]; exact zero_block s hs hcol j hj1 hj2 _ _ rfl
    have hhU := wpart_uh s hs hA
    set h := wpart s with hh
    have hhW : h ∈ UWset k r z := by
      refine ⟨hhU, fun a => ⟨?_, ?_⟩, ?_⟩
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.1; simp only [eI] at this; omega)]
      · rw [mulVec_bvec]; funext i
        simp only [hh, wpart, bvec, Pi.single_apply]
        rw [if_neg (by intro h'; have := h'.2.2.2; simp only [esI] at this; omega)]
      · funext i
        by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
        · rw [← hzc i hi.1]
          simp only [Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
          · simp only [hh, wpart, if_pos (And.intro hi.1 (And.intro hi.2 hj))]
          · have hzj : z j = 0 := hz.1 j (by omega)
            rw [hzj, mul_zero, mul_zero]
        · simp only [Matrix.mulVec, dotProduct]
          rw [Finset.sum_eq_single i]
          · simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩)]; simp
          · intro j _ hj
            simp only [hh, wpart]; rw [if_neg (fun h' => hi ⟨h'.1, h'.2.1⟩), if_neg (Ne.symm hj), zero_mul]
          · simp
    have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hhU
    have hblk := WeylGroupFacts.uw_block (WeylGroupFacts.uw_inv hhW)
    refine ⟨h, hhW, h⁻¹ * s, ?_, ?_⟩
    · rw [WeylGroupFacts.nset_iff]
      refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hhU) hs, fun i j hj hij => ?_⟩
      rw [Matrix.mul_apply]
      by_cases hjr : j.val < r
      · have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
        have hterm : ∀ p, h⁻¹ i p * s p j = (if i = p then 1 else 0) * s p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr)]
          · have := hcol ⟨j.val, hjr⟩ p (by simp; omega)
            rw [e, if_neg (fun e' => hpr (by rw [e']; exact hjr))] at this
            rw [this, mul_zero, mul_zero]
        simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        have := hcol ⟨j.val, hjr⟩ i (by simp; omega)
        rw [e] at this; exact this
      · have hir : r ≤ i.val := by omega
        have hterm : ∀ p, h⁻¹ i p * s p j = h⁻¹ i p * h p j := by
          intro p
          by_cases hpr : p.val < r
          · rw [hblk.1 i p (Or.inl hpr), if_neg (fun e' => by rw [e'] at hir; omega), zero_mul, zero_mul]
          · by_cases hpk : p.val ≤ r + k
            · simp only [hh, wpart]
              rw [if_pos ⟨by omega, hpk, by omega, hj⟩]
            · rw [hA p j (by omega) (by omega) hj]
              simp only [hh, wpart]
              rw [if_neg (fun h' => hpk h'.2.1), if_neg (fun e' => by rw [e'] at hpk; exact hpk hj)]
        simp only [hterm]
        rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hhu, Matrix.one_apply]
    · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  · intro hs
    refine ⟨Sset_UH hs, fun a => ?_⟩
    obtain ⟨U, hU1, hU2, hsF⟩ := S_F hz.1 hs
    rw [colEq hsF a]
    have hfa : fvec k r z a = ∑ c, (if c = a then (1 : ℂ) else 0) • fvec k r z c := by
      simp [ite_smul]
    rw [hfa, ← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro c _
    rw [← sub_smul]
    by_cases hca : c < a
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hca⟩, rfl⟩)
    · have : U c a - (if c = a then 1 else 0) = 0 := by
        rcases eq_or_lt_of_le (not_lt.mp hca) with e | e
        · rw [← e, hU2, if_pos rfl, sub_self]
        · rw [hU1 c a e, if_neg (ne_of_gt e), sub_self]
      rw [this, zero_smul]; exact Submodule.zero_mem _

end Formalism.FourierDecayAlt.P
end
