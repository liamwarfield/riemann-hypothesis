module

public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstExpansionIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolynomialBound

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOfAlg
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

section Int

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem ofFn_prod_int {t : ℕ} (F : Fin t → Module.End ℂ V) (F' : Fin t → Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (h : ∀ k x, f (F k x) = F' k (f x)) (x : V) : f ((List.ofFn F).prod x) = (List.ofFn F').prod (f x) := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      h, ih (fun k => F k.succ) (fun k => F' k.succ) (fun k y => h k.succ y)]

theorem tm_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (a b : Fin n) (x : V) :
    f (Tm E u a b x) = Tm E' u a b (f x) := by
  unfold Tm
  split_ifs <;> simp [Module.algebraMap_end_apply, hf]

theorem qminor_int {n t : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (a b : Fin t → Fin n) (u : ℂ) (x : V) :
    f (qminor E a b u x) = qminor E' a b u (f x) := by
  unfold qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul,
    ofFn_prod_int _ _ f (fun k y => tm_int f hf _ _ _ y)]

theorem qdet_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) :
    f (qdet E u x) = qdet E' u (f x) :=
  qminor_int f hf id id u x

end Int

section Restr

variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def resE (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) : Fin n → Fin n → Module.End ℂ S :=
  fun a b => (E a b).restrict (hS a b)

theorem resE_apply (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) (a b : Fin n) (x : S) :
    ((resE E S hS a b x : S) : V) = E a b x := rfl

theorem glRel_resE {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (S : Submodule ℂ V) (hS : Stab E S) :
    GlRel (resE E S hS) := by
  intro a b c d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := LinearMap.congr_fun (hE a b c d) (x : V)
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp only [hbc, hda, if_true, if_false, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.zero_apply,
      Submodule.coe_sub, Submodule.coe_zero, sub_zero, zero_sub, resE_apply] at h ⊢ <;> exact h

theorem irr_resE {E : Fin n → Fin n → Module.End ℂ V} (S : Submodule ℂ V) (hS : Stab E S) (hne : S ≠ ⊥)
    (hirr : ∀ S' : Submodule ℂ V, S' ≤ S → Stab E S' → S' = ⊥ ∨ S' = S) : Irr (resE E S hS) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun T hT => ?_⟩
  have hinj := Submodule.map_injective_of_injective S.injective_subtype
  have hst : Stab E (T.map S.subtype) := by
    intro a b v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨resE E S hS a b x, hT a b x hx, rfl⟩
  rcases hirr (T.map S.subtype) (Submodule.map_subtype_le S T) hst with h | h
  · left
    exact hinj (h.trans (Submodule.map_bot _).symm)
  · right
    exact hinj (h.trans (Submodule.map_subtype_top S).symm)

theorem cap_resE {E : Fin n → Fin n → Module.End ℂ V} (m : Fin n → ℂ) (hS : Stab E (CapSp E m)) (w : ℂ)
    (x : CapSp E m) : qdet (resE E (CapSp E m) hS) w x = cpol m w • x := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  have := qdet_int (CapSp E m).subtype (E := resE E (CapSp E m) hS) (E' := E) (fun a b y => rfl) w x
  simp only [Submodule.subtype_apply] at this
  rw [this]
  exact mem_CapSp.1 x.2 w

end Restr

section Proj

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}

def projI (h : DirectSum.IsInternal S) (i : ι) : V →ₗ[ℂ] S i :=
  (DirectSum.component ℂ ι (fun j => S j) i).comp (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm.toLinearMap

theorem projI_apply (h : DirectSum.IsInternal S) (i : ι) (v : V) :
    projI h i v = (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm v i := rfl

theorem projI_self (h : DirectSum.IsInternal S) {i : ι} (x : S i) : projI h i (x : V) = x := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_same h x

theorem projI_ne (h : DirectSum.IsInternal S) {i j : ι} (hij : j ≠ i) (x : S j) : projI h i (x : V) = 0 := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_ne h hij x

theorem projI_sum (h : DirectSum.IsInternal S) (y : ∀ j, S j) (i : ι) : projI h i (∑ j, (y j : V)) = y i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single i (fun j _ hj => projI_ne h hj (y j)) (fun hi => absurd (Finset.mem_univ i) hi)]
  exact projI_self h (y i)

theorem sum_projI (h : DirectSum.IsInternal S) (v : V) : ∑ j, (projI h j v : V) = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h with he
  have h1 : DirectSum.coeLinearMap S (e.symm v) = v := e.apply_symm_apply v
  conv_rhs => rw [← h1, ← DirectSum.sum_univ_of (e.symm v)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [DirectSum.coeLinearMap_of]
  rfl

theorem projI_comm (h : DirectSum.IsInternal S) (T : Module.End ℂ V) (hT : ∀ j, ∀ v ∈ S j, T v ∈ S j) (i : ι) (v : V) :
    projI h i (T v) = T.restrict (hT i) (projI h i v) := by
  have e : T v = ∑ j, ((T.restrict (hT j) (projI h j v) : S j) : V) := by
    conv_lhs => rw [← sum_projI h v]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  rw [e, projI_sum]

end Proj

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatNormBound
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem zhat_norm_bound : C2.ZhatBound := by
  intro k r z z'
  set K : Fin (r + 1) → Fin (r + 1) → ℝ := fun a b =>
    ∑ i, ‖fvec k r z a i‖ * ∑ j, (∑ p, ‖Hpk k r i p‖) * ‖fvec k r z' b j‖ with hK
  refine ⟨∑ a, ∑ b, K a b, fun g => ?_⟩
  have hg : ∀ p j, ‖g p j‖ ≤ B.gN g := by
    intro p j
    unfold B.gN
    rw [← Real.sqrt_sq (norm_nonneg (g p j)), ← Complex.normSq_eq_norm_sq]
    apply Real.sqrt_le_sqrt
    exact le_trans (Finset.single_le_sum (f := fun j => Complex.normSq (g p j))
      (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j))
      (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)) (Finset.mem_univ p))
  have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have hKnn : ∀ a b, 0 ≤ K a b := fun a b => Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg (fun j _ => mul_nonneg (Finset.sum_nonneg (fun p _ => norm_nonneg _)) (norm_nonneg _))))
  have hC : 0 ≤ ∑ a, ∑ b, K a b := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hKnn a b))
  unfold C2.mx
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hgN)).mpr
  intro a
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hgN)).mpr
  intro b
  show ‖Zhat k r z z' g a b‖ ≤ _
  have hent : ‖Zhat k r z z' g a b‖ ≤ B.gN g * K a b := by
    simp only [Zhat, herm, Matrix.mulVec_mulVec]
    calc ‖star (fvec k r z a) ⬝ᵥ ((Hpk k r * g) *ᵥ fvec k r z' b)‖
        ≤ ∑ i, ‖fvec k r z a i‖ * ∑ j, ‖(Hpk k r * g) i j‖ * ‖fvec k r z' b j‖ := by
          simp only [dotProduct, Matrix.mulVec]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
          rw [norm_mul, Pi.star_apply, norm_star]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
          rw [norm_mul]
      _ ≤ ∑ i, ‖fvec k r z a i‖ * ∑ j, ((∑ p, ‖Hpk k r i p‖) * B.gN g) * ‖fvec k r z' b j‖ := by
          gcongr with i _ j _
          rw [Matrix.mul_apply]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum (fun p _ => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg p j) (norm_nonneg _))
      _ = B.gN g * K a b := by
          simp only [hK, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          ring
  calc ‖Zhat k r z z' g a b‖ ≤ B.gN g * K a b := hent
    _ ≤ B.gN g * ∑ a, ∑ b, K a b := mul_le_mul_of_nonneg_left
        (le_trans (Finset.single_le_sum (f := fun b => K a b) (fun b _ => hKnn a b) (Finset.mem_univ b))
          (Finset.single_le_sum (f := fun a => ∑ b, K a b)
            (fun a _ => Finset.sum_nonneg (fun b _ => hKnn a b)) (Finset.mem_univ a))) hgN
    _ = (∑ a, ∑ b, K a b) * B.gN g := mul_comm _ _

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SectionDecompositionOfParts
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x7

set_option maxHeartbeats 400000 in
theorem c2_section_decomp_of_pieces : C2.SectionDecompOfParts := by
  intro _ hC1iii hURI hUp _ hUM _ hTM k r z z' γ hstd hpos hmono s hs
  have hz := hstd.2.1
  have hU := hUM k r z hz
  have hSg := symmetric_group_holds k r z hz.1
  have hNg := unipotent_subgroup_holds k r

  have hu1 : C2.uMap k r z 1 = 1 := hU.2 1 (one_mem_UW z)
  have huinv : ∀ x ∈ Sset k r z, C2.uMap k r z x⁻¹ = (C2.uMap k r z x)⁻¹ := by
    intro x hx
    have hxi := hSg.2.2 x hx
    have hxu : IsUnit x.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hx)
    have : C2.uMap k r z x * C2.uMap k r z x⁻¹ = 1 := by
      rw [← (hU.1 x hx).2.2 _ hxi, Matrix.mul_nonsing_inv _ hxu, hu1]
    exact (Matrix.inv_eq_right_inv this).symm

  have huSg : ∀ σ ∈ C2.Sg k r z z' γ, σ ∈ Sset k r z ∧ ∃ v, v ∈ C2.UTset (r + 1) ∧ vᴴ ∈ C2.LPg (Zhat k r z z' γ) ∧
      C2.uMap k r z σ = v := by
    rintro σ ⟨n0, hn0, v, hv, hvL, h, hh, rfl⟩
    obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
    have hn0S : n0 ∈ Sset k r z := N_sub_S hn0.1
    have hτS : C2.tauM k r z v ∈ Sset k r z := N_sub_S hτN
    have hhS : h ∈ Sset k r z := UW_sub_S hh
    have hs1 := hSg.2.1 _ hn0S _ hτS
    refine ⟨hSg.2.1 _ hs1 _ hhS, v, hv, hvL, ?_⟩
    rw [(hU.1 _ hs1).2.2 h hhS, (hU.1 _ hn0S).2.2 _ hτS, hn0.2, hτu, hU.2 h hh, Matrix.one_mul, Matrix.mul_one]

  have hRimg : ∀ ρ ∈ C2.Rst k r z z' γ, C2.uMap k r z ρ ∈ C2.UTset (r + 1) ∧ (C2.uMap k r z ρ)ᴴ ∈ C2.Lstg (Zhat k r z z' γ) := by
    intro ρ hρ
    have hmap := (hC1iii k r z z' γ hstd hpos).1.mapsTo hρ
    obtain ⟨h1, h2, h3⟩ := hmap
    have : C2.uMap k r z ρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} :=
      ⟨h1, _, h2, h3⟩
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono] at this
    exact this
  have hRS : ∀ ρ ∈ C2.Rst k r z z' γ, ρ ∈ Sset k r z := fun ρ hρ => hρ.1.1
  obtain ⟨hus, husUT, _⟩ := hU.1 s hs
  obtain ⟨⟨uρ, v⟩, ⟨huρ, hv, huρL, hvL, hue⟩, huniq⟩ := hUp (r + 1) (Zhat k r z z' γ) hmono _ husUT
  simp only at huρ hv huρL hvL hue

  have huρR : uρ ∈ {u | u ∈ C2.UTset (r + 1) ∧ ∃ u' ∈ C2.UTset (r + 1), uᴴ * Zhat k r z z' γ * u' = Zhat k r z z' γ} := by
    rw [hURI (r + 1) (Zhat k r z z' γ) hmono]; exact ⟨huρ, huρL⟩
  obtain ⟨u', hu', hu'e⟩ := huρR.2
  have hmemT : (uρ, u') ∈ {p : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ |
      p.1 ∈ C2.UTset (r + 1) ∧ p.2 ∈ C2.UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} :=
    ⟨huρ, hu', hu'e⟩
  obtain ⟨ρ, hρ, hρe⟩ := (hC1iii k r z z' γ hstd hpos).1.surjOn hmemT
  have hρu : C2.uMap k r z ρ = uρ := congrArg Prod.fst hρe
  have hρS := hRS ρ hρ
  have hρu' : IsUnit ρ.det := WeylGroupFacts.isUnit_of_uh (Sset_UH hρS)
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = ρ⁻¹ * s := ⟨_, rfl⟩
  have hσS : σ ∈ Sset k r z := by rw [hσ]; exact hSg.2.1 _ (hSg.2.2 _ hρS) _ hs
  have hσu : C2.uMap k r z σ = v := by
    rw [hσ, (hU.1 _ (hSg.2.2 _ hρS)).2.2 s hs, huinv ρ hρS, hρu, hue, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (C2x2.ut_unit huρ), Matrix.one_mul]
  obtain ⟨h1, hh1, n1, hn1, hσe⟩ := hσS
  have hh1S := UW_sub_S hh1
  have hn1S := N_sub_S (z := z) hn1
  have hn1u : C2.uMap k r z n1 = v := by
    rw [← hσu, hσe, (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1, Matrix.one_mul]
  have hh1inv := WeylGroupFacts.uw_inv hh1
  have hh1u : IsUnit h1.det := WeylGroupFacts.isUnit_of_uh hh1.1
  have hn2 : h1 * n1 * h1⁻¹ ∈ Nset k r := (unitary_weyl_normal_holds k r z hz.1 h1 hh1 n1 hn1).1
  have hn2u : C2.uMap k r z (h1 * n1 * h1⁻¹) = v := by
    rw [(hU.1 _ (hSg.2.1 _ hh1S _ hn1S)).2.2 _ (UW_sub_S hh1inv), (hU.1 _ hh1S).2.2 _ hn1S, hU.2 _ hh1,
      hU.2 _ hh1inv, hn1u, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨hτN, _, hτu⟩ := hTM k r z hz v hv
  obtain ⟨τv, hτv⟩ : ∃ τv, τv = C2.tauM k r z v := ⟨_, rfl⟩
  rw [← hτv] at hτN hτu
  have hτS : τv ∈ Sset k r z := N_sub_S hτN
  have hτunit : IsUnit τv.det := WeylGroupFacts.isUnit_of_uh hτN.1
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = h1 * n1 * h1⁻¹ * τv⁻¹ := ⟨_, rfl⟩
  have hn0N : n0 ∈ Nset k r := by rw [hn0]; exact hNg.2.1 _ hn2 _ (hNg.2.2 _ hτN)
  have hn0u : C2.uMap k r z n0 = 1 := by
    rw [hn0, (hU.1 _ (N_sub_S hn2)).2.2 _ (hSg.2.2 _ hτS), huinv _ hτS, hn2u, hτu,
      Matrix.mul_nonsing_inv _ (C2x2.ut_unit hv)]
  have hσdec : σ = n0 * τv * h1 := by
    rw [hσe, hn0, Matrix.mul_assoc (h1 * n1 * h1⁻¹), Matrix.nonsing_inv_mul _ hτunit, Matrix.mul_one,
      Matrix.mul_assoc (h1 * n1), Matrix.nonsing_inv_mul _ hh1u, Matrix.mul_one]
  have hσSg : σ ∈ C2.Sg k r z z' γ := ⟨n0, ⟨hn0N, hn0u⟩, v, hv, hvL, h1, hh1, by rw [hσdec, hτv]⟩
  refine ⟨(ρ, σ), ⟨hρ, hσSg, ?_⟩, ?_⟩
  · show s = ρ * σ
    rw [hσ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hρu', Matrix.one_mul]
  · rintro ⟨ρ', σ'⟩ ⟨hρ', hσ', hse⟩
    simp only at hρ' hσ' hse
    obtain ⟨hσ'S, v', hv', hv'L, hσ'u⟩ := huSg σ' hσ'
    obtain ⟨hρ'U, hρ'L⟩ := hRimg ρ' hρ'
    have hus' : C2.uMap k r z s = C2.uMap k r z ρ' * v' := by
      rw [hse, (hU.1 _ (hRS ρ' hρ')).2.2 _ hσ'S, hσ'u]
    have := huniq (C2.uMap k r z ρ', v') ⟨hρ'U, hv', hρ'L, hv'L, hus'⟩
    rw [Prod.ext_iff] at this
    simp only at this
    have hρρ : ρ' = ρ := (hC1iii k r z z' γ hstd hpos).2.1 hρ' hρ (this.1.trans hρu.symm)
    subst hρρ
    have hρ'u : IsUnit ρ'.det := hρu'
    have : σ' = ρ'⁻¹ * s := by
      rw [hse, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ'u, Matrix.one_mul]
    rw [this, hσ]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondExpansionIdentity
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem det_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.of fun a b => star (M a b)).det = star M.det := by
  have e : (Matrix.of fun a b => star (M a b)) = M.conjTranspose.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]

theorem keyS_sR (k r m : ℕ) (hm : m ≤ r) (l : Fin m) : keyS k r (sR k r m hm l) = l.val := by
  simp only [sR]
  rw [keyS_esI]
  rfl

theorem AAv_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (ell : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → p ∉ Set.range (sR k r i0 hi0) → y a p = 0)
    (hh : ∀ a b : Fin i0, y (Fin.castLE hi0 a) (sR k r i0 hi0 b) = star (h a b)) :
    AAv k r E y i0 hi0 ell = star h.det • qminor E (sR k r i0 hi0) (sR k r i0 hi0) (ell + (i0 : ℂ) - 1) := by
  classical
  have hsv : ∀ l : Fin i0, (sR k r i0 hi0 l).val = 2 * r + k - l.val := by
    intro l
    simp [sR, Formalism.QuantumDeterminants.esI]
  have he : StrictMono (fun l => keyS k r (sR k r i0 hi0 l)) := by
    intro a b hab
    simp only [keyS_sR]
    exact hab
  have hX : ∀ (a : Fin i0) (p : Fin (2 * r + k + 1)), p ∉ Set.range (sR k r i0 hi0) →
      y (Fin.castLE hi0 a) p = 0 := by
    intro a p hp
    exact hz _ p a.isLt hp
  have hu : ∀ c : Fin i0 → Fin (2 * r + k + 1), StrictMono (fun l => keyS k r (c l)) →
      (∀ l, c l ∈ Set.range (sR k r i0 hi0)) → c = sR k r i0 hi0 := by
    intro c hc hS
    exact uniq_key (keyS k r) (keyS_inj k r) (sR k r i0 hi0) c he hc hS
  have hs := sum_single (M := A) (fun B : Fin i0 → Fin (2 * r + k + 1) => StrictMono (fun l => keyS k r (B l)))
    (fun a p => y (Fin.castLE hi0 a) p) (Set.range (sR k r i0 hi0)) hX (sR k r i0 hi0) he hu
    (fun B => qminor E B (sR k r i0 hi0) (ell + (i0 : ℂ) - 1))
  have hdet : (Matrix.of fun a l : Fin i0 => y (Fin.castLE hi0 a) (sR k r i0 hi0 l)).det = star h.det := by
    rw [← det_star]
    congr 1
    ext a b
    exact hh a b
  unfold AAv
  rw [← hdet]
  convert hs using 1

theorem second_expansion_identity : ExpansionDualColumn := by
  intro A _ _ M _ _ k r z' E La y i0 s h t ell hs hj hG hR hh ht hy
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  have hm' : i0 + s' + 1 ≤ r := by omega
  rw [AAv_congr k r E y (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm]
  set e2 : Fin (i0 + s') → Fin (2 * r + k + 1) :=
    fun l => sR k r (i0 + s' + 1) hm' ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) with he2def
  have he2v : ∀ l, (e2 l).val = 2 * r + k - ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp [e2, sR, esI]
  have he2k : ∀ l, keyS k r (e2 l) = ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp only [e2]; rw [keyS_sR]
  have he2 : StrictMono (fun l => keyS k r (e2 l)) := by
    intro a b hab
    simp only [he2k]; exact Fin.strictMono_succAbove _ hab
  have hAA : AAv k r E y (i0 + s') hm ell =
      star (h.det * t ^ s' * sgnW s') • qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1) := by
    unfold AAv
    rw [sum_single (fun B => StrictMono (fun l => keyS k r (B l))) (fun a p => y (Fin.castLE hm a) p)
      (Set.range e2) ?_ e2 he2 ?_]
    · congr 1
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp, ← det_star]
      congr 1
      ext a l
      simp only [Matrix.of_apply]
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      rw [hy _ _ (by simp; omega), if_pos (by rw [he2v]; omega), he2v]
      congr 2 <;> (try simp) <;> omega
    · intro a p hp
      rw [hy _ _ (by simp; omega)]
      split_ifs with h1
      · by_cases hpi : 2 * r + k - p.val = i0
        · rw [hpi, zb_col_zero i0 s' h t _ (by simp), star_zero]
        · exfalso; apply hp
          refine ⟨⟨if 2 * r + k - p.val < i0 then 2 * r + k - p.val else 2 * r + k - p.val - 1,
            by split_ifs <;> omega⟩, ?_⟩
          ext; rw [he2v, succAbove_val]; simp only; split_ifs <;> omega
      · rfl
    · intro c hc hS; exact uniq_key (keyS k r) (keyS_inj k r) _ _ he2 hc hS
  have hhead : AAv k r E y i0 (by omega) ell =
      star h.det • qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1) := by
    apply AAv_head
    · intro a p ha hp
      rw [hy _ _ (by omega)]
      split_ifs with hc
      · have hx : ¬ (2 * r + k - p.val < i0) := by
          intro hlt; apply hp
          exact ⟨⟨2 * r + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩
        unfold Zb; rw [dite_eq_left ha, dite_eq_right hx, star_zero]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hy _ _ (by simp; omega)]
      rw [if_pos (by simp [sR, esI]; omega)]
      have hsv : (sR k r i0 (by omega) b).val = 2 * r + k - b.val := by simp [sR, esI]
      have hav : (Fin.castLE (by omega : i0 ≤ r) a).val = a.val := by simp
      unfold Zb
      rw [hav, hsv]
      rw [dite_eq_left a.isLt, dite_eq_left (by omega)]
      congr 2
      apply Fin.ext; simp only [Fin.val_mk]; omega
  have hP := third_peeling_identity A k r z' E hG (i0 + s') hm' ⟨i0, by omega⟩ ell
  have hLa : La (qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1)) =
      La (qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1)) := la_congr hR hP
  rw [hAA, hhead, map_smul, map_smul, hLa, (derivative_leading_zb i0 (s' + 1) h t).1, (derivative_leading_zb i0 (s' + 1) h t).2,
    smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [star_mul', star_pow, star_sgnW, sgnW_succ, Nat.add_sub_cancel, star_neg, star_one]
  rw [scal_E (star h.det) (star t) (sgnW s') ((-1) ^ s') s' (star_ne_zero.mpr hh) (star_ne_zero.mpr ht)
    (sgnW_sq s') (neg_one_sq' s')]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def sc (ε x : ℝ) : ℝ := Real.smoothTransition ((x - ε / 4) / (ε / 4))

lemma sc_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 4) : sc ε x = 0 := by
  unfold sc
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_iff.2 (Or.inr ⟨by linarith, by linarith⟩))

lemma sc_one {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 ≤ x) : sc ε x = 1 := by
  unfold sc
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma sc_cd (ε : ℝ) : ContDiff ℝ ∞ (sc ε) := by
  show ContDiff ℝ ∞ (fun x => Real.smoothTransition ((x - ε / 4) / (ε / 4)))
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

def hh (ε x : ℝ) : ℝ := sc ε x * x ^ (-(1 / 2 : ℝ))

lemma hh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (hh ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ε / 8 < x
  · have hx0 : 0 < x := by linarith
    show ContDiffAt ℝ ∞ (fun y => sc ε y * y ^ (-(1 / 2 : ℝ))) x
    exact ((sc_cd ε).contDiffAt).mul (Real.contDiffAt_rpow_const_of_ne hx0.ne')
  · have h0 : hh ε =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < ε / 4 by linarith)] with y hy
      simp [hh, sc_zero hε (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq h0

lemma hh_ev {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 < x) :
    hh ε =ᶠ[nhds x] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [hh, sc_one hε (le_of_lt hy), one_mul]

lemma hh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) {x : ℝ} (hx : ε ≤ x) :
    ‖iteratedFDeriv ℝ j (hh ε) x‖ ≤ |(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) := by
  have hx0 : 0 < x := lt_of_lt_of_le hε hx
  have h2 : ε / 2 < x := by linarith
  have heq : iteratedFDeriv ℝ j (hh ε) x = iteratedFDeriv ℝ j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) x := by
    first
    | exact ((hh_ev hε h2).iteratedFDeriv ℝ j).eq_of_nhds
    | exact (hh_ev hε h2).iteratedFDeriv_eq j
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hexp : -(1 / 2 : ℝ) - j ≤ 0 := by linarith
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  first
  | exact Real.rpow_le_rpow_of_exponent_nonpos hε hx hexp
  | exact Real.rpow_le_rpow_of_nonpos hε hx hexp

def Phh (ε : ℝ) (z : ℂ) : ℂ := ((hh ε z.re : ℝ) : ℂ)

lemma Phh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (Phh ε) := by
  show ContDiff ℝ ∞ (fun z : ℂ => ((hh ε z.re : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((hh_cd hε).comp Complex.reCLM.contDiff)

lemma Phh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | ε ≤ z.re}, ‖iteratedFDeriv ℝ j (Phh ε) z‖ ≤ B := by
  refine ⟨‖Complex.ofRealCLM‖ * (|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) *
    ‖Complex.reCLM‖ ^ j), fun z hz => ?_⟩
  have hh' : ContDiff ℝ ∞ (hh ε ∘ Complex.reCLM) := (hh_cd hε).comp Complex.reCLM.contDiff
  have e : Phh ε = Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM) := rfl
  rw [e]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM)) z‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖ :=
        by
          first
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh' z (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt z (by exact_mod_cast le_top)
    _ ≤ _ := by
        gcongr
        calc ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖
            = ‖(iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)).compContinuousLinearMap
                fun _ => Complex.reCLM‖ := by
              first
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) z (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε).contDiffAt (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) (by exact_mod_cast le_top)]
          _ ≤ ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ∏ _i : Fin j, ‖Complex.reCLM‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ = ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ‖Complex.reCLM‖ ^ j := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := by
              gcongr
              exact hh_bound hε j hz

lemma sqrt_div_eq {T x : ℝ} (hT : 0 < T) (hx : 0 < x) : Real.sqrt (T / x) = Real.sqrt T * x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_div hT.le x, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma admissible_of_unit_words {k r i : ℕ} {u v : List (Mat k r)} (h : C6.UnitWords k r u v i) : admitted i (wL u ++ wR v) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨u, v, h1, h2, h3.le, rfl⟩

lemma poly_adm {k r d n : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) :
    ContDiff ℝ ∞ P ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ C * gN g ^ d := by
  obtain ⟨hc, hb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r d P hP
  refine ⟨hc, ?_⟩
  obtain ⟨C, hC⟩ := hb n
  refine ⟨max C 0, le_max_right _ _, fun w hw g hg => ?_⟩
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
  have := hC u v hu hv hl g hg
  simp only [List.map_const', List.sum_replicate, smul_zero, Nat.cast_zero, add_zero, Real.rpow_natCast] at this
  rw [← dLR_eq]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by have := gN_pos hg; positivity))

theorem fibre_unit_normalization : C6.FibUnit := by
  intro k r m om Gp T hom hGp hT _ ε hε i
  set ψ : Mat k r → ℂ := fun g => ((Gp g : ℝ) : ℂ) with hψdef
  obtain ⟨hψc, CG, hCG0, hCG⟩ := poly_adm (n := i) hGp
  have hGpc : Continuous Gp := by
    have : Gp = fun g => (ψ g).re := by funext g; simp [hψdef]
    rw [this]; exact Complex.continuous_re.comp hψc.continuous

  obtain ⟨C₁, hC₁0, hC₁⟩ := fdb ψ hψc {g | g ∈ GV k r ∧ ε ≤ Gp g} {z : ℂ | ε ≤ z.re}
    (fun g hg => by simpa [hψdef] using hg.2) gN (fun g hg => gN_ge_one hg.1) (2 * r + 2) 0 CG i
    (by
      intro w hw hne g hg
      have h1 := hCG w hw g hg.1
      have hl : 1 ≤ w.length := List.length_pos_iff.mpr hne
      refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg.1) ?_) hCG0)
      nlinarith)
    i ℂ (Phh ε) (Phh_cd hε) (Phh_bound hε)

  have hoa : ∀ a, ContDiff ℝ ∞ (fun g => om g a) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted i w → ∀ g ∈ GV k r,
      ‖Dw w (fun g => om g a) g‖ ≤ C * gN g ^ (r + 1) := fun a => poly_adm (hom a)
  choose hoc Co hCo0 hCo using hoa
  set C₂ : ℝ := ∑ a, Co a with hC₂
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun a _ => hCo0 a
  have hCoa : ∀ a, Co a ≤ C₂ := fun a => Finset.single_le_sum (fun b _ => hCo0 b) (Finset.mem_univ a)
  refine ⟨Real.sqrt T * (2 ^ i * (C₁ * C₂)), fun u v huv g hg hεg => ?_⟩
  set w := wL u ++ wR v with hw
  have hwA : admitted i w := admissible_of_unit_words huv
  have hwl : w.length = i := by rw [hw, len_LR]; exact huv.2.2
  have hlie : ∀ x ∈ w, inLie k r x.2 := lie_LR (unit_lie huv.1) (unit_lie huv.2.1)

  set Ut : Mat k r → (Fin m → ℂ) := fun g a => (Real.sqrt T : ℂ) * (Phh ε (ψ g) * om g a) with hUt
  have hUtc : ContDiff ℝ ∞ Ut :=
    contDiff_pi.2 fun a => contDiff_const.mul (((Phh_cd hε).comp hψc).mul (hoc a))
  have hO : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGpc
  have heq : ∀ g' ∈ GV k r, g' ∈ {g : Mat k r | ε / 2 < Gp g} →
      (fun g' => C6.unitOf T (Gp g') (om g')) g' = Ut g' := by
    intro g' _ hg'
    have hp : 0 < Gp g' := by simp only [Set.mem_setOf_eq] at hg'; linarith
    funext a
    simp only [C6.unitOf, hUt, Phh, hψdef, Complex.ofReal_re, Pi.smul_apply, smul_eq_mul]
    rw [AdmissibleLieWords.hh, sc_one hε (le_of_lt hg'), one_mul, sqrt_div_eq hT hp]
    push_cast; ring
  rw [dLR_eq, Dw_congr_loc hlie hO heq g hg (by show ε / 2 < Gp g; linarith)]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (mul_nonneg hC₁0 hC₂0))) (pow_nonneg (gN_pos hg).le _))).2
  intro a
  have e1 : Dw w Ut g a = Dw w (fun g => Ut g a) g := by
    have := dw_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) a) w hUtc
    exact (congrFun this g).symm
  rw [e1]
  have e2 : (fun g => Ut g a) = fun g => (Real.sqrt T : ℂ) • (Phh ε (ψ g) * om g a) := by
    funext g; simp [hUt, smul_eq_mul]
  rw [e2, Dw_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hL := leibB g (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) w (fun g => Phh ε (ψ g)) (fun g => om g a)
    ((Phh_cd hε).comp hψc) (hoc a) (by
      intro w₁ w₂ hs
      have hlen := spl_len hs
      obtain ⟨h₁, h₂, _⟩ := hs
      have b1 := hC₁ w₁ (Adm_sub h₁ hwA) (by have := h₁.length_le; omega) g ⟨hg, hεg⟩
      have b2 := (hCo a w₂ (Adm_sub h₂ hwA) g hg).trans
        (mul_le_mul_of_nonneg_right (hCoa a) (pow_nonneg (gN_pos hg).le _))
      have hexp : (2 * r + 2 + 0) * w₁.length + (r + 1) ≤ (r + 1) * (2 * i + 1) := by
        have := h₁.length_le; rw [hwl] at this; nlinarith
      calc ‖Dw w₁ (fun g => Phh ε (ψ g)) g‖ * ‖Dw w₂ (fun g => om g a) g‖
          ≤ (C₁ * gN g ^ ((2 * r + 2 + 0) * w₁.length)) * (C₂ * gN g ^ (r + 1)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hC₁0 (pow_nonneg (gN_pos hg).le _))
        _ = C₁ * C₂ * gN g ^ ((2 * r + 2 + 0) * w₁.length + (r + 1)) := by rw [pow_add]; ring
        _ ≤ C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg) hexp) (mul_nonneg hC₁0 hC₂0))
  rw [hwl] at hL
  calc ‖Dw w (fun g => Phh ε (ψ g) * om g a) g‖ ≤ 2 ^ i * (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) := hL
    _ = 2 ^ i * (C₁ * C₂) * gN g ^ ((r + 1) * (2 * i + 1)) := by ring

end Formalism.FourierDecayAlt.P
end
end
