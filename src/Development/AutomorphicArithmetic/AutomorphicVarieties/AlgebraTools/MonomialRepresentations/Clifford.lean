module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Clifford
open Polynomial Matrix

namespace UpperTheory.V.AlgebraTools

section

variable {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V) (N : Subgroup G) [hN : N.Normal]

private def cliffTr (g : G) (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) where
  toSubmodule := W.toSubmodule.comap (ρ g)
  apply_mem_toSubmodule n v hv := by
    have h := W.apply_mem_toSubmodule ⟨g * n * g⁻¹, hN.conj_mem _ n.2 g⟩ hv
    have e : ρ (g * n * g⁻¹) (ρ g v) = ρ g (ρ n v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    change ρ g (ρ n v) ∈ W.toSubmodule
    rw [← e]
    exact h

private theorem cliffTr_mul (g h : G) (hgh : g * h = 1)
    (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    cliffTr ρ N h (cliffTr ρ N g W) = W := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change ρ g (ρ h v) ∈ W.toSubmodule ↔ _
  rw [← Module.End.mul_apply, ← map_mul, hgh, map_one]
  rfl

private def cliffIso (g : G) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) ≃o
      Subrepresentation (ρ.comp N.subtype : Representation K N V) :=
  Equiv.toOrderIso
    { toFun := cliffTr ρ N g
      invFun := cliffTr ρ N g⁻¹
      left_inv := cliffTr_mul ρ N g g⁻¹ (by simp)
      right_inv := cliffTr_mul ρ N g⁻¹ g (by simp) }
    (fun _ _ h _ hv => h hv) (fun _ _ h _ hv => h hv)

end

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.clifford :
    ∀ (K G V : Type) [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V)
      (N : Subgroup G) [N.Normal], ρ.IsIrreducible → Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  intro K G V _ _ _ _ _ ρ N _ hirr
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← sSup_simples_eq_top_iff_isSemisimpleModule]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)
  let A := {m : Submodule (MonoidAlgebra K N) (Representation.asModule (ρ.comp N.subtype)) |
    IsSimpleModule (MonoidAlgebra K N) m}
  have hA : ∀ m, m ∈ A ↔ IsAtom m := fun m => isSimpleModule_iff_isAtom
  change sSup A = ⊤
  have inv : ∀ g : G, ∀ v : V, v ∈ e.symm (sSup A) → ρ g v ∈ e.symm (sSup A) := by
    intro g v hv
    let φ := e.symm.trans ((UpperTheory.V.AlgebraTools.cliffIso ρ N g).trans e)
    have hφ : φ (sSup A) = sSup A := by
      rw [OrderIso.map_sSup]
      apply le_antisymm
      · refine iSup₂_le fun a ha => le_sSup ?_
        exact (hA _).2 ((φ.isAtom_iff a).2 ((hA a).1 ha))
      · refine sSup_le fun b hb => ?_
        have hb' : φ.symm b ∈ A := (hA _).2 ((φ.symm.isAtom_iff b).2 ((hA b).1 hb))
        have h := le_iSup₂ (f := fun a (_ : a ∈ A) => φ a) (φ.symm b) hb'
        simpa using h
    have h : v ∈ e.symm (φ (sSup A)) := by rw [hφ]; exact hv
    exact h
  let T : Subrepresentation ρ := ⟨(e.symm (sSup A)).toSubmodule, fun g v hv => inv g v hv⟩
  rcases eq_bot_or_eq_top T with hT | hT
  · exfalso
    have hmono : StrictMono (Subrepresentation.toSubmodule :
        Subrepresentation (ρ.comp N.subtype) → Submodule K V) :=
      fun x y h => h
    haveI := hmono.wellFoundedLT
    haveI : IsAtomic (Subrepresentation (ρ.comp N.subtype)) :=
      isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    have hne : (⊤ : Subrepresentation (ρ.comp N.subtype)) ≠ ⊥ := by
      intro h
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.ext
      exact (congrArg Subrepresentation.toSubmodule h).symm
    obtain ⟨a, ha, -⟩ :=
      (eq_bot_or_exists_atom_le (⊤ : Subrepresentation (ρ.comp N.subtype))).resolve_left hne
    have h1 : a ≤ e.symm (sSup A) := by
      have h0 : e a ≤ sSup A := le_sSup ((hA _).2 ((e.isAtom_iff a).2 ha))
      simpa using e.symm.monotone h0
    have h2 : (e.symm (sSup A)).toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hT
    apply ha.1
    apply Subrepresentation.ext
    apply le_antisymm _ bot_le
    intro v hv
    have h3 : v ∈ (e.symm (sSup A)).toSubmodule := h1 hv
    rw [h2] at h3
    exact h3
  · refine eq_top_iff.2 fun v _ => ?_
    have h3 : (show V from v) ∈ T.toSubmodule := by rw [hT]; exact Submodule.mem_top
    exact h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.HenselDiag
open Polynomial Matrix

section
variable {C ι : Type} [CommRing C] [Fintype ι] [DecidableEq ι]

private theorem res_one [IsLocalRing C] (u : Matrix ι ι C) :
    (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ↔ (IsLocalRing.residue C).mapMatrix u = 1 := by
  rw [← map_one (IsLocalRing.residue C).mapMatrix, ← sub_eq_zero, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, IsLocalRing.residue_eq_zero_iff]

private theorem unit_of_res [IsLocalRing C] (x : C) (h : IsLocalRing.residue C x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h ((IsLocalRing.residue_eq_zero_iff _).mpr hx)

private theorem res_diag [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) :
    (IsLocalRing.residue C).mapMatrix M = diagonal fun i => IsLocalRing.residue C (M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, IsLocalRing.residue_eq_zero_iff, h i j hij]

private theorem exists_root [HenselianLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι) :
    ∃ d : C, (Matrix.scalar ι d - M).det = 0 ∧ d - M i i ∈ IsLocalRing.maximalIdeal C := by
  have hc : M.charpoly.map (IsLocalRing.residue C) = ∏ j, (X - Polynomial.C (IsLocalRing.residue C (M j j))) := by
    rw [← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, res_diag M h, Matrix.charpoly_diagonal]
  have h1 : M.charpoly.eval (M i i) ∈ IsLocalRing.maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval_map_apply, hc, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have h2 : IsUnit (M.charpoly.derivative.eval (M i i)) := by
    apply unit_of_res
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hc,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, add_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
    rw [← map_sub]
    exact ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨d, hd, hd'⟩ := HenselianLocalRing.is_henselian M.charpoly M.charpoly_monic (M i i) h1 h2
  exact ⟨d, by rw [← Matrix.eval_charpoly]; exact hd, hd'⟩

private theorem exists_vec [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι)
    (d : C) (hd : (Matrix.scalar ι d - M).det = 0) (hd' : d - M i i ∈ IsLocalRing.maximalIdeal C) :
    ∃ v : ι → C, (∀ k, ∑ j, M k j * v j = v k * d) ∧ v i = 1 ∧ ∀ k, k ≠ i → v k ∈ IsLocalRing.maximalIdeal C := by
  have hdi : IsLocalRing.residue C d = IsLocalRing.residue C (M i i) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd'
  set A := (Matrix.scalar ι d - M).adjugate with hA
  have h0 : (Matrix.scalar ι d - M) * A = 0 := by rw [hA, Matrix.mul_adjugate, hd, zero_smul]
  have h1 : (IsLocalRing.residue C).mapMatrix (Matrix.scalar ι d - M) =
      diagonal fun k => IsLocalRing.residue C (M i i - M k k) := by
    rw [map_sub, res_diag M h]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hdi]
    · simp [hab]
  have h2 : (IsLocalRing.residue C).mapMatrix A =
      diagonal fun k => ∏ j ∈ Finset.univ.erase k, IsLocalRing.residue C (M i i - M j j) := by
    rw [hA, RingHom.map_adjugate, h1, Matrix.adjugate_diagonal]
  have h3 : IsUnit (A i i) := by
    apply unit_of_res
    have := congrFun (congrFun h2 i) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at this
    rw [this]
    exact Finset.prod_ne_zero_iff.mpr fun a ha => ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨c, hc⟩ := h3.exists_right_inv
  refine ⟨fun k => A k i * c, fun k => ?_, hc, fun k hk => ?_⟩
  · rw [sub_mul, sub_eq_zero] at h0
    have := congrFun (congrFun h0 k) i
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply] at this
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, ← this]; ring
  · have := congrFun (congrFun h2 k) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hk,
      IsLocalRing.residue_eq_zero_iff] at this
    exact Ideal.mul_mem_right _ _ this

end

theorem UpperTheory.V.AlgebraTools.henselDiag :
    ∀ (C ι : Type) [CommRing C] [HenselianLocalRing C] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C),
      (∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) → (∀ i j, i ≠ j → IsUnit (M i i - M j j)) →
      ∃ (u : Matrix ι ι C) (d : ι → C), (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ∧ M * u = u * diagonal d ∧
        (∀ i, d i - M i i ∈ IsLocalRing.maximalIdeal C) ∧
        ∀ (u' : Matrix ι ι C) (d' : ι → C), (∀ i j, (u' - 1) i j ∈ IsLocalRing.maximalIdeal C) → M * u' = u' * diagonal d' →
          d' = d ∧ ∃ t : ι → C, u' = u * diagonal t := by
  intro C ι _ _ _ _ M h hu
  choose d hd hd' using exists_root M h hu
  choose v hv hv1 hv0 using fun i => exists_vec M h hu i (d i) (hd i) (hd' i)
  let u : Matrix ι ι C := Matrix.of fun k i => v i k
  have hu1 : ∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [u, hv1]
    · simpa [u, hij] using hv0 j i hij
  have hMu : M * u = u * diagonal d := by
    ext k i
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    exact hv i k
  refine ⟨u, d, hu1, hMu, hd', fun u' d' hu' hM' => ?_⟩
  have r1 := (res_one u).mp hu1
  have r2 := (res_one u').mp hu'
  have hdet : IsUnit u := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply unit_of_res
    rw [RingHom.map_det, r1, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨U, hU⟩ := hdet
  set w : Matrix ι ι C := (U⁻¹ : (Matrix ι ι C)ˣ) * u' with hw
  have huw : u' = u * w := by rw [hw, ← hU, Units.mul_inv_cancel_left]
  have r3 : (IsLocalRing.residue C).mapMatrix w = 1 := by
    rw [huw, map_mul, r1, one_mul] at r2; exact r2
  have hcomm : diagonal d * w = w * diagonal d' := by
    rw [huw, ← mul_assoc, hMu, mul_assoc, mul_assoc, ← hU] at hM'
    exact (Units.mul_right_inj U).mp hM'
  have he : ∀ i j, (d i - d' j) * w i j = 0 := by
    intro i j
    have := congrFun (congrFun hcomm i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    rw [sub_mul, this]; ring
  have hd2 : ∀ j, IsLocalRing.residue C (d' j) = IsLocalRing.residue C (M j j) := by
    intro j
    have := congrArg (IsLocalRing.residue C).mapMatrix hM'
    rw [map_mul, map_mul, r2, mul_one, one_mul] at this
    have := congrFun (congrFun this j) j
    simpa using this.symm
  have hd1 : ∀ j, IsLocalRing.residue C (d j) = IsLocalRing.residue C (M j j) := by
    intro j
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd' j
  constructor
  · funext i
    have hwi : IsUnit (w i i) := by
      apply unit_of_res
      have := congrFun (congrFun r3 i) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq] at this
      rw [this]; exact one_ne_zero
    exact (sub_eq_zero.mp (hwi.mul_left_eq_zero.mp (he i i))).symm
  · refine ⟨fun i => w i i, ?_⟩
    rw [huw]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      refine (unit_of_res (d i - d' j) ?_).mul_right_eq_zero.mp (he i j)
      rw [map_sub, hd1, hd2, ← map_sub]
      exact ((hu i j hij).map _).ne_zero
end
