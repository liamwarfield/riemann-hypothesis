module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SplitRes
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem split_r {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (b : O →+* R) (g : Γ) :
    (Φ.split b).r g = Matrix.diagonal fun i => b (Φ.χ i g) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Fr.split, mapRep, diagRep]
  · simp [Fr.split, mapRep, diagRep, Matrix.diagonal_apply_ne _ h]

private theorem split_conj {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (b : O →+* R) (v : Φ.ι)
    (g : Γ) : adj ((Φ.split b).n v) * (Φ.split b).r g * (Φ.split b).n v = Matrix.diagonal fun i => b (Φ.χ i g) := by
  show adj 1 * _ * 1 = _
  rw [(grp R).2.2.2.2.1, one_mul, mul_one, split_r]

private theorem adj_diag {R : Type} [CommRing R] (d : Fin 4 → R) :
    adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
  ext i j
  rw [adj_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    fin_cases i <;> simp [sgn]
  · rw [Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), smul_zero]

private theorem res_self {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsCO Λ (ResidueField Λ)] (x : ResidueField Λ) :
    res Λ (ResidueField Λ) x = x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  have := (res Λ (ResidueField Λ)).commutes a
  rwa [IsLocalRing.ResidueField.algebraMap_eq] at this

theorem UpperTheory.V.Ws.sxSplitRes :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Φ : Fr O Γ} {l : ℕ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} [IsCO Λ (ResidueField Λ)], Φ.Std l a → Φ.IsRes ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) ∧ Φ.Lifts a (Φ.split ((residue Λ).comp a)) (Φ.split ((residue Λ).comp a)) := by
  intro O Γ _ _ _ _ Φ l Λ _ _ a _ hs
  have ok := hs.ok
  have hψ : ∀ v i s, (Φ.split ((residue Λ).comp a)).ψ v i s = (residue Λ).comp a (Φ.χ i s) := by
    intro v i s
    unfold PD.ψ
    rw [split_conj, Matrix.diagonal_apply_eq]
  have hpair : Φ.IsPair ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) := by
    refine ⟨fun g => ?_, fun g hg => ?_, ?_, fun v => ?_, fun v s _ => ?_, fun v s hs' i => ?_⟩
    · show adj _ * _ = _
      rw [split_r, adj_diag, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        rw [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
          ← map_mul, ← Units.val_mul, mul_comm, ok.mul]
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    · rw [split_r, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact ok.kill g hg i
    · rw [split_r]
      exact Matrix.isDiag_diagonal _
    · show IsLow (1 : M4 (ResidueField Λ))
      refine ⟨?_, fun i => Matrix.one_apply_eq i, fun i j hij => Matrix.one_apply_ne hij.ne⟩
      show adj 1 * 1 = (1 : ResidueField Λ) • 1
      rw [(grp _).2.2.2.2.1, mul_one, one_smul]
    · rw [split_conj]
      intro i j hji
      exact Matrix.diagonal_apply_ne _ hji.ne'
    · rw [hψ]
      exact (hs.mu v s hs').2 i
  have hres : Φ.Res ((residue Λ).comp a) (Φ.split ((residue Λ).comp a)) :=
    ⟨fun g i => by rw [split_r, Matrix.diagonal_apply_eq], fun v s _ i => hψ v i s,
      Or.inr fun g i j hij _ => by rw [split_r, Matrix.diagonal_apply_ne _ hij]⟩
  have hcont : ∀ I, (Φ.split ((residue Λ).comp a)).Cont I := by
    intro I i j N
    by_cases h : i = j
    · subst h
      simp only [split_r, Matrix.diagonal_apply_eq]
      exact (ok.lc i).comp _
    · simp only [split_r, Matrix.diagonal_apply_ne _ h, map_zero]
      exact IsLocallyConstant.const _
  refine ⟨⟨hpair, hres, hcont ⊥⟩, ⟨?_, hcont _, ?_⟩⟩
  · rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact hpair
  · apply PD.ext
    · exact MonoidHom.ext fun g => Matrix.ext fun i j => res_self _
    · funext v
      exact Matrix.ext fun i j => res_self _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SubMemMax
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearConj
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

private theorem nc_wt_self (i : Fin 4) : wt i i = 0 := by revert i; decide

private theorem nc_apply {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) :
    tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

private theorem nc_diag {R : Type} [CommRing R] (t : Rˣ × Rˣ) (X : M4 R) (i : Fin 4) : tconj t X i i = X i i := by
  rw [nc_apply, nc_wt_self]; simp [wv]

private theorem nc_smul {R : Type} [CommRing R] (t : Rˣ × Rˣ) (c : R) (X : M4 R) : tconj t (c • X) = c • tconj t X := by
  ext i j
  simp only [nc_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearConj :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} (t : Rˣ × Rˣ), Φ.Near a 0 D → ∃ D' : RD Φ R, Φ.Near a 0 D' ∧ (∀ g, D'.r g = tconj t (D.r g)) ∧ D'.ψ = D.ψ := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ D t h
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -, -⟩ := grp R
  let r' : Γ →* M4 R :=
    { toFun := fun g => tconj t (D.r g)
      map_one' := by rw [map_one, hone]
      map_mul' := fun g k => by rw [map_mul, hmul] }
  have hr : ∀ g, r' g = tconj t (D.r g) := fun _ => rfl
  refine ⟨⟨r', D.ψ⟩, ⟨⟨fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩, fun i j N => ?_, h.contψ, fun g i => ?_,
    fun g i j hij hτ => ?_, h.redψ⟩, hr, rfl⟩
  · have := h.rep.mult g
    unfold IsGSp at *
    show adj (tconj t (D.r g)) * tconj t (D.r g) = _
    rw [hadj, ← hmul, this, nc_smul, hone]
  · show tconj t (D.r g) = 1
    rw [h.rep.kill g hg, hone]
  · show tconj t (D.r Φ.g0) i j = 0
    rw [nc_apply, h.rep.nrm hij, mul_zero]
  · exact (h.cont i j N).comp fun x => Ideal.Quotient.mk _ (wv t (wt i j) : R) * x
  · show res Λ R (tconj t (D.r g) i i) = _
    rw [nc_diag, h.diag]
  · show tconj t (D.r g) i j ∈ _
    rw [nc_apply]
    exact Ideal.mul_mem_left _ _ (h.off g i j hij hτ)
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem char_eq_wv {R : Type} [CommRing R] (t : Multiplicative (ℤ × ℤ) →* Rˣ) (w : ℤ × ℤ) :
    t (Multiplicative.ofAdd w) = wv (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) w := by
  have h : w = w.1 • ((1, 0) : ℤ × ℤ) + w.2 • ((0, 1) : ℤ × ℤ) := by ext <;> simp
  conv_lhs => rw [h]
  rw [ofAdd_add, map_mul, ofAdd_zsmul, ofAdd_zsmul, map_zpow, map_zpow]
  rfl

private theorem const_mem {Λ X R : Type} [CommRing Λ] [AddCommGroup X] [CommRing R] [Algebra Λ R] (W : WPres Λ X R)
    (c : Λ) : algebraMap Λ R c ∈ W.part 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ c (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)

private theorem sub_mem_max {Λ R : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {x : R} {c : Λ} (h : res Λ R x = residue Λ c) : x - algebraMap Λ R c ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff Λ, map_sub, AlgHom.commutes, h]
  exact sub_self _

theorem UpperTheory.V.Ws.sxGradD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R}, Φ.RUniv a D → ∃ W : WPres Λ (ℤ × ℤ) R, D.Graded W := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D hD
  obtain ⟨hN, hU⟩ := hD
  let c : Γ → Fin 4 → Fin 4 → Λ := fun g i j => if i = j then a (Φ.χ i g) else 0
  let S : Type := (Γ × Fin 4 × Fin 4) ⊕ (Σ v : Φ.ι, Fin 4 × Φ.Gv v)
  let e : S → R := Sum.elim (fun x => D.r x.1 x.2.1 x.2.2 - algebraMap Λ R (c x.1 x.2.1 x.2.2))
    (fun x => D.ψ x.1 x.2.1 x.2.2 - algebraMap Λ R (a (Φ.χ x.2.1 x.2.2)))
  let w : S → ℤ × ℤ := Sum.elim (fun x => wt x.2.1 x.2.2) (fun _ => 0)
  have hc : ∀ g i j, i ≠ j → c g i j = 0 := fun g i j h => if_neg h
  refine (coord_grading Λ (ℤ × ℤ) R S e w ?_ ?_ ?_).elim fun W ⟨u, hu, hW⟩ => ?_
  rotate_right
  · refine ⟨W, fun s => ?_, fun g i j => ?_, fun v i s => ?_, fun s => ?_⟩
    · rw [(hu s).1]
      rcases u s with ⟨g, i, j⟩ | ⟨v, i, t⟩
      · show D.r g i j - algebraMap Λ R (c g i j) ∈ _
        by_cases h : i = j
        · subst h
          exact sub_mem_max ((hN.diag g i).trans (by simp [c]))
        · rw [hc g i j h, map_zero, sub_zero]
          exact hN.off g i j h le_rfl
      · exact sub_mem_max (hN.redψ v i t)
    · have h1 : D.r g i j - algebraMap Λ R (c g i j) ∈ W.part (wt i j) := hW (Sum.inl (g, i, j))
      by_cases h : i = j
      · rw [(wt_eq_zero i j).2 h] at h1 ⊢
        simpa using add_mem h1 (const_mem W (c g i j))
      · rwa [hc g i j h, map_zero, sub_zero] at h1
    · have h1 : D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)) ∈ W.part 0 := hW (Sum.inr ⟨v, i, s⟩)
      simpa using add_mem h1 (const_mem W (a (Φ.χ i s)))
    · rw [(hu s).1, (hu s).2]
      rcases u s with ⟨g, i, j⟩ | ⟨v, i, t⟩
      · exact Or.inl ⟨g, i, j, c g i j, rfl, rfl, hc g i j⟩
      · exact Or.inr ⟨v, i, t, _, rfl, rfl⟩
  · rintro (⟨g, i, j⟩ | ⟨v, i, t⟩)
    · show D.r g i j - algebraMap Λ R (c g i j) ∈ _
      by_cases h : i = j
      · subst h
        exact sub_mem_max ((hN.diag g i).trans (by simp [c]))
      · rw [hc g i j h, map_zero, sub_zero]
        exact hN.off g i j h le_rfl
    · exact sub_mem_max (hN.redψ v i t)
  · intro R' _ _ _ f f' h
    refine (hU R' (D.map (f' : R →+* R')) (sxNearMap f' hN)).unique ?_ rfl
    refine RD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => ?_) (funext fun v => funext fun i => MonoidHom.ext fun s => ?_)
    · have h1 : f (D.r g i j - algebraMap Λ R (c g i j)) = f' (D.r g i j - algebraMap Λ R (c g i j)) :=
        h (Sum.inl (g, i, j))
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at h1
      exact h1
    · have h1 : f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) = f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) :=
        h (Sum.inr ⟨v, i, s⟩)
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at h1
      exact h1
  · intro R' _ _ _ f t _
    obtain ⟨D', hD', hr, hψ⟩ := sxNearConj (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1)))
      (sxNearMap f hN)
    obtain ⟨f', hf', -⟩ := hU R' D' hD'
    refine ⟨f', ?_⟩
    rintro (⟨g, i, j⟩ | ⟨v, i, s⟩)
    · show f' (D.r g i j - algebraMap Λ R (c g i j)) =
        t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j - algebraMap Λ R (c g i j))
      have h1 : f' (D.r g i j) = t (Multiplicative.ofAdd (wt i j)) * f (D.r g i j) := by
        have h2 : f' (D.r g i j) = D'.r g i j := by rw [← hf']; rfl
        rw [h2, hr, char_eq_wv t (wt i j)]
        rfl
      by_cases h : i = j
      · rw [(wt_eq_zero i j).2 h] at h1 ⊢
        rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
        simp
      · rw [hc g i j h, map_zero, sub_zero, h1]
    · show f' (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s))) =
        t (Multiplicative.ofAdd 0) * f (D.ψ v i s - algebraMap Λ R (a (Φ.χ i s)))
      have h1 : f' (D.ψ v i s) = f (D.ψ v i s) := by
        have h2 : f' (D.ψ v i s) = D'.ψ v i s := by rw [← hf']; rfl
        rw [h2, hψ]
        rfl
      rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, h1]
      simp
end
