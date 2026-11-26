module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Diag

variable {R : Type} [CommRing R]

private theorem prj_diag (c : Fin 4 → R) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.diagonal fun a => ∏ j ∈ Finset.univ.erase i, (c a - c j) := by
  unfold prj
  have h : Matrix.diagonal c = Matrix.diagonalAlgHom (n := Fin 4) (α := R) R c := rfl
  rw [h, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext a
  simp [map_prod, Finset.prod_apply, Pi.algebraMap_apply]

private theorem prj_zero (c : Fin 4 → R) {i a : Fin 4} (h : a ≠ i) :
    ∏ j ∈ Finset.univ.erase i, (c a - c j) = 0 :=
  Finset.prod_eq_zero (i := a) (by simp [h]) (sub_self _)

private theorem ord_diag {H : Type} [Group H] (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R)
    (hr : ∀ g, r g = Matrix.diagonal fun i => ps i g) : Ord I ps s₀ r := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, Matrix.charpoly_diagonal]
  · intro g i j hij
    rw [hr s₀, hr g, prj_diag, prj_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_zero]
    congr 1
    funext a
    by_cases h : a = i
    · rw [prj_zero (fun a => ps a s₀) (i := j) (a := a) (by rw [h]; exact hij.ne), zero_mul, zero_mul]
    · rw [prj_zero (fun a => ps a s₀) h, mul_zero]
  · intro s _ i
    rw [hr s₀, hr s, prj_diag, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext a
    by_cases h : a = i
    · rw [h, sub_self, mul_zero, zero_mul]
    · rw [prj_zero (fun a => ps a s₀) h, mul_zero]

private theorem gsp_diag (d : Fin 4 → R) (ν : R) (h : ∀ i, d i * d i.rev = ν) : IsGSp ν (Matrix.diagonal d) := by
  have hs : ∀ i, sgn i * sgn i = 1 := by decide
  have ha : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
    ext i j
    rw [adj_apply]
    by_cases hij : i = j
    · subst hij
      simp [hs]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (fun e => hij (Fin.rev_injective e).symm), smul_zero]
  unfold IsGSp
  rw [ha, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [mul_comm, h]

private theorem res_self (O : Type) [CommRing O] [IsLocalRing O] [IsCO O O] (x : O) : res O O x = residue O x :=
  (res O O).commutes x

private theorem onComp_self {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsCO O O] {Γ ι : Type} [Group Γ]
    [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} (P : Cond O rbar)
    (ρ : Lift O rbar O) (h : P O ρ) : OnComp P ρ.hom ρ :=
  ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ρ, h, ⟨AlgHom.id O O, fun _ _ _ => rfl⟩,
    AlgHom.id O O, Lift.ext (MonoidHom.ext fun _ => Matrix.ext fun _ _ => rfl)⟩

end Diag

theorem UpperTheory.V.GradeZeroInterpolatingElement.r0pt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∃ ρ : Lift c.O D.rbar c.O, ρ.hom = D.r0 ∧ D.IsPt ρ := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, -, hunr, -, hP, hrev, -, -, -, -, hcont, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hr : ∀ g, D.r0 g = Matrix.diagonal fun i => (D.ps i g : c.O) := fun _ => rfl
  have hoff : ∀ g i j, i ≠ j → D.r0 g i j = 0 := fun g i j h => by rw [hr, Matrix.diagonal_apply_ne _ h]
  have hmult : D.Mult D.r0 := fun g => by
    rw [hr]
    refine gsp_diag _ _ fun i => ?_
    rw [← hrev i]
    rfl
  have hone : ∀ g, (∀ i, D.ps i g = 1) → D.r0 g = 1 := fun g h => by
    rw [hr, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [h i]
    rfl
  let ρ : Lift c.O D.rbar c.O :=
    { hom := D.r0
      cont := fun a b => by
        by_cases h : a = b
        · subst h
          simpa only [hr, Matrix.diagonal_apply_eq] using hcont a
        · intro N
          simp only [hoff _ _ _ h]
          exact IsLocallyConstant.const _
      red := fun g a b => res_self _ _ }
  refine ⟨ρ, rfl, hmult, fun A hA g hg h1 => hone g fun i => hunr i A hA g hg h1, ⟨fun i j h => hoff _ _ _ ?_, ?_, ?_⟩,
    onComp_self _ (D.loc ρ l) ⟨fun g => hmult g, ord_diag _ _ _ _ fun g => hr g⟩,
    fun p hp => onComp_self _ (D.loc ρ p) ⟨fun g => hmult g, fun g hg => hone g fun i => ?_⟩⟩
  · rintro rfl
    exact h rfl
  · show D.r0 _ 0 2 + _ * D.r0 _ 0 2 = 0
    rw [hoff _ _ _ (by decide), hoff _ _ _ (by decide), mul_zero, add_zero]
  · show D.r0 _ 2 0 + _ * D.r0 _ 2 0 = 0
    rw [hoff _ _ _ (by decide), hoff _ _ _ (by decide), mul_zero, add_zero]
  · obtain ⟨h1, h2, h3⟩ := hP p hp g hg.1
    have h4 : D.ψ g = 1 := hg.2
    fin_cases i
    · exact h3.trans h4
    · exact h2.trans h4
    · exact h1
    · rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EiiUnit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem eii_step {R : Type} [CommRing R] (A : Submodule R (M4 R)) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)
    (y0 y1 y2 y3 : R) (hY : (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) ∈ A)
    (hu : IsUnit (y0 * y3 - y1 * y2)) : (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
  have key : (y0 * y3 - y1 * y2) • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) =
      (y0 + y3) • (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) -
        (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) *
          (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  have hm : (y0 * y3 - y1 * y2) • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
    rw [key]
    exact A.sub_mem (A.smul_mem _ hY) (hmul _ hY _ hY)
  obtain ⟨u, hu⟩ := hu
  have hs := A.smul_mem (↑u⁻¹ : R) hm
  rwa [← hu, smul_smul, Units.inv_mul, one_smul] at hs

private theorem eii_alg {R : Type} [CommRing R] (A : Submodule R (M4 R)) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)
    (hone : (1 : M4 R) ∈ A) (hadj : ∀ x ∈ A, adj x ∈ A) (X : M4 R) (hX : X ∈ A) (hb : IsBlock X)
    (hu : IsUnit ((X 0 0 * X 0 0 + X 0 2 * X 2 0 - (X 1 1 + X 3 3) * X 0 0 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) *
      (X 2 0 * X 0 2 + X 2 2 * X 2 2 - (X 1 1 + X 3 3) * X 2 2 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) -
      (X 0 0 * X 0 2 + X 0 2 * X 2 2 - (X 1 1 + X 3 3) * X 0 2) * (X 2 0 * X 0 0 + X 2 2 * X 2 0 - (X 1 1 + X 3 3) * X 2 0)))
    (H : M4 R) (hH : H ∈ A) (h02 : H 0 2 = 0) (h20 : H 2 0 = 0) (hd : IsUnit (H 0 0 - H 2 2)) (i : Fin 4) :
    Matrix.single i i (1 : R) ∈ A := by
  have z : ∀ a b, lamW a ≠ lamW b → X a b = 0 := hb
  have x01 := z 0 1 (by simp [lamW])
  have x03 := z 0 3 (by simp [lamW])
  have x10 := z 1 0 (by simp [lamW])
  have x12 := z 1 2 (by simp [lamW])
  have x21 := z 2 1 (by simp [lamW])
  have x23 := z 2 3 (by simp [lamW])
  have x30 := z 3 0 (by simp [lamW])
  have x32 := z 3 2 (by simp [lamW])
  have hYA : X * X - (X 1 1 + X 3 3) • X + (X 1 1 * X 3 3 - X 1 3 * X 3 1) • (1 : M4 R) ∈ A :=
    A.add_mem (A.sub_mem (hmul X hX X hX) (A.smul_mem _ hX)) (A.smul_mem _ hone)
  have hE : (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
    refine eii_step A hmul
      (X 0 0 * X 0 0 + X 0 2 * X 2 0 - (X 1 1 + X 3 3) * X 0 0 + (X 1 1 * X 3 3 - X 1 3 * X 3 1))
      (X 0 0 * X 0 2 + X 0 2 * X 2 2 - (X 1 1 + X 3 3) * X 0 2)
      (X 2 0 * X 0 0 + X 2 2 * X 2 0 - (X 1 1 + X 3 3) * X 2 0)
      (X 2 0 * X 0 2 + X 2 2 * X 2 2 - (X 1 1 + X 3 3) * X 2 2 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) ?_ hu
    convert hYA using 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, x01, x03, x10, x12, x21, x23, x30, x32] <;>
      ring
  have hZ : (H 0 0 - H 2 2) • Matrix.single 0 0 (1 : R) =
      (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) * H *
          (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) -
        H 2 2 • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases a <;> fin_cases b <;> simp [Matrix.single, h02, h20]
  have h0m : (H 0 0 - H 2 2) • Matrix.single 0 0 (1 : R) ∈ A := by
    rw [hZ]
    exact A.sub_mem (hmul _ (hmul _ hE _ hH) _ hE) (A.smul_mem _ hE)
  have e0 : Matrix.single 0 0 (1 : R) ∈ A := by
    obtain ⟨u, hu'⟩ := hd
    have hs := A.smul_mem (↑u⁻¹ : R) h0m
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at hs
  have e2 : Matrix.single 2 2 (1 : R) ∈ A := by
    have h : Matrix.single 2 2 (1 : R) =
        (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) - Matrix.single 0 0 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    rw [h]
    exact A.sub_mem hE e0
  have hadjs : ∀ k : Fin 4, adj (Matrix.single k k (1 : R)) = Matrix.single k.rev k.rev 1 := by
    intro k
    ext a b
    fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [adj_apply, Matrix.single, sgn, Fin.rev]
  fin_cases i
  · exact e0
  · have h := hadj _ e2
    rwa [hadjs] at h
  · exact e2
  · have h := hadj _ e0
    rwa [hadjs] at h

private theorem eii_span {R H : Type} [CommRing R] [Group H] (r : H →* M4 R) (ν : H → R) (hν : ∀ g, IsGSp (ν g) (r g)) :
    (∀ x ∈ Submodule.span R (Set.range r), ∀ y ∈ Submodule.span R (Set.range r), x * y ∈ Submodule.span R (Set.range r)) ∧
      ∀ x ∈ Submodule.span R (Set.range r), adj x ∈ Submodule.span R (Set.range r) := by
  have hadj : ∀ g, adj (r g) = ν g • r g⁻¹ := by
    intro g
    have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : adj (r g) * r g * r g⁻¹ = ν g • 1 * r g⁻¹ := by rw [hν g]
    rw [mul_assoc, hinv, mul_one, smul_mul_assoc, one_mul] at h0
    exact h0
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨a, ⟨g, rfl⟩, b, ⟨k, rfl⟩, rfl⟩
    exact ⟨g * k, map_mul r g k⟩
  · let L : M4 R →ₗ[R] M4 R :=
      { toFun := adj
        map_add' := fun x y => by
          ext i j
          simp only [adj_apply, Matrix.add_apply, smul_add]
        map_smul' := fun c x => by
          ext i j
          simp only [adj_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, zsmul_eq_mul]
          ring }
    have hle : Submodule.span R (Set.range r) ≤ (Submodule.span R (Set.range r)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      show adj (r g) ∈ Submodule.span R (Set.range r)
      rw [hadj g]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
    exact hle hx

private theorem eii_unit {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (x : R)
    (h : res O R x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h ((res_eq_zero_iff O R x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx))

private theorem eii_abs {O R H : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Group H]
    (r : H →* M4 R) (ps : Fin 4 → H →* Oˣ) (ν : H → R) (hν : ∀ g, IsGSp (ν g) (r g))
    (hr : ∀ g i j, res O R (r g i j) = residue O (diagRep ps g i j)) (φ g : H) (hb : IsBlock (r φ))
    (hφ : ∀ i j, lamW i ≠ lamW j → residue O (ps i φ) ≠ residue O (ps j φ))
    (h0 : ps 0 g = ps 2 g * ps 1 g) (h1 : residue O (ps 1 g) ≠ 1) (h2 : residue O (ps 2 g) ≠ 1)
    (h02 : (r g + algebraMap O R (ps 0 g) • r g⁻¹) 0 2 = 0) (h20 : (r g + algebraMap O R (ps 0 g) • r g⁻¹) 2 0 = 0)
    (i : Fin 4) : Matrix.single i i (1 : R) ∈ Submodule.span R (Set.range r) := by
  obtain ⟨hmul, hadj⟩ := eii_span r ν hν
  have hone : (1 : M4 R) ∈ Submodule.span R (Set.range r) := Submodule.subset_span ⟨1, map_one r⟩
  have hdiag : ∀ k i, res O R (r k i i) = residue O (ps i k : O) := by
    intro k i
    rw [hr]
    simp [diagRep]
  have hoff : ∀ k i j, i ≠ j → res O R (r k i j) = 0 := by
    intro k i j h
    rw [hr]
    simp [diagRep, Matrix.diagonal_apply_ne _ h]
  have hHm : r g + algebraMap O R (ps 0 g) • r g⁻¹ ∈ Submodule.span R (Set.range r) :=
    Submodule.add_mem _ (Submodule.subset_span ⟨g, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩))
  refine eii_alg _ hmul hone hadj (r φ) (Submodule.subset_span ⟨φ, rfl⟩) hb ?_ _ hHm h02 h20 ?_ i
  · apply eii_unit (O := O)
    simp only [map_mul, map_add (f := _), map_sub, hdiag, hoff φ 0 2 (by decide), hoff φ 2 0 (by decide),
      hoff φ 1 3 (by decide), hoff φ 3 1 (by decide)]
    have n01 := sub_ne_zero.2 (hφ 0 1 (by simp [lamW]))
    have n03 := sub_ne_zero.2 (hφ 0 3 (by simp [lamW]))
    have n21 := sub_ne_zero.2 (hφ 2 1 (by simp [lamW]))
    have n23 := sub_ne_zero.2 (hφ 2 3 (by simp [lamW]))
    intro h
    apply mul_ne_zero (mul_ne_zero n01 n03) (mul_ne_zero n21 n23)
    linear_combination h
  · apply eii_unit (O := O)
    have hc : res O R (algebraMap O R (ps 0 g : O)) = residue O (ps 0 g : O) := by
      rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq]
    have hi : ∀ k, residue O (ps k g⁻¹ : O) * residue O (ps k g : O) = 1 := by
      intro k
      rw [← map_mul (residue O), ← Units.val_mul, ← map_mul (ps k), inv_mul_cancel, map_one,
        Units.val_one, map_one]
    have e0 : residue O (ps 0 g : O) = residue O (ps 2 g : O) * residue O (ps 1 g : O) := by
      rw [h0, Units.val_mul, map_mul]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_add (f := _), map_mul, hc, hdiag]
    intro h
    have hp : (residue O (ps 1 g : O) - 1) * (residue O (ps 2 g : O) - 1) = 0 := by
      linear_combination h - e0 * (1 - residue O (ps 2 g⁻¹ : O)) - hi 0 + residue O (ps 1 g : O) * hi 2
    rcases mul_eq_zero.1 hp with h' | h'
    · exact h1 (sub_eq_zero.1 h')
    · exact h2 (sub_eq_zero.1 h')

theorem UpperTheory.V.GradeZeroInterpolatingElement.eii :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), D.Mult ρ.hom → D.Nrm ρ.hom → ∀ i, Matrix.single i i (1 : R) ∈ Submodule.span R (Set.range ρ.hom) := by
  intro Ω _ _ _ l _ c D hG R _ _ _ ρ hM hN i
  obtain ⟨-, hT, -, -, -, -, -, -, -, hph, -⟩ := facts D hG
  have hrb : ∀ k j, D.rbar k j j = residue c.O (D.ps j k : c.O) := by
    intro k j
    simp [Raw.rbar, mapRep, Raw.r0, diagRep]
  refine eii_abs ρ.hom D.ps (fun g => algebraMap c.O R (D.th g : c.O)) hM ?_ D.ph D.g0 hN.1 ?_ ?_ ?_ ?_
    hN.2.1 hN.2.2 i
  · intro g a b
    rw [ρ.red]
    simp [Raw.rbar, mapRep, Raw.r0]
  · intro a b hab
    rw [← hrb, ← hrb, hph, hrb, hrb]
    exact (hT l (Finset.mem_insert_self _ _)).2.2 a b hab
  · rfl
  · exact hG.genElt_Psi
  · exact hG.genElt_alpha
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocVanP
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem lv_gen (hP : Loc.LocalPublishedTheorems) {v l : ℕ} [Fact v.Prime] [Fact l.Prime] (hvl : v ≠ l) {H : Type} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* Formalism.BasicNotions.Loc.GQ v) (hφ : Topology.IsOpenEmbedding φ)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : H →* kˣ) (hκ : IsOpen (κ.ker : Set H))
    (σ : H) (h1 : κ σ ≠ 1) (h2 : Loc.cycA v l k (φ σ) = 1) (z : H → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  letI : TopologicalSpace k := ⊥
  haveI : DiscreteTopology k := ⟨rfl⟩
  have h1' : (κ σ : k) ≠ 1 := fun h => h1 (Units.ext h)
  have hρ : ∀ g x, Loc.chRep κ g x = (κ g : k) * x := fun _ _ => rfl
  have hlc : IsLocallyConstant κ := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' (κ.ker : Set H),
      hκ.preimage (continuous_const.mul continuous_id), by simp, fun h hh => ?_⟩
    have : κ (g⁻¹ * h) = 1 := hh
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have hca : ContAction (Loc.chRep κ) := by
    unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro y
    exact (hlc.comp fun u : kˣ => (u : k) * y).continuous
  obtain ⟨f1, f2, e1, e2⟩ := Loc.tateFin hP φ hφ k k (Loc.chRep κ) hca
  have z0 : H0 (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm σ
    rw [hρ] at this
    rw [Submodule.mem_bot]
    by_contra h
    exact h1' (mul_right_cancel₀ h (by rw [this, one_mul]))
  have z2 : Loc.H0dual ((Loc.cycA v l k).comp φ) (Loc.chRep κ) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have := hf σ x
    rw [MonoidHom.comp_apply, h2, hρ, ← smul_eq_mul, map_smul, smul_eq_mul, Units.val_one] at this
    by_contra h
    exact h1' (mul_right_cancel₀ h this)
  rw [e2, z0, z2, if_neg hvl, finrank_bot, finrank_bot] at e1
  haveI : Subsingleton (H1 (Loc.chRep κ)) := Module.finrank_zero_iff.1 e1
  have hz1 : z ∈ Z1 (Loc.chRep κ) := ⟨hz.continuous, hc⟩
  have : (Submodule.Quotient.mk ⟨z, hz1⟩ : H1 (Loc.chRep κ)) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at this
  exact this

private theorem lv_dec (hP : Loc.LocalPublishedTheorems) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v l : ℕ} (hv : v.Prime)
    [Fact l.Prime] (hvl : v ≠ l) (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1)
    (k : Type) [Field k] [Finite k] [CharP k l] [Algebra ℤ_[l] k] (κ : Dec (F := ℚ) A →* kˣ)
    (hκ : IsOpen (κ.ker : Set (Dec (F := ℚ) A))) (σ : Dec (F := ℚ) A) (h1 : κ σ ≠ 1)
    (h2 : algebraMap ℤ_[l] k (cycZ ℚ Ω l σ : ℤ_[l]ˣ) = 1) (z : Dec (F := ℚ) A → k) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + (κ g : k) * z h) : ∃ m, ∀ g, z g = (κ g : k) * m - m := by
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨φ, hφ, -, -, -, hcyc, -⟩ := ((Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).2 j).2
  refine lv_gen hP hvl φ hφ k κ hκ σ h1 (Units.ext ?_) z hz hc
  rw [← hcyc l σ] at h2
  exact h2

private theorem lv_red {O k : Type} [CommRing O] [IsLocalRing O] [Field k] (red : O →+* k)
    (hred : ∀ a ∈ maximalIdeal O, red a = 0) (a b : O) : red a = red b ↔ residue O a = residue O b := by
  rw [← sub_eq_zero, ← map_sub, ← sub_eq_zero (a := residue O a), ← map_sub, residue_eq_zero_iff]
  refine ⟨fun h => ?_, hred _⟩
  by_contra hn
  exact ((IsLocalRing.notMem_maximalIdeal.1 hn).map red).ne_zero h

theorem UpperTheory.V.GradeZeroInterpolatingElement.locVanP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ (k : Type) [Field k] [Finite k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ p ∈ D.Sb, ∀ z : D.Gp p → k, IsLocallyConstant z → (∀ g h : D.Gp p, z (g * h) = z g + red (γ g : c.O) * z h) → ∃ m, ∀ g : D.Gp p, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD hP k _ _ red hred γ hγ p hp z hz hc
  obtain ⟨f1, f2, -, -, -, -, -, -, -, -, -, fo, -⟩ := facts D hD
  obtain ⟨hpp, hpl, -, -⟩ := f1 p hp
  obtain ⟨hσ, hom, hne⟩ := f2 p (Finset.mem_insert_of_mem hp)
  have hl : l.Prime := Fact.out
  obtain ⟨i, j, hij, hγ'⟩ : ∃ i j, lamW i ≠ lamW j ∧ ∀ g, γ g * D.ps j g = D.ps i g := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨1, 2, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨0, 3, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨3, 2, by decide, fun g => by simp [Raw.ps]⟩
    · exact ⟨2, 1, by decide, fun g => by simp [Raw.ps, Raw.be]⟩
    · exact ⟨3, 0, by decide, fun g => by simp [Raw.ps]⟩
  have hγr : ∀ g, red (γ g : c.O) * red (D.ps j g : c.O) = red (D.ps i g : c.O) := fun g => by
    rw [← map_mul, ← Units.val_mul, hγ']
  letI : Algebra ℤ_[l] k := (red.comp (algebraMap ℤ_[l] c.O)).toAlgebra
  have hl0 : (l : k) = 0 := by
    have hloc := (dvrFacts l c.O).2.2.1
    have hm : (l : c.O) ∈ maximalIdeal c.O := by
      rw [mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O), isUnit_map_iff]
      exact PadicInt.p_nonunit
    simpa using hred _ hm
  haveI : CharP k l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  let κ : D.Gp p →* kˣ := ((Units.map red.toMonoidHom).comp γ).comp (D.Gp p).subtype
  have hκ : ∀ g : D.Gp p, (κ g : k) = red (γ g : c.O) := fun _ => rfl
  have hker : D.rbar.ker.comap (D.Gp p).subtype ≤ κ.ker := by
    intro g hg
    have hg' : D.rbar g = 1 := hg
    have h1 : ∀ a, red (D.ps a g : c.O) = 1 := fun a => by
      rw [← map_one red, lv_red red hred, map_one]
      have := congrFun (congrFun hg' a) a
      simpa [Raw.rbar, Raw.r0, diagRep] using this
    refine Units.ext ?_
    have := hγr g
    rw [h1, h1, mul_one] at this
    exact this
  refine lv_dec hP hpp hpl (D.pl p) (hD.pl_over p hpp) k κ
    (Subgroup.isOpen_mono hker (fo.preimage continuous_subtype_val)) ⟨D.sg p, hσ⟩ (fun h => ?_) ?_ z hz hc
  · have h' : red (γ (D.sg p) : c.O) = 1 := congrArg Units.val h
    have := hγr (D.sg p)
    rw [h', one_mul, lv_red red hred] at this
    exact hne i j hij this.symm
  · have : red (chiO ℚ Ω l c.O (D.sg p) : c.O) = red 1 := by
      rw [lv_red red hred, map_one]
      exact (hD.om_bar _).symm.trans hom
    rw [map_one] at this
    exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ShaCoc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem kill_of_len {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M]
    [Module O M] (h : Module.length O M ≠ ⊤) : ∃ b : O, b ≠ 0 ∧ ∀ x : M, b • x = 0 := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M p
  have h1 := hn (n + 1) (Nat.le_succ n)
  have h2 : LinearMap.range (p ^ n • LinearMap.id : M →ₗ[O] M) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (IsNoetherian.noetherian _) ?_
      (maximalIdeal_le_jacobson _)
    intro y hy
    rw [h1] at hy
    obtain ⟨x, rfl⟩ := hy
    have : (p ^ (n + 1) • LinearMap.id : M →ₗ[O] M) x = p • (p ^ n • LinearMap.id : M →ₗ[O] M) x := by
      simp [smul_smul, pow_succ']
    rw [this]
    exact Submodule.smul_mem_smul ((mem_maximalIdeal _).2 hp.not_isUnit) ⟨x, rfl⟩
  refine ⟨p ^ n, pow_ne_zero _ hp.ne_zero, fun x => ?_⟩
  have : (p ^ n • LinearMap.id : M →ₗ[O] M) x ∈ (⊥ : Submodule O M) := h2 ▸ ⟨x, rfl⟩
  simpa using this

section Abs

variable {O W Γ : Type} [CommRing O] [AddCommGroup W] [Module O W] [TopologicalSpace W] [DiscreteTopology W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W] [Group Γ] [TopologicalSpace Γ]

private theorem exists_norm (θ : Γ →* Oˣ) (hc : ∀ m : W, Continuous fun g => (θ g : O) • m) (g0 : Γ)
    (hu : IsUnit ((θ g0 : O) - 1)) :
    ∃ N : H1U (Formalism.GaloisCohomology.scalRep W θ) ⊤ →ₗ[O] (Γ → W), Function.Injective N ∧ (∀ x, IsLocallyConstant (N x)) ∧
      (∀ x g h, N x (g * h) = N x g + (θ g : O) • N x h) ∧ (∀ x, N x g0 = 0) ∧
      ∀ (𝒟 : Set (Subgroup Γ)) x, x ∈ LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 → ∀ D ∈ 𝒟, ∃ m : W, ∀ g ∈ D,
        N x g = (θ g : O) • m - m := by
  obtain ⟨u, hu⟩ := hu
  let t : Γ → (⊤ : Subgroup Γ) := fun g => ⟨g, trivial⟩
  let n : Z1U (Formalism.GaloisCohomology.scalRep W θ) ⊤ →ₗ[O] (Γ → W) :=
    { toFun := fun z g => z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0)
      map_add' := fun z z' => by
        funext g
        simp only [Submodule.coe_add, Pi.add_apply, smul_add]
        abel
      map_smul' := fun r z => by
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_sub, RingHom.id_apply, smul_smul]
        congr 2
        ring }
  have hn : ∀ z g, n z g = z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0) := fun _ _ => rfl
  have hker : ∀ z, n z = 0 ↔ ∃ m : W, ∀ g : (⊤ : Subgroup Γ), z.1 g = (θ g : O) • m - m := fun z => by
    constructor
    · intro h
      refine ⟨((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g => ?_⟩
      have := congrFun h g
      rw [hn, Pi.zero_apply, sub_eq_zero, sub_smul, one_smul] at this
      exact this
    · rintro ⟨m, hm⟩
      funext g
      have e : z.1 (t g0) = (u : O) • m := by rw [hm, hu, sub_smul, one_smul]
      rw [hn, e, smul_smul _ _ m, Units.inv_mul, one_smul, hm, sub_smul, one_smul]
      exact sub_self _
  refine ⟨Submodule.liftQ _ n fun z hz => (hker z).2 ((mem_coboundaries1 _ _).1 hz), ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ((hker z).1 hx))
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [IsLocallyConstant.iff_continuous]
    show Continuous (n z)
    have h1 : Continuous fun g => z.1 (t g) := z.2.1.comp (continuous_id.subtype_mk _)
    refine (h1.sub ((hc (((u⁻¹ : Oˣ) : O) • z.1 (t g0))).sub (continuous_const (y := ((u⁻¹ : Oˣ) : O) • z.1 (t g0))))).congr fun g => ?_
    rw [hn, sub_smul, one_smul]
    rfl
  · intro x g h
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show n z _ = n z _ + _ • n z _
    have e : z.1 (t (g * h)) = z.1 (t g) + (θ g : O) • z.1 (t h) := z.2.2 (t g) (t h)
    rw [hn, hn, hn, e, map_mul, Units.val_mul]
    module
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show n z _ = 0
    rw [hn, ← hu, smul_smul, Units.mul_inv, one_smul, sub_self]
  · intro 𝒟 x hx D hD
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := mk_mem_locSel.1 hx D hD
    refine ⟨m - ((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g hg => ?_⟩
    show n z _ = _
    have e : z.1 (t g) = (θ g : O) • m - m := hm (t g) hg
    rw [hn, e]
    module

omit [TopologicalSpace W] [DiscreteTopology W] [IsTopologicalAddGroup W] [ContinuousConstSMul O W] in
private theorem exists_j (a : O) (w : W) (hw : ∀ y : O, y • w = 0 ↔ a ∣ y) (hg : ∀ w' : W, a • w' = 0 → ∃ y : O, w' = y • w) :
    ∃ (ι : (O ⧸ Ideal.span {a}) →ₗ[O] W) (j : W → O ⧸ Ideal.span {a}), Function.Injective ι ∧
      ∀ m, a • m = 0 → ι (j m) = m := by
  let ι : (O ⧸ Ideal.span {a}) →ₗ[O] W := Submodule.liftQ (Ideal.span {a}) (LinearMap.toSpanSingleton O W w)
    fun y hy => (hw y).2 (Ideal.mem_span_singleton.1 hy)
  refine ⟨ι, Function.invFun ι, ?_, fun m hm => Function.invFun_eq ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ((hw y).1 hx))
  · obtain ⟨y, rfl⟩ := hg m hm
    exact ⟨Submodule.Quotient.mk y, rfl⟩

private theorem main_abs [IsDomain O] (θ : Γ →* Oˣ) (hc : ∀ m : W, Continuous fun g => (θ g : O) • m) (g0 : Γ)
    (hu : IsUnit ((θ g0 : O) - 1)) (𝒟 : Set (Subgroup Γ)) (b : O) (hb : b ≠ 0)
    (hk : ∀ x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟, b • x = 0) (T : Finset ℕ) (Gp : ℕ → Subgroup Γ)
    (hG : ∀ v ∈ T, Gp v ∈ 𝒟 ∧ ∃ s ∈ Gp v, θ s ≠ 1)
    (hW : ∀ a : O, a ≠ 0 → ∃ w : W, (∀ y : O, y • w = 0 ↔ a ∣ y) ∧ ∀ w' : W, a • w' = 0 → ∃ y : O, w' = y • w) :
    ∃ a : O, a ≠ 0 ∧ ∃ Z : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 →+ (Γ → O ⧸ Ideal.span {a}), Function.Injective Z ∧
      ∀ x, IsLocallyConstant (Z x) ∧ (∀ g h, Z x (g * h) = Z x g + Ideal.Quotient.mk _ (θ g : O) * Z x h) ∧
        (∀ D ∈ 𝒟, ∀ g ∈ D, θ g = 1 → Z x g = 0) ∧ Z x g0 = 0 ∧
        ∀ v ∈ T, ∃ m : O ⧸ Ideal.span {a}, ∀ g ∈ Gp v, Z x g = Ideal.Quotient.mk _ (θ g : O) * m - m := by
  obtain ⟨N, hi, hl, hco, h0, hloc⟩ := exists_norm θ hc g0 hu
  choose! s hs hs1 using fun v hv => (hG v hv).2
  let a : O := b * ∏ v ∈ T, ((θ (s v) : O) - 1)
  have ha : a ≠ 0 := mul_ne_zero hb (Finset.prod_ne_zero_iff.2 fun v hv h =>
    hs1 v hv (Units.ext (sub_eq_zero.1 h)))
  obtain ⟨w, hw, hg⟩ := hW a ha
  obtain ⟨ι, j, hι, hj⟩ := exists_j a w hw hg
  have hbN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, b • N x g = 0 := fun x g => by
    have h1 : b • (x : H1U (Formalism.GaloisCohomology.scalRep W θ) ⊤) = 0 := congrArg Subtype.val (hk x)
    have h2 := congrFun (map_smul N b x.1) g
    rw [h1, map_zero] at h2
    exact h2.symm
  have haN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, ι (j (N x g)) = N x g := fun x g =>
    hj _ (by
      show (b * _) • _ = _
      rw [mul_comm b, mul_smul, hbN, smul_zero])
  have hmul : ∀ (r : O) (q : O ⧸ Ideal.span {a}), ι (Ideal.Quotient.mk _ r * q) = r • ι q := fun r q =>
    map_smul ι r q
  let Z : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 →+ (Γ → O ⧸ Ideal.span {a}) := AddMonoidHom.mk' (fun x g => j (N x g))
    fun x y => funext fun g => hι (by
      show ι (j (N (x + y).1 g)) = ι (j (N x.1 g) + j (N y.1 g))
      rw [map_add ι, haN, haN, haN, Submodule.coe_add, map_add N, Pi.add_apply])
  have hZ : ∀ x g, ι (Z x g) = N x g := haN
  refine ⟨a, ha, Z, fun x y h => Subtype.ext (hi (funext fun g => by rw [← hZ, ← hZ, h])), fun x =>
    ⟨(hl x).comp j, fun g h => hι ?_, fun D hD g hg h1 => hι ?_, hι ?_, fun v hv => ?_⟩⟩
  · rw [map_add ι, hmul, hZ, hZ, hZ, hco]
  · obtain ⟨m, hm⟩ := hloc 𝒟 x x.2 D hD
    rw [hZ, hm g hg, h1, map_zero, Units.val_one, one_smul, sub_self]
  · rw [hZ, h0, map_zero]
  · obtain ⟨m, hm⟩ := hloc 𝒟 x x.2 _ (hG v hv).1
    have h1 : a • m = 0 := by
      have e : (((θ (s v) : O) - 1)) • m = N x (s v) := by rw [hm _ (hs v hv), sub_smul, one_smul]
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun v => (θ (s v) : O) - 1) hv
      have : a = d * (b * ((θ (s v) : O) - 1)) := by
        show b * _ = _
        rw [hd]; ring
      rw [this, mul_smul, mul_smul, e, hbN, smul_zero]
    refine ⟨j m, fun g hg => hι ?_⟩
    rw [hZ, map_sub, hmul, hj m h1, hm g hg]

end Abs

section Conc

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

private theorem isUnit_inverse_character_sub_one (hD : D.Good) : IsUnit (((D.Psi⁻¹ D.g0 : c.Oˣ) : c.O) - 1) := by
  rw [MonoidHom.inv_apply]
  have h1 : IsUnit (1 - (D.Psi D.g0 : c.O)) := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one]
    exact fun h => hD.genElt_Psi (sub_eq_zero.1 h).symm
  have := (Units.isUnit (D.Psi D.g0)⁻¹).mul h1
  rwa [mul_sub, mul_one, Units.inv_mul] at this

private theorem local_group_in_family_nontrivial (hD : D.Good) (v : ℕ) (hv : v ∈ D.T) :
    D.Gp v ∈ shaFam ℚ Ω (∏ p ∈ D.S, p) ∧ ∃ s ∈ D.Gp v, D.Psi⁻¹ s ≠ 1 := by
  obtain ⟨-, -, -, -, hP, -, hinj, -⟩ := facts D hD
  have hθ1 : ∀ g, D.Psi⁻¹ g = 1 ↔ D.Psi g = 1 := fun g => by rw [MonoidHom.inv_apply, inv_eq_one]
  have hvS : v ∈ D.S := by
    rcases Finset.mem_insert.1 hv with h | h
    · exact h ▸ hD.l_mem
    · classical exact (Finset.mem_filter.1 h).1
  refine ⟨Chr.shaFam_mono (Finset.dvd_prod_of_mem (fun p => p) hvS)
    (Or.inl ⟨D.pl v, hD.pl_over v (hD.S_prime v hvS), rfl⟩), ?_⟩
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]
    refine ⟨D.s0, D.s0.2, fun h => ?_⟩
    have h1 : D.ps 1 D.s0 = D.ps 3 D.s0 := (hθ1 _).1 h
    have h2 : (1 : Fin 4) = 3 := hinj (congrArg Units.val h1)
    exact absurd h2 (by decide)
  · by_contra hne
    have h1 : (D.Ip v).map D.ψ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro s hs
      by_contra h2
      exact hne ⟨s, hs.1, fun h3 => h2 (((hP v h s hs).2.1).symm.trans ((hθ1 _).1 h3))⟩
    have h3 : l ∣ Nat.card ((D.Ip v).map D.ψ) := by classical exact (Finset.mem_filter.1 h).2.2
    rw [h1, Subgroup.card_bot] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

private theorem cont_Psi (hD : D.Good) (m : QO l c.O) : Continuous fun g => ((D.Psi⁻¹ g : c.Oˣ) : c.O) • m := by
  have hθ : D.Psi⁻¹ = D.ψ⁻¹ * chiO ℚ Ω l c.O ^ (-(D.e : ℤ)) := Chr.Psi_inv l D.e D.ψ
  have hker : (D.ψ⁻¹).ker = D.ψ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  have hc := (contTw ℚ Ω l).2.2 c.O D.ψ⁻¹ (-(D.e : ℤ)) (by rw [hker]; exact hD.psi_open)
  rw [← hθ] at hc
  exact (continuous_prod_of_discrete_right.1 hc) m

set_option synthInstance.maxHeartbeats 200000 in
private theorem conc (hD : D.Good) (ρ : Representation c.O (G ℚ Ω) (QO l c.O)) (hρ : ρ = twist₂ l D.Psi⁻¹)
    (hfin : Module.length c.O (ShaU ρ (∏ p ∈ D.S, p) ⊤) ≠ ⊤) :
    ∃ a : c.O, a ≠ 0 ∧ ∃ Z : ShaU ρ (∏ p ∈ D.S, p) ⊤ →+ (G ℚ Ω → c.O ⧸ Ideal.span {a}), Function.Injective Z ∧
      ∀ x, D.ShaCoc a (Z x) := by
  subst hρ
  have hU := (facts D hD).2.2.1 1
  have q1 := (ML.qoCyc l c.O).2.1
  have q2 := (ML.qoCyc l c.O).2.2.1
  have HH := fun b hb hk => main_abs (W := QO l c.O) D.Psi⁻¹ (cont_Psi D hD) D.g0 (isUnit_inverse_character_sub_one D hD)
    (shaFam ℚ Ω (∏ p ∈ D.S, p)) b hb hk D.T D.Gp (local_group_in_family_nontrivial D hD)
    (fun a ha => (q1 a ha).imp fun w hw => ⟨hw, q2 a w ha hw⟩)
  refine (kill_of_len hfin).elim fun b hb => (HH b hb.1 hb.2).imp fun a h => ⟨h.1, h.2.imp fun Z hZ => ⟨hZ.1, fun x => ?_⟩⟩
  have H := hZ.2 x
  refine ⟨H.1, H.2.1, fun A hA g hg hr => H.2.2.1 _ (Or.inr ⟨A, rfl⟩) g hg ?_, H.2.2.2.1, H.2.2.2.2⟩
  rw [MonoidHom.inv_apply, inv_eq_one]
  exact hU A hA g hg hr

end Conc

theorem UpperTheory.V.GradeZeroInterpolatingElement.shaCoc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → SoFin Ω l → D.sha ≠ ⊤ ∧ ∃ a : c.O, a ≠ 0 ∧ ∃ Z : ShaU (Chr.rho l D.e D.ψ) (∏ p ∈ D.S, p) ⊤ →+ (G ℚ Ω → c.O ⧸ Ideal.span {a}), Function.Injective Z ∧ ∀ x, D.ShaCoc a (Z x) := by
  intro Ω _ _ _ l _ c D hD hS
  have hfin : D.sha ≠ ⊤ := ne_top_of_le_ne_top (hS c D.ψ hD.psi_open D.e (le_trans one_le_two hD.two_le))
    (Chr.VS_anti l (Finset.dvd_prod_of_mem (fun p => p) hD.l_mem) D.e D.ψ)
  exact ⟨hfin, conc D hD _ (Chr.rho_eq l D.e D.ψ) hfin⟩
end
