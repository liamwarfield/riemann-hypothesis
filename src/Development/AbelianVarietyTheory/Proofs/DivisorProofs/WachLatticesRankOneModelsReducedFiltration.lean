module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSlotsGlobal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixRangeEq
namespace GlobalTheory.MatrixRangeExistence

theorem exists_matrix_range_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a : Fin n => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O,
      (∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x) ∧ Matrix.det A ≠ 0 := by
  classical
  let f : (Fin n → O) →ₗ[O] N :=
    LinearMap.codRestrict N (ϖ • LinearMap.id) (fun y => hN y)
  have hf : Function.Injective f := by
    intro y z h
    have h' : ϖ • y = ϖ • z := congrArg Subtype.val h
    funext a
    exact mul_left_cancel₀ hϖ (congrFun h' a)
  have h1 : n ≤ Module.finrank O N := by
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  have h2 : Module.finrank O N ≤ n := by
    have := Submodule.finrank_le N
    simpa using this
  let b : Module.Basis (Fin n) O N := Module.finBasisOfFinrankEq O N (le_antisymm h2 h1)
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => (b j : Fin n → O) i
  have hA : ∀ u : Fin n → O, Matrix.mulVec A u = ((∑ j, u j • b j : N) : Fin n → O) := by
    intro u
    funext i
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x := by
    intro x
    constructor
    · intro hx
      refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
      rw [hA, b.sum_repr ⟨x, hx⟩]
    · rintro ⟨u, rfl⟩
      rw [hA]
      exact Subtype.property _
  refine ⟨A, key, ?_⟩
  have hcol : ∀ j : Fin n, ∃ u : Fin n → O,
      Matrix.mulVec A u = fun a => ϖ * (Pi.single j (1 : O) : Fin n → O) a :=
    fun j => (key _).1 (hN _)
  choose U hU using hcol
  have hmul : A * (Matrix.of fun i j => U j i) = ϖ • (1 : Matrix (Fin n) (Fin n) O) := by
    ext i j
    have := congrFun (hU j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Matrix.one_apply, Pi.single_apply]
  intro h0
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hϖ this.symm

end GlobalTheory.MatrixRangeExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformi
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem exists_square_matrix_of_submodule_between
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq
  | (apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixRangeExistence.exists_matrix_range_eq ..)
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformiStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)), ϖ ≠ 0 → (∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) → ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first | exact @GlobalTheory.exists_square_matrix_of_submodule_between | exact GlobalTheory.exists_square_matrix_of_submodule_between | (intros; apply GlobalTheory.exists_square_matrix_of_submodule_between <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLine
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreLine

theorem cancel_left {O : Type} [CommRing O] {a b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => hA ?_
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem cancel_left₂ {O : Type} [CommRing O] {a a' b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    {A' : Matrix (Fin a') (Fin b) O} (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) (h' : A' * X = A' * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  refine sub_eq_zero.mp (hA _ ?_ ?_)
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, sub_self]
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', sub_self]

theorem solve {O : Type} [CommRing O] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) O) (B : Matrix (Fin a) (Fin c) O)
    (h : ∀ v, ∃ w, A *ᵥ w = B *ᵥ v) : ∃ S : Matrix (Fin b) (Fin c) O, B = A * S := by
  choose w hw using h
  refine ⟨Matrix.of fun i j => w (Pi.single j 1) i, Matrix.ext_of_mulVec_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← hw]
  congr 1
  rw [Matrix.mulVec_single_one]
  rfl

theorem mkRep {Γ O : Type} [Group Γ] [CommRing O] {a a' m : ℕ} (A : Matrix (Fin a) (Fin m) O)
    (A' : Matrix (Fin a') (Fin m) O) (ρ : Γ →* GL (Fin a) O) (ρ' : Γ →* GL (Fin a') O)
    (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    (hst : ∀ g v, ∃ w, A *ᵥ w = (ρ g : Matrix (Fin a) (Fin a) O) *ᵥ (A *ᵥ v) ∧
      A' *ᵥ w = (ρ' g : Matrix (Fin a') (Fin a') O) *ᵥ (A' *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin m) O, Tw r' ρ A ∧ Tw r' ρ' A' := by
  choose w hw using hst
  let M : Γ → Matrix (Fin m) (Fin m) O := fun g => Matrix.of fun i j => w g (Pi.single j 1) i
  have hM : ∀ g j, M g *ᵥ Pi.single j 1 = w g (Pi.single j 1) := fun g j => by
    rw [Matrix.mulVec_single_one]
    rfl
  have k1 : ∀ g, A * M g = (ρ g : Matrix (Fin a) (Fin a) O) * A := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).1]
  have k2 : ∀ g, A' * M g = (ρ' g : Matrix (Fin a') (Fin a') O) * A' := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).2]
  let f : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := M
      map_one' := cancel_left₂ hA (by rw [k1, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
        (by rw [k2, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left₂ hA
        (by rw [k1, ← Matrix.mul_assoc, k1, Matrix.mul_assoc, k1, ← Matrix.mul_assoc, map_mul, Units.val_mul])
        (by rw [k2, ← Matrix.mul_assoc, k2, Matrix.mul_assoc, k2, ← Matrix.mul_assoc, map_mul, Units.val_mul]) }
  refine ⟨f.toHomUnits, fun g => ?_, fun g => ?_⟩
  · rw [MonoidHom.coe_toHomUnits]
    exact k1 g
  · rw [MonoidHom.coe_toHomUnits]
    exact k2 g

theorem rank_map {O F : Type} [CommRing O] [Field F] (f : O →+* F) {a b : ℕ} (A : Matrix (Fin a) (Fin b) O)
    (B : Matrix (Fin b) (Fin a) O) (h : A * B = 1) : (A.map f).rank = a ∧ (B.map f).rank = a :=
  rank_of_mul_eq_one _ _ (by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)])

theorem fibre_line : ∀ {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (Ac As : Matrix (Fin n) (Fin n) O) (ρc ρs : Γ →* GL (Fin n) O) (x : Fin n → O), Function.Injective Ac.mulVec → Function.Injective As.mulVec → Tw ρc r Ac → Tw ρs r As → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (∀ g, ∃ u, Ac *ᵥ u = (r g : Matrix (Fin n) (Fin n) O) *ᵥ x - fun a => (χ g : O) * x a) → ∃ (r2 : Γ →* GL (Fin (n + 1)) O) (B B' : Matrix (Fin n) (Fin (n + 1)) O) (C : Matrix (Fin 1) (Fin (n + 1)) O) (E : Matrix (Fin (n + 1)) (Fin n) O), Tw r2 r B ∧ Tw r2 ρs B' ∧ Tw r2 (GlobalTheory.TripleGal.rk1 χ) C ∧ Tw ρc r2 E ∧ B * E = Ac ∧ C * E = 0 ∧ B = As * B' ∧ (E.map (residue O)).rank = n ∧ (C.map (residue O)).rank = 1 ∧ (B'.map (residue O)).rank = n ∧ ∀ v, B *ᵥ v = 0 → C *ᵥ v = 0 → v = 0 := by
  intro Γ O _ _ _ _ n r χ Ac As ρc ρs x hAc hAs htc hts h1 h2 h3 h4
  let B : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (x i) (fun j => Ac i j) j
  let Cm : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ j => Fin.lastCases (1 : O) (fun _ => 0) j
  let E : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i j => if i = j.castSucc then 1 else 0
  let P : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (0 : O) (fun j => if i = j then 1 else 0) j
  let e : Matrix (Fin (n + 1)) (Fin 1) O := Matrix.of fun _ _ => 1
  have hB : ∀ v, B *ᵥ v = Ac *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • x := fun v => by
    funext i
    simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hC : ∀ v, Cm *ᵥ v = fun _ => v (Fin.last n) := fun v => by
    funext i
    simp [Cm, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hBs : ∀ (u : Fin n → O) (c : O), B *ᵥ (Fin.snoc u c : Fin (n + 1) → O) = Ac *ᵥ u + c • x := fun u c => by
    rw [hB]
    simp
  have hBE : B * E = Ac := by
    ext i k
    simp [B, E, Matrix.mul_apply]
  have hCE : Cm * E = 0 := by
    ext i k
    simp [Cm, E, Matrix.mul_apply]
  have hPE : P * E = 1 := by
    ext i k
    simp [P, E, Matrix.mul_apply, Matrix.one_apply]
  have hCe : Cm * e = 1 := by
    ext i k
    rw [Subsingleton.elim i k]
    simp [Cm, e, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hinj : ∀ v, B *ᵥ v = 0 → Cm *ᵥ v = 0 → v = 0 := fun v hb hc => by
    have hl : v (Fin.last n) = 0 := by
      rw [hC] at hc
      exact congrFun hc 0
    rw [hB, hl, zero_smul, add_zero] at hb
    have h0 : (fun j : Fin n => v j.castSucc) = 0 := hAc (by rw [hb, Matrix.mulVec_zero])
    funext j
    refine Fin.lastCases hl (fun j => congrFun h0 j) j
  have hr : ∀ g, (GlobalTheory.TripleGal.rk1 χ g : Matrix (Fin 1) (Fin 1) O) = Matrix.scalar (Fin 1) (χ g : O) := fun _ => rfl
  obtain ⟨r2, hr2B, hr2C⟩ := mkRep B Cm r (GlobalTheory.TripleGal.rk1 χ) hinj (fun g v => by
    obtain ⟨u, hu⟩ := h4 g
    have hu' : (r g : Matrix (Fin n) (Fin n) O) *ᵥ x = Ac *ᵥ u + (χ g : O) • x := by
      rw [hu]
      exact (sub_add_cancel _ _).symm
    refine ⟨Fin.snoc ((ρc g : Matrix (Fin n) (Fin n) O) *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • u)
      ((χ g : O) * v (Fin.last n)), ?_, ?_⟩
    · rw [hBs, hB, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htc g,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hu', smul_add, smul_smul, mul_comm, add_assoc]
    · rw [hC, hC, hr]
      funext i
      simp [Matrix.mulVec_diagonal])
  obtain ⟨B', hB'⟩ := solve As B (fun v => by
    obtain ⟨w0, hw0⟩ := h2
    obtain ⟨w1, hw1⟩ := h3 (fun j => v j.castSucc)
    exact ⟨w1 + v (Fin.last n) • w0, by rw [hB, Matrix.mulVec_add, Matrix.mulVec_smul, hw0, hw1]⟩)
  obtain ⟨S, hS⟩ := solve B' (1 : Matrix (Fin n) (Fin n) O) (fun v => by
    obtain ⟨u, c, huc⟩ := h1 v
    refine ⟨Fin.snoc u c, hAs ?_⟩
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hB', hBs, huc]
    rfl)
  refine ⟨r2, B, B', Cm, E, hr2B, fun g => cancel_left hAs ?_, hr2C, fun g => cancel_left₂ hinj ?_ ?_, hBE, hCE, hB',
    (rank_map _ P E hPE).2, (rank_map _ Cm e hCe).1, (rank_map _ B' S hS.symm).1, hinj⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hB', hr2B g, hts g, Matrix.mul_assoc, ← hB']
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBE, hr2B g, Matrix.mul_assoc, hBE, htc g]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCE, hr2C g, Matrix.mul_assoc, hCE, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.FibreLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFibreProductStableLatticeChainLineStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_fibre_product_stable_lattice_chain_line : ∀ {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (Ac As : Matrix (Fin n) (Fin n) O) (ρc ρs : Γ →* GL (Fin n) O) (x : Fin n → O), Function.Injective Ac.mulVec → Function.Injective As.mulVec → Tw ρc r Ac → Tw ρs r As → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (∀ g, ∃ u, Ac *ᵥ u = (r g : Matrix (Fin n) (Fin n) O) *ᵥ x - fun a => (χ g : O) * x a) → ∃ (r2 : Γ →* GL (Fin (n + 1)) O) (B B' : Matrix (Fin n) (Fin (n + 1)) O) (C : Matrix (Fin 1) (Fin (n + 1)) O) (E : Matrix (Fin (n + 1)) (Fin n) O), Tw r2 r B ∧ Tw r2 ρs B' ∧ Tw r2 (GlobalTheory.TripleGal.rk1 χ) C ∧ Tw ρc r2 E ∧ B * E = Ac ∧ C * E = 0 ∧ B = As * B' ∧ (E.map (residue O)).rank = n ∧ (C.map (residue O)).rank = 1 ∧ (B'.map (residue O)).rank = n ∧ ∀ v, B *ᵥ v = 0 → C *ᵥ v = 0 → v = 0 := by
  first | exact @GlobalTheory.FibreLine.fibre_line | exact GlobalTheory.FibreLine.fibre_line | (intros; apply GlobalTheory.FibreLine.fibre_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVector
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

namespace GlobalTheory

theorem rank_residue_succ_of_adjoin
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O)
    (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O) :
    Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) →
    (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) →
    (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) →
    (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  intro hϖ h1 h2 h3 h4 h5
  set bar := residue O with hbar
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) O) (v : Fin n → O),
      (A.map bar) *ᵥ (bar ∘ v) = bar ∘ (A *ᵥ v) := by
    intro A v; funext i; exact (RingHom.map_mulVec bar A v i).symm
  have hlift : ∀ z : Fin n → ResidueField O, ∃ v : Fin n → O, bar ∘ v = z := by
    intro z
    refine ⟨fun i => (residue_surjective (z i)).choose, ?_⟩
    funext i; exact (residue_surjective (z i)).choose_spec
  set V := LinearMap.range (As.map bar).mulVecLin
  set Wc := LinearMap.range (Ac.map bar).mulVecLin
  set xb : Fin n → ResidueField O := bar ∘ x
  have hV : V = Wc ⊔ Submodule.span (ResidueField O) {xb} := by
    apply le_antisymm
    · rintro v ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := hlift z
      obtain ⟨u, c, hc⟩ := h2 w
      rw [Matrix.mulVecLin_apply, hmap, hc]
      have : bar ∘ (Ac *ᵥ u + fun a => c * x a) = (Ac.map bar) *ᵥ (bar ∘ u) + bar c • xb := by
        rw [hmap]; funext i; simp [xb]
      rw [this]
      exact Submodule.add_mem_sup ⟨bar ∘ u, rfl⟩
        (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    · apply sup_le
      · rintro v ⟨z, rfl⟩
        obtain ⟨u, rfl⟩ := hlift z
        obtain ⟨w, hw⟩ := h4 u
        refine ⟨bar ∘ w, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hmap, hmap, hw]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        obtain ⟨w, hw⟩ := h3
        exact ⟨bar ∘ w, by rw [Matrix.mulVecLin_apply, hmap, hw]⟩
  have hxb : xb ∉ Wc := by
    rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hlift z
    rw [Matrix.mulVecLin_apply, hmap] at hz
    have hmem : ∀ a, (x - Ac *ᵥ u) a ∈ Ideal.span {ϖ} := by
      intro a
      rw [← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
      have := congrFun hz a
      simp only [Function.comp_apply, xb] at this
      rw [Pi.sub_apply, map_sub, ← hbar, this, sub_self]
    choose y hy using fun a => Ideal.mem_span_singleton'.1 (hmem a)
    obtain ⟨u', hu'⟩ := h1 y
    apply h5
    refine ⟨u + u', ?_⟩
    rw [Matrix.mulVec_add, hu']
    funext a
    have := hy a
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply]
    rw [mul_comm, this]; ring
  have hxb0 : xb ≠ 0 := by
    intro h; exact hxb (h ▸ Wc.zero_mem)
  have hinf : Wc ⊓ Submodule.span (ResidueField O) {xb} = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvW, hvs⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvs
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using Wc.smul_mem c⁻¹ hvW) hxb
  have key := Submodule.finrank_sup_add_finrank_inf_eq Wc (Submodule.span (ResidueField O) {xb})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hxb0, ← hV] at key
  show Module.finrank _ V = Module.finrank _ Wc + 1
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVectorStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O), Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) → (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  first | exact @GlobalTheory.rank_residue_succ_of_adjoin | exact GlobalTheory.rank_residue_succ_of_adjoin | (intros; apply GlobalTheory.rank_residue_succ_of_adjoin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixForm
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

namespace GlobalTheory.WachChain

theorem cancel_left {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O)
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin q) (Fin m) O} (h : A * X = A * Y) : X = Y := by
  ext i j
  have h1 := congrArg (fun Z => Z *ᵥ Pi.single j 1) h
  simp only [← Matrix.mulVec_mulVec] at h1
  have h2 := congrFun (hA h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem solve {O ι : Type} [CommRing O] [Fintype ι] {q m : ℕ} (A : Matrix ι (Fin q) O) (Z : Matrix ι (Fin m) O)
    (h : ∀ j, ∃ w, A *ᵥ w = fun i => Z i j) : ∃ Y : Matrix (Fin q) (Fin m) O, A * Y = Z := by
  choose w hw using h
  refine ⟨Matrix.of fun k j => w j k, ?_⟩
  ext i j
  have h1 := congrFun (hw j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1

theorem mkRep {Γ O ι : Type} [Group Γ] [CommRing O] [Fintype ι] [DecidableEq ι] {q : ℕ} (A : Matrix ι (Fin q) O)
    (ρ : Γ →* Matrix ι ι O) (hA : Function.Injective A.mulVec)
    (hst : ∀ g v, ∃ w, A *ᵥ w = ρ g *ᵥ (A *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin q) O, ∀ g, A * (r' g : Matrix (Fin q) (Fin q) O) = ρ g * A := by
  have h1 : ∀ g, ∃ Y : Matrix (Fin q) (Fin q) O, A * Y = ρ g * A := fun g =>
    solve A (ρ g * A) fun j => by
      obtain ⟨w, hw⟩ := hst g (Pi.single j 1)
      refine ⟨w, ?_⟩
      rw [hw, Matrix.mulVec_mulVec]
      funext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  choose Y hY using h1
  let f : Γ →* Matrix (Fin q) (Fin q) O :=
    { toFun := Y
      map_one' := cancel_left A hA (by rw [hY, map_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left A hA (by
        rw [hY, map_mul, Matrix.mul_assoc, ← hY h, ← Matrix.mul_assoc, ← hY g, Matrix.mul_assoc]) }
  exact ⟨f.toHomUnits, fun g => by rw [MonoidHom.coe_toHomUnits]; exact hY g⟩

theorem chain_of_lattices : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  intro Γ O _ _ _ _ n t R r ψ ϖ M rs hϖ hM0 hlast hmono hst hline
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hin : ∀ k (y : Fin n → O), (fun a => ϖ * y a) ∈ M k := fun k y =>
    hmono (Fin.zero_le k) ((hM0 _).2 ⟨y, rfl⟩)
  choose A hA hdet using fun k => GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer n ϖ (M k) hϖ0 (hin k)
  have hinj : ∀ k, Function.Injective (A k).mulVec := fun k u v huv => by
    by_contra hne
    refine hdet k ((Matrix.exists_mulVec_eq_zero_iff).1 ⟨u - v, sub_ne_zero.2 hne, ?_⟩)
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hrep : ∀ k, ∃ ρ : Γ →* GL (Fin n) O, Tw ρ r (A k) := fun k =>
    mkRep (A k) ((Units.coeHom _).comp r) (hinj k)
      (fun g v => (hA k _).1 (hst g k _ ((hA k _).2 ⟨v, rfl⟩)))
  choose ρ hρ using hrep
  have hbb : ∀ k : Fin R, ∃ Y, A k.succ * Y = A k.castSucc := fun k =>
    solve _ _ fun j => (hA k.succ _).1 (hmono (Fin.castSucc_lt_succ (i := k)).le
      ((hA k.castSucc _).2 ⟨Pi.single j 1, by funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]⟩))
  choose bb hbbe using hbb
  choose xs hxs hxn hsup hψ using hline
  have hsW : ∀ s w, ∃ u c', A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u + fun a => c' * xs s a := by
    intro s w
    have hm := (hA (rs s).succ _).2 ⟨w, rfl⟩
    rw [hsup s, Submodule.mem_sup] at hm
    obtain ⟨y, hy, z, hz, hyz⟩ := hm
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨u, rfl⟩ := (hA _ _).1 hy
    exact ⟨u, c', by rw [← hyz]; rfl⟩
  have hxW : ∀ s, ∃ w, A (rs s).succ *ᵥ w = xs s := fun s => (hA _ _).1 (hxs s)
  have hcW : ∀ s u, ∃ w, A (rs s).succ *ᵥ w = A (rs s).castSucc *ᵥ u := fun s u =>
    (hA _ _).1 (hmono Fin.castSucc_lt_succ.le ((hA _ _).2 ⟨u, rfl⟩))
  have hnW : ∀ s, ¬ ∃ u, A (rs s).castSucc *ᵥ u = xs s := fun s h => hxn s ((hA _ _).2 h)
  have hψW : ∀ s g, ∃ u, A (rs s).castSucc *ᵥ u =
      (r g : Matrix (Fin n) (Fin n) O) *ᵥ xs s - fun a => ((ψ s g : Oˣ) : O) * xs s a :=
    fun s g => (hA _ _).1 (hψ s g)
  choose r2 B B' C E hL using fun s => GlobalTheory.T.matrix_fibre_product_stable_lattice_chain_line n r (ψ s) (A (rs s).castSucc) (A (rs s).succ) (ρ _) (ρ _)
    (xs s) (hinj _) (hinj _) (hρ _) (hρ _) (hsW s) (hxW s) (hcW s) (hψW s)
  refine ⟨⟨ρ, A, bb, r2, B, B', C, E⟩, fun k => ((A k).map (residue O)).rank,
    ⟨fun k => ⟨hρ k, hdet k, rfl⟩, fun k => ⟨?_, (hbbe k).symm⟩, fun s => hL s⟩, ?_, ?_,
    fun s => GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector n ϖ _ _ (xs s) hϖ (fun y => (hA _ _).1 (hin _ y)) (hsW s) (hxW s) (hcW s) (hnW s)⟩
  · intro g
    apply cancel_left (A k.succ) (hinj _)
    rw [← Matrix.mul_assoc, hbbe k, hρ k.castSucc g, ← hbbe k, ← Matrix.mul_assoc, ← hρ k.succ g,
      Matrix.mul_assoc]
  · have hz : (A 0).map (residue O) = 0 := by
      ext i j
      obtain ⟨y, hy⟩ := (hM0 _).1 ((hA 0 _).2 ⟨Pi.single j 1, rfl⟩)
      have hij : A 0 i j = ϖ * y i := by
        have h1 := congrFun hy i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
      have hr : residue O ϖ = 0 :=
        (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
      simp [hij, hr]
    simp [hz]
  · obtain ⟨S, hS⟩ := solve (A (Fin.last R)) (1 : Matrix (Fin n) (Fin n) O) fun j =>
      (hA _ _).1 (by rw [hlast]; trivial)
    exact (rank_of_mul_eq_one ((A (Fin.last R)).map (residue O)) (S.map (residue O))
      (by rw [← Matrix.map_mul, hS, Matrix.map_one _ (map_zero _) (map_one _)])).1

end GlobalTheory.WachChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeChainWithLinesMatrixFormStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form : ∀ (Γ O : Type) [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n t R : ℕ) (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), Irreducible ϖ → (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun a => ϖ * y a) → M (Fin.last R) = ⊤ → Monotone M → (∀ g k x, x ∈ M k → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M k) → (∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun a => ((ψ s g : Oˣ) : O) * x a) ∈ M (rs s).castSucc) → ∃ (x : GalMats Γ O n t R) (dim : Fin (R + 1) → ℕ), x.Chain (residue O) r (fun s => GlobalTheory.TripleGal.rk1 (ψ s)) rs dim ∧ dim 0 = 0 ∧ dim (Fin.last R) = n ∧ ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1 := by
  first | exact @GlobalTheory.WachChain.chain_of_lattices | exact GlobalTheory.WachChain.chain_of_lattices | (intros; apply GlobalTheory.WachChain.chain_of_lattices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulVecEqPow
set_option autoImplicit false

noncomputable section

open PowerSeries Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachPlace

section Columns

variable {F : Type} [Field F] {a b c : ℕ}

def vecL (y : Fin a → F⟦X⟧) : Fin a → LaurentSeries F := fun j => algebraMap F⟦X⟧ (LaurentSeries F) (y j)

def linL (A : Mx F⟦X⟧ a b) : (Fin b → LaurentSeries F) →ₗ[LaurentSeries F] (Fin a → LaurentSeries F) :=
  (A.map (algebraMap F⟦X⟧ (LaurentSeries F))).mulVecLin

def colL (A : Mx F⟦X⟧ a b) : Submodule (LaurentSeries F) (Fin a → LaurentSeries F) := LinearMap.range (linL A)

theorem finrank_colL (A : Mx F⟦X⟧ a b) : Module.finrank (LaurentSeries F) (colL A) = lrank A := rfl

theorem linL_vecL (A : Mx F⟦X⟧ a b) (y : Fin b → F⟦X⟧) : linL A (vecL y) = vecL (A.mulVec y) := by
  funext j
  exact (RingHom.map_mulVec (algebraMap F⟦X⟧ (LaurentSeries F)) A y j).symm

theorem linL_mul (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : linL (A * B) = (linL A).comp (linL B) := by
  rw [linL, Matrix.map_mul, Matrix.mulVecLin_mul]
  rfl

theorem vecL_smul (s : F⟦X⟧) (y : Fin a → F⟦X⟧) : vecL (s • y) = algebraMap F⟦X⟧ (LaurentSeries F) s • vecL y := by
  funext j
  simp only [vecL, Pi.smul_apply, smul_eq_mul, map_mul]

theorem vecL_sub (y z : Fin a → F⟦X⟧) : vecL (y - z) = vecL y - vecL z := by
  funext j
  simp only [vecL, Pi.sub_apply, map_sub]

theorem vecL_injective : Function.Injective (vecL : (Fin a → F⟦X⟧) → _) := fun _ _ h =>
  funext fun j => IsFractionRing.injective F⟦X⟧ (LaurentSeries F) (congrFun h j)

theorem colL_mul_le (A : Mx F⟦X⟧ a b) (B : Mx F⟦X⟧ b c) : colL (A * B) ≤ colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_le_range _ _

theorem colL_eq_top {A : Mx F⟦X⟧ a b} (h : lrank A = a) : colL A = ⊤ :=
  Submodule.eq_top_of_finrank_eq (by rw [finrank_colL, h, Module.finrank_fin_fun])

theorem colL_mul_eq (A : Mx F⟦X⟧ a b) {B : Mx F⟦X⟧ b c} (h : lrank B = b) : colL (A * B) = colL A := by
  rw [colL, linL_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (colL_eq_top h)

theorem exists_clear (z : Fin a → LaurentSeries F) :
    ∃ (m : ℕ) (w : Fin a → F⟦X⟧), vecL w = algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) • z := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (X : F⟦X⟧)) z
  obtain ⟨m, hm⟩ := s.2
  choose w hw using hs
  refine ⟨m, w, funext fun j => ?_⟩
  rw [vecL, hw j, ← hm, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem semilin_mem (θ : F⟦X⟧ →+* F⟦X⟧) (hθ : θ X ≠ 0) {M : Mx F⟦X⟧ a a} {M' : Mx F⟦X⟧ b b} {A A' : Mx F⟦X⟧ a b}
    (h : M * A'.map θ = A * M') {y : Fin a → F⟦X⟧} (hy : vecL y ∈ colL A') :
    vecL (M.mulVec fun j => θ (y j)) ∈ colL A := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨m, w, hw⟩ := exists_clear z
  have e1 : A'.mulVec w = (X : F⟦X⟧) ^ m • y := by
    apply vecL_injective
    rw [← linL_vecL, hw, map_smul, hz, vecL_smul]
  have e2 : (A'.map θ).mulVec (fun j => θ (w j)) = θ X ^ m • fun j => θ (y j) := by
    funext j
    have := RingHom.map_mulVec θ A' w j
    rw [e1] at this
    rw [show (fun j => θ (w j)) = θ ∘ w from rfl, ← this]
    simp
  have e3 : θ X ^ m • (M.mulVec fun j => θ (y j)) = A.mulVec (M'.mulVec fun j => θ (w j)) := by
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_smul]
  have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (θ X ^ m) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ hθ)
  rw [← Submodule.smul_mem_iff _ h0, ← vecL_smul, e3, ← linL_vecL]
  exact LinearMap.mem_range_self _ _

theorem ker_eq_colL {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0) (hE : lrank E = a)
    (hC : lrank C = 1) : LinearMap.ker (linL C) = colL E := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← linL_mul, h]
    simp [linL]
  · have := LinearMap.finrank_range_add_finrank_ker (linL C)
    rw [← colL, finrank_colL, hC, Module.finrank_fin_fun] at this
    rw [finrank_colL, hE]
    omega

theorem exists_mulVec_eq_pow {C : Mx F⟦X⟧ 1 a} (hC : lrank C = 1) :
    ∃ (y : Fin a → F⟦X⟧) (m : ℕ), C.mulVec y = fun _ => X ^ m := by
  obtain ⟨z, hz⟩ : (fun _ => 1 : Fin 1 → LaurentSeries F) ∈ colL C := by
    rw [colL_eq_top hC]
    trivial
  obtain ⟨m, w, hw⟩ := exists_clear z
  refine ⟨w, m, vecL_injective ?_⟩
  rw [← linL_vecL, hw, map_smul, hz]
  funext j
  simp [vecL]

theorem line_rel (θ : F⟦X⟧ →+* F⟦X⟧) {M : Mx F⟦X⟧ a a} {M₂ : Mx F⟦X⟧ (a + 1) (a + 1)} {M₁ : Mx F⟦X⟧ 1 1}
    {B B' : Mx F⟦X⟧ a (a + 1)} {C C' : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a}
    (hB : M * B'.map θ = B * M₂) (hC : M₁ * C'.map θ = C * M₂) (h : C * E = 0) (hE : lrank E = a)
    (hC1 : lrank C = 1) {y y' : Fin (a + 1) → F⟦X⟧} {m m' : ℕ} (hy : C.mulVec y = fun _ => X ^ m)
    (hy' : C'.mulVec y' = fun _ => X ^ m') :
    algebraMap F⟦X⟧ (LaurentSeries F) X ^ m • vecL (M.mulVec fun j => θ (B'.mulVec y' j)) -
      (algebraMap F⟦X⟧ (LaurentSeries F) (θ X) ^ m' * algebraMap F⟦X⟧ (LaurentSeries F) (M₁ 0 0)) •
        vecL (B.mulVec y) ∈ colL (B * E) := by
  have e : ∀ {k : ℕ} (A : Mx F⟦X⟧ k (a + 1)), (fun j => θ (A.mulVec y' j)) = (A.map θ).mulVec fun j => θ (y' j) :=
    fun A => funext fun j => RingHom.map_mulVec θ A y' j
  let z : Fin (a + 1) → F⟦X⟧ := (X : F⟦X⟧) ^ m • (M₂.mulVec fun j => θ (y' j)) - (θ X ^ m' * M₁ 0 0) • y
  have hz : C.mulVec z = 0 := by
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hC]
    rw [← Matrix.mulVec_mulVec, ← e, hy, hy']
    funext j
    rw [Subsingleton.elim j 0]
    simp [Matrix.mulVec, dotProduct]
    ring
  have hk : vecL z ∈ colL E := by
    rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, linL_vecL, hz]
    funext j
    simp [vecL]
  obtain ⟨v, hv⟩ := hk
  refine ⟨v, ?_⟩
  rw [linL_mul, LinearMap.comp_apply, hv, linL_vecL]
  simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hB]
  rw [← Matrix.mulVec_mulVec, ← e, vecL_sub, vecL_smul, vecL_smul, map_pow, map_mul, map_pow]

theorem colL_eq_sup {B : Mx F⟦X⟧ a (a + 1)} {C : Mx F⟦X⟧ 1 (a + 1)} {E : Mx F⟦X⟧ (a + 1) a} (h : C * E = 0)
    (hE : lrank E = a) (hC1 : lrank C = 1) {y : Fin (a + 1) → F⟦X⟧} {m : ℕ} (hy : C.mulVec y = fun _ => X ^ m) :
    colL B = colL (B * E) ⊔ Submodule.span (LaurentSeries F) {vecL (B.mulVec y)} := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have h0 : algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F⟦X⟧ (LaurentSeries F))).2 (pow_ne_zero _ X_ne_zero)
    let s : LaurentSeries F := linL C z 0 / algebraMap F⟦X⟧ (LaurentSeries F) (X ^ m)
    have hk : z - s • vecL y ∈ colL E := by
      rw [← ker_eq_colL h hE hC1, LinearMap.mem_ker, map_sub, map_smul, linL_vecL, hy]
      funext j
      rw [Subsingleton.elim j 0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, vecL, div_mul_cancel₀ _ h0, sub_self]
      rfl
    obtain ⟨v, hv⟩ := hk
    have : linL B z = linL (B * E) v + s • vecL (B.mulVec y) := by
      rw [linL_mul, LinearMap.comp_apply, hv, map_sub, map_smul, linL_vecL, sub_add_cancel]
    rw [this]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le (colL_mul_le _ _) ?_
    rw [Submodule.span_singleton_le_iff_mem, ← linL_vecL]
    exact LinearMap.mem_range_self _ _

end Columns

theorem filtration_of_chain {F : Type} [Field F] {ι : Type} (σ : Equiv.Perm ι) {l n t R : ℕ} (hl : 0 < l) (un : F⟦X⟧)
    (P D : ι → Mx F⟦X⟧ n n) (Pψ Dψ : Fin t → ι → Mx F⟦X⟧ 1 1) (rs : Fin t → Fin R) (dim : Fin (R + 1) → ℕ)
    (y : ι → Slot F n t R) (h0 : dim 0 = 0) (hR : dim (Fin.last R) = n)
    (hs : ∀ s, dim (rs s).succ = dim (rs s).castSucc + 1)
    (hy : ∀ i, (y i).Chain (y (σ i)) l un (P i) (D i) (fun s => Pψ s i) (fun s => Dψ s i) rs dim) :
    ∃ (V : ι → Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
      (e : ι → Fin t → Fin n → F⟦X⟧) (m : ι → Fin t → ℤ),
      (∀ i, V i 0 = ⊥ ∧ V i (Fin.last R) = ⊤ ∧ Monotone (V i)) ∧
      (∀ k i j, Module.finrank (LaurentSeries F) (V i k) = Module.finrank (LaurentSeries F) (V j k)) ∧
      (∀ i k v, vecL v ∈ V (σ i) k → vecL ((P i).mulVec fun a => frob0 l (v a)) ∈ V i k) ∧
      (∀ i k v, vecL v ∈ V i k → vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (v a)) ∈ V i k) ∧
      (∀ i s, vecL (e i s) ∉ V i (rs s).castSucc ∧
        V i (rs s).succ = V i (rs s).castSucc ⊔ Submodule.span (LaurentSeries F) {vecL (e i s)}) ∧
      (∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) • vecL ((P i).mulVec fun a => frob0 l (e (σ i) s a)) -
        (((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * m (σ i) s) * ((Pψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) •
          vecL (e i s) ∈ V i (rs s).castSucc) ∧
      ∀ i s, (((X : F⟦X⟧) : LaurentSeries F) ^ m i s) •
          vecL ((1 + (X : F⟦X⟧) • D i).mulVec fun a => gam0 0 un (e i s a)) -
        (((gamSer 0 un : F⟦X⟧) : LaurentSeries F) ^ m i s *
          ((1 + X * Dψ s i 0 0 : F⟦X⟧) : LaurentSeries F)) • vecL (e i s) ∈ V i (rs s).castSucc := by
  have h1 : HasSubst (X ^ l : F⟦X⟧) := HasSubst.X_pow hl.ne'
  have h2 : HasSubst (gamSer 0 un) := HasSubst.of_constantCoeff_zero' (by simp [gamSer])
  obtain ⟨φ, hφ⟩ : ∃ φ : F⟦X⟧ →+* F⟦X⟧, ⇑φ = frob0 l := ⟨(substAlgHom h1 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h1⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : F⟦X⟧ →+* F⟦X⟧, ⇑γ = gam0 0 un := ⟨(substAlgHom h2 : F⟦X⟧ →ₐ[F] F⟦X⟧), coe_substAlgHom h2⟩
  have hφX : φ X = X ^ l := by rw [hφ, frob0, subst_X h1]
  have hγX : γ X = gamSer 0 un := by rw [hγ, gam0, subst_X h2]
  have hγ0 : γ X ≠ 0 := by
    rw [hγX, gamSer]
    refine mul_ne_zero X_ne_zero fun h => ?_
    simpa using congrArg constantCoeff h
  choose w m hw using fun i s => exists_mulVec_eq_pow ((hy i).2.2 s).2.2.2.2.2.2.1
  have hsup : ∀ i s, colL ((y i).A (rs s).succ) =
      colL ((y i).A (rs s).castSucc) ⊔ Submodule.span (LaurentSeries F) {vecL (((y i).B s).mulVec (w i s))} := by
    intro i s
    obtain ⟨-, -, e1, e2, e3, e4, e5, e6⟩ := (hy i).2.2 s
    rw [← e1, ← colL_eq_sup e2 e4 e5 (hw i s), e3, colL_mul_eq _ e6]
  refine ⟨fun i k => colL ((y i).A k), fun i s => ((y i).B s).mulVec (w i s), fun i s => m i s,
    fun i => ⟨?_, colL_eq_top (((hy i).1 _).2.trans hR), ?_⟩, fun k i j => ?_, fun i k v hv => ?_, fun i k v hv => ?_,
    fun i s => ⟨fun hm => ?_, hsup i s⟩, fun i s => ?_, fun i s => ?_⟩
  · exact Submodule.finrank_eq_zero.1 ((finrank_colL _).trans (((hy i).1 _).2.trans h0))
  · refine Fin.monotone_iff_le_succ.2 fun k => ?_
    exact (congrArg colL ((hy i).2.1 k)).trans_le (colL_mul_le _ _)
  · rw [finrank_colL, finrank_colL, ((hy i).1 k).2, ((hy j).1 k).2]
  · rw [← hφ]
    exact semilin_mem φ (by rw [hφX]; exact pow_ne_zero _ X_ne_zero) (hφ ▸ ((hy i).1 k).1.1) hv
  · rw [← hγ]
    exact semilin_mem γ hγ0 (hγ ▸ ((hy i).1 k).1.2) hv
  · have e := hsup i s
    rw [sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 hm)] at e
    have e' := finrank_colL ((y i).A (rs s).succ)
    rw [e, finrank_colL, ((hy i).1 _).2, ((hy i).1 _).2, hs] at e'
    omega
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel φ (hφ ▸ b1.1) (hφ ▸ c1.1) e2 e4 e5 (hw i s) (hw (σ i) s)
    rw [e1, hφX, hφ, map_pow, ← pow_mul] at this
    rw [← Nat.cast_mul, zpow_natCast, zpow_natCast]
    exact this
  · obtain ⟨b1, c1, e1, e2, -, e4, e5, -⟩ := (hy i).2.2 s
    have := line_rel γ (hγ ▸ b1.2) (hγ ▸ c1.2) e2 e4 e5 (hw i s) (hw i s)
    rw [e1, hγX, hγ, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul] at this
    rw [zpow_natCast, zpow_natCast]
    exact this

end GlobalTheory.WachPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansions
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachExp

theorem exists_locExp_expAt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  intro l _ LL _ hex
  obtain ⟨ζL, hζL⟩ := hex
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin := LL.2
  have hint : IsIntegral ℤ_[l] ζL := IsIntegral.of_pow hl (by rw [hζL.pow_eq_one]; exact isIntegral_one)
  let ζ : ↥(OL LL) := ⟨ζL, hint⟩
  have hζ : IsPrimitiveRoot ζ l :=
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζL Subtype.val_injective

  have hu : IsUnit (1 + (l : ℤ_[l]) * 1) := by
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
    rcases h with h | h
    · exact absurd ((IsUnit.neg_iff _).1 h) PadicInt.prime_p.not_isUnit
    · simpa [sub_eq_add_neg] using h
  let u : ℤ_[l]ˣ := hu.unit
  have hu1 : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * 1 := hu.unit_spec

  have hmax : ζ - 1 ∈ maximalIdeal ↥(OL LL) := by
    refine (GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm (p := l) LL.1 _).2 ?_
    refine lt_of_eq_of_lt (b := ‖((((ζL - 1 : ↥LL.1)) : PadicAlgCl l) : ℂ_[l])‖) rfl ?_
    rw [PadicComplex.norm_extends]
    exact norm_root_sub_one_lt LL hζL.pow_eq_one
  have hpow : ∀ b : ℕ, (ζL ^ b) ^ l = 1 := fun b => by
    rw [← pow_mul, mul_comm, pow_mul, hζL.pow_eq_one, one_pow]
  choose ev hC hev using fun b : ℕ => exists_ev LL (ζL ^ b) (hpow b)
  refine ⟨u, 1, ζ, ev, hu1, isUnit_one, hζ, hmax, fun b _ => ⟨⟨fun a => hC b a, ?_, fun f => ?_⟩, ⟨fun a => hC b a, hev b⟩⟩⟩
  · obtain ⟨g, hg⟩ : X ∣ exp ↥LL.1 - 1 := X_dvd_iff.2 (by simp)
    have hg0 : constantCoeff g = 1 := by
      have h := congrArg (coeff 1) hg
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h
      rw [← h]; simp [coeff_exp]
    have hzb : ζL ^ b ≠ 0 := pow_ne_zero _ (hζL.ne_zero (by omega))
    have hunit : IsUnit (C (ζL ^ b) * g) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hg0, hzb]
    have hcalc : ev b (X - C (ζ ^ b - 1)) = X * (C (ζL ^ b) * g) := by
      rw [map_sub, hev, hC]
      have hco : ((ζ ^ b - 1 : ↥(OL LL)) : ↥LL.1) = ζL ^ b - 1 := rfl
      rw [hco, map_sub (C : ↥LL.1 →+* _), map_one]
      linear_combination (C (ζL ^ b)) * hg
    rw [hcalc]
    exact associated_mul_unit_left X _ hunit
  · set r : ↥LL.1 := algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) with hr_def
    have hact : Formalism.CohomologicalDescent.HeightDescentMinors.act l ↥(OL LL) (u : ℤ_[l]) f = GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) f := by
      simp only [Formalism.CohomologicalDescent.HeightDescentMinors.act, Formalism.CohomologicalDescent.HeightDescentMinors.br, GlobalTheory.Fon.gam]
      exact (congrFun (coe_substAlgHom _) f).symm
    have hxz := ringHom_gam_X (O := ↥(OL LL)) (L := ↥LL.1) (ev b) (hC b) (ζL ^ b) (hev b) (hpow b)
      (u : ℤ_[l]) ⟨1, by rw [hu1]; ring⟩
    have huniq := ev_unique LL (C (ζL ^ b) * rescale r (exp ↥LL.1) - 1)
      (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL (hpow b))
      ((ev b).comp (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) : PowerSeries ↥(OL LL) →+* PowerSeries ↥(OL LL)))
      ((rescale r).comp (ev b))
      (fun a => by
        change ev b (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) (C a)) = _
        rw [GlobalTheory.Fon.gam_C, hC])
      (fun a => by
        change rescale r (ev b (C a)) = _
        rw [hC, rescale_C'])
      hxz
      (by
        change rescale r (ev b X) = _
        rw [hev, map_sub, map_mul, map_one, rescale_C'])
    rw [hact]
    exact RingHom.congr_fun huniq f

end GlobalTheory.WachExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansionsStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  first | exact @GlobalTheory.WachExp.exists_locExp_expAt | exact GlobalTheory.WachExp.exists_locExp_expAt | (intros; apply GlobalTheory.WachExp.exists_locExp_expAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltration
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

private theorem lau_eq_vecL {F : Type} [Field F] {n : ℕ} (y : Fin n → F⟦X⟧) :
    GlobalTheory.WachBlock.lau y = GlobalTheory.WachPlace.vecL y := by
  funext a
  rfl

private theorem unConst : UnConst := by
  exact unit_series_constant_holds

private theorem lau_mem_iff_vecL_mem {F : Type} [Field F] {n : ℕ}
    {S : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)} {y : Fin n → F⟦X⟧} :
    GlobalTheory.WachBlock.lau y ∈ S ↔ GlobalTheory.WachPlace.vecL y ∈ S := by
  rw [lau_eq_vecL]

private theorem map_comp_rk1_eq_rk1_map {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (χ : Γ →* (↥(OL LL))ˣ) :
    (Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 χ) =
      GlobalTheory.TripleGal.rk1 ((Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp χ) := by
  ext g i j
  simp [GlobalTheory.TripleGal.rk1, toOm, GlobalTheory.WachBlock.ofOL]
  obtain rfl := Subsingleton.elim i j
  simp


open NumberField GlobalTheory.ExpFrame in
theorem GlobalTheory.WachPlace.wach_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  intro hBS E Ω _ _ _ _ _ _ l _ hl hd σ hσ n t h J bot hJ hbot hIB
  obtain ⟨LL, r, ψ, ϖ, R, M, rs, hz, hE, hcr, hψcr, hirr, hM0, hMtop, hmono, hstab, hrs, hlines⟩ := hIB
  obtain ⟨_, _, _⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI : CharP (ResidueField ↥(OL LL)) l := GlobalTheory.WachMap.charP_residueField_of_irreducible LL
  obtain ⟨x, dim, hx, hd0, hdR, hds⟩ :=
    GlobalTheory.T.stable_lattice_chain_with_lines_matrix_form _ ↥(OL LL) n t R r ψ ϖ M rs hirr hM0 hMtop hmono hstab hlines
  obtain ⟨u, c, ζ, jj, hu, hc, hζ, hζm, hjj⟩ := GlobalTheory.T.exists_unit_root_cyclotomicExpExpansions l LL hl hz
  obtain ⟨un, hun⟩ := (unConst l ↥(OL LL) hl (u : ℤ_[l]) c hu).1
  have hψ' : ∀ s, GlobalTheory.ExpFrame.CrysWith
      ((Matrix.GeneralLinearGroup.map (toOm LL)).comp (GlobalTheory.TripleGal.rk1 (ψ s)))
      fun τ => {bot τ + ((s : ℕ) : ℤ)} := by
    intro s
    rw [map_comp_rk1_eq_rk1_map]
    exact hψcr s
  obtain ⟨N, Nψ, y, hN, hNψ, hy⟩ := GlobalTheory.WachPlace.exists_positions_global hBS hl hd hσ
    (J := J) (wt := fun s i => bot i + ((s : ℕ) : ℤ)) hJ (fun s i => hbot i s) hz hE
    (r := r) (ψ := fun s => GlobalTheory.TripleGal.rk1 (ψ s)) hcr hψ' hx hu hun hζ (fun a ha => (hjj a ha).2)
  obtain ⟨V, e, m, hV0, hVrk, hVphi, hVgam, hVe, hVphie, hVgame⟩ :=
    GlobalTheory.WachPlace.filtration_of_chain σ (Fact.out : l.Prime).pos
      (PowerSeries.map (residue ↥(OL LL)) un)
      (fun i => (N.P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun i => (N.D i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).P i).map (PowerSeries.map (residue ↥(OL LL))))
      (fun s i => ((Nψ s).D i).map (PowerSeries.map (residue ↥(OL LL)))) rs dim y hd0 hdR hds hy
  refine ⟨↥(OL LL), ResidueField ↥(OL LL), ↥LL.1, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, maximalIdeal ↥(OL LL), inferInstance,
    residue ↥(OL LL), un, N, Nψ, u, c, ζ, (OL LL).val.toRingHom, jj, ⟨hu, hc, hun⟩,
    ⟨hζ, hζm, Subtype.val_injective, fun b hb => (hjj b hb).1⟩, hN, hNψ, ?_⟩
  unfold GlobalTheory.WachBlock.RedFilt
  refine ⟨R, V, rs, e, m, hrs, hV0, hVrk, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVphi i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i k v hv
    exact lau_mem_iff_vecL_mem.2 (hVgam i k v (lau_mem_iff_vecL_mem.1 hv))
  · intro i s
    simp only [lau_eq_vecL]
    exact hVe i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVphie i s
  · intro i s
    simp only [lau_eq_vecL]
    exact hVgame i s

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachLatticesRankOneModelsReducedFiltrationStatement
open NumberField GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattices_rankOne_models_reducedFiltration : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (red : O' →+* F) (un : PowerSeries O') (N : Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) n O') (Npsi : Fin t → Formalism.CohomologicalDescent.FrobeniusPeriodChange.Lat (E →+* PadicAlgCl l) 1 O') (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsUn l O' (u : ℤ_[l]) un) ∧ (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧ ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l O' L' em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧ Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l N h u J em jj ∧ (∀ s, Formalism.CohomologicalDescent.FrobeniusPeriodChange.LatN l (Npsi s) h u (fun i _ => bot i + ((s : ℕ) : ℤ)) em jj) ∧ GlobalTheory.WachBlock.RedFilt σ l (PowerSeries.map red un) (fun i => (N.P i).map (PowerSeries.map red)) (fun i => (N.D i).map (PowerSeries.map red)) (fun s i => PowerSeries.map red ((Npsi s).P i 0 0)) (fun s i => PowerSeries.map red ((Npsi s).D i 0 0)) := by
  first | exact @GlobalTheory.WachPlace.wach_lattices | exact GlobalTheory.WachPlace.wach_lattices | (intros; apply GlobalTheory.WachPlace.wach_lattices <;> assumption)
end
