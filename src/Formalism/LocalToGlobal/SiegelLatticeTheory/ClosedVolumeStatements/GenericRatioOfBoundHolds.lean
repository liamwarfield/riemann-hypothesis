module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermCarrierStable
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagClassConstancy.FlagOfInSFRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.FinrankOrthAddLe
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormChiNBi
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGenerators.ScalarEquivOfGen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaModX
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalRelRepFree
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMatBound
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AddIntG
public import Formalism.PadicSubsetSums.StableGradedCounts.MemBesselSetZeroIffUpperTriangular

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.WhitFunctDual
namespace PI

def WhitFunctDual : Prop :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GelfandGraevMultOne → Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne

end PI
end

section -- merged from Formalism.PeriodIntegrals.ExplicitFormulaCounts.BetaIndep
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaIndependence.YliftLeOrth
noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaIndep

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem orth_anti {U W : Submodule E S.V} (h : U ≤ W) : orth S W ≤ orth S U := by
  intro v hv
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth] at hv ⊢
  exact fun x hx => hv x (h hx)

theorem Hp_le_orth (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Hp Λ F F' ≤ orth S (Xsp F') :=
  orth_anti (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F')

theorem Ylift'_le_orth (Λ : Submodule (𝓞 E) S.V) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') : Ylift' Λ F F' ≤ orth S (Xsp F') := by
  intro v hv
  have hX : Xsp F' ≤ Xplus F' := (le_sup_left : F'.fl.X ≤ F'.fl.X ⊔ Submodule.span E {F'.fl.z})
  exact orth_anti hX hv.2

theorem mem_ThPairs (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (p : S.V × S.V) :
    p ∈ ThPairs Λ F F' F'' β ↔
      ((p.1 ∈ Hp Λ F F' ∧ p.2 ∈ Hp Λ F F'') ∧ p.1 - p.2 ∈ Xsp F) ∧ β p.1 - p.2 ∈ Xsp F'' :=
  Iff.rfl

variable (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T')
  (β₁ β₂ : S.V ≃ₗ[E] S.V)

theorem ThPairs_eq (hΛ : Submodule.IsFullLattice E Λ)
    (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') :
    ThPairs Λ F F' F'' β₁ = ThPairs Λ F F' F'' β₂ := by
  ext p
  rw [mem_ThPairs, mem_ThPairs]
  have hd : p.1 ∈ Hp Λ F F' → β₁ p.1 - β₂ p.1 ∈ Xsp F'' := fun h1 => H p.1 (Hp_le_orth Λ hΛ F F' h1)
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    have e : β₂ p.1 - p.2 = (β₁ p.1 - p.2) - (β₁ p.1 - β₂ p.1) := by abel
    rw [e]
    exact sub_mem h4 (hd h1)
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    have e : β₁ p.1 - p.2 = (β₂ p.1 - p.2) + (β₁ p.1 - β₂ p.1) := by abel
    rw [e]
    exact add_mem h4 (hd h1)

theorem Th_eq (hΛ : Submodule.IsFullLattice E Λ)
    (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') :
    Th Λ F F' F'' β₁ = Th Λ F F' F'' β₂ := by
  unfold Th
  rw [ThPairs_eq Λ F F' F'' β₁ β₂ hΛ H]

theorem s0_eq (hΛ : Submodule.IsFullLattice E Λ)
    (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') (k : ℕ) :
    s0 Λ F F' F'' β₁ k = s0 Λ F F' F'' β₂ k := by
  unfold s0
  rw [Th_eq Λ F F' F'' β₁ β₂ hΛ H]

theorem isScalar_iff (H : ∀ v ∈ orth S (Xsp F'), β₁ v - β₂ v ∈ Xsp F'') :
    IsScalar Λ F F' F'' β₁ ↔ IsScalar Λ F F' F'' β₂ := by
  have key : ∀ y1' ∈ Ylift' Λ F F', ∀ y2'' : S.V,
      (y2'' - β₁ y1' ∈ Xsp F'' ↔ y2'' - β₂ y1' ∈ Xsp F'') := by
    intro y1' hy y2''
    have hd := H y1' (Ylift'_le_orth Λ F F' hy)
    constructor
    · intro h
      have e : y2'' - β₂ y1' = (y2'' - β₁ y1') + (β₁ y1' - β₂ y1') := by abel
      rw [e]
      exact add_mem h hd
    · intro h
      have e : y2'' - β₁ y1' = (y2'' - β₂ y1') - (β₁ y1' - β₂ y1') := by abel
      rw [e]
      exact sub_mem h hd
  unfold IsScalar
  constructor
  · intro h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hb
    exact h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx ((key y1' hy1' y2'').2 hb)
  · intro h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx hb
    exact h y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hx ((key y1' hy1' y2'').1 hb)

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem betaIndep_of (D : D7) (u u' : D.what₂.Word) (h : PI.ScalPairs.BetaL D u u') :
    PI.ScalPairs.BetaFree D u u' := by
  intro hg F0 Λ hR x y hx hy β₁ β₂ h1 h2
  have hΛ : Submodule.IsFullLattice D.host.E Λ := hR.1.1
  have H := h hg F0 Λ hR x y hx hy β₁ β₂ h1 h2
  exact ⟨s0_eq Λ _ _ _ β₁ β₂ hΛ H _, isScalar_iff Λ _ _ _ β₁ β₂ H⟩

end D7

end PI.UnitaryGroupMassFormula.BetaIndep
end
end

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scalPairs_betaFree (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalPairs.BetaFree D u u' :=
  PI.UnitaryGroupMassFormula.BetaIndep.betaIndep_of D u u' (beta_mod_iota_surjective D u u')
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarPairDr
theorem scalar_pair_dr (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' :=
  PI.ScalarPairDr.W.scalarDr D u u'
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdCellInS
theorem term_id_iff_in_s (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermIdIffInS D u u' :=
  PI.UnitaryGroupMassFormula.IdCellInSW.termIdIffInS_of D (PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D) u u'
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DCRelEquiv
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_eq_iff_relation (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermEqIff D u u' := by
  intro F0 Λ _
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.eqIffAll_holds _ _ _ _ _ _ _ _
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSClassConst
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem in_s_class_constant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSFun D u u' :=
  fun _ Λ _ => PI.InSClassConstW.inSFun_all Λ _ _
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSRelevant
theorem in_s_relevant (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.FourParts.TermInSRel D u u' :=
  PI.UnitaryGroupMassFormula.InSRelevantW.termInSRel_main D u u'
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PairCorankPos
theorem pair_corank_pos : PI.PairCorankPos.CorankPosG := PI.PairCorankPos.W.corankPosG
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMirBound
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.MirabolicBound
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development
namespace PI.GGMirBoundW

open Matrix Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

def D (F : Type) [Fintype F] (m : ℕ) : ℕ := ∏ i ∈ Finset.Ico 1 m, (Fintype.card F ^ i - 1)

section Defs

variable {F : Type} [Field F] [Fintype F]

def blkM {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) F)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def blkHom (F : Type) [Field F] (n : ℕ) : Matrix (Fin n) (Fin n) F →* Matrix (Fin (n + 1)) (Fin (n + 1)) F where
  toFun := blkM
  map_one' := by
    simp only [blkM, Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  map_mul' A B := by
    simp only [blkM]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def E (F : Type) [Field F] (n : ℕ) : GL (Fin n) F →* GL (Fin (n + 1)) F := Units.map (blkHom F n)

def colM {n : ℕ} (x : Fin n → F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  (Matrix.fromBlocks 1 (Matrix.of fun i (_ : Fin 1) => x i) 0 (1 : Matrix (Fin 1) (Fin 1) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

theorem colM_mul {n : ℕ} (x y : Fin n → F) : colM x * colM y = colM (x + y) := by
  simp only [colM]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [add_comm]
  · simp
  · simp

theorem colM_zero {n : ℕ} : colM (0 : Fin n → F) = 1 := by
  simp only [colM]
  have : (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → F) i) = 0 := by ext; simp
  rw [this, Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

def col {n : ℕ} (x : Fin n → F) : GL (Fin (n + 1)) F where
  val := colM x
  inv := colM (-x)
  val_inv := by rw [colM_mul, add_neg_cancel, colM_zero]
  inv_val := by rw [colM_mul, neg_add_cancel, colM_zero]

def LastRowE {n : ℕ} (g : GL (Fin (n + 1)) F) : Prop :=
  ∀ j, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = if j = Fin.last n then 1 else 0

end Defs

def Claim (F : Type) [Field F] [Fintype F] (n : ℕ) : Prop :=
  ∀ (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1)) F) V)
      (ℓ : Module.Dual ℂ V), ℓ ≠ 0 → IsWhit ψ₀ π ℓ →
      ∃ p : Fin (D F (n + 1)) → GL (Fin (n + 1)) F,
        (∀ i, LastRowE (p i)) ∧ LinearIndependent ℂ (fun i => ℓ ∘ₗ π (p i))

def BaseProp : Prop := ∀ (F : Type) [Field F] [Fintype F], Claim F 0

def StepProp : Prop := ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), Claim F n → Claim F (n + 1)

def UnitriangularBlockExtension : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (u : GL (Fin n) F), IsUni n u →
    IsUni (n + 1) (E F n u) ∧
      superdiag (n + 1) (E F n u : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
        superdiag n (u : Matrix (Fin n) (Fin n) F)

def ColFacts : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (x : Fin (n + 1) → F),
    IsUni (n + 2) (col x) ∧
      superdiag (n + 2) (col x : Matrix (Fin (n + 2)) (Fin (n + 2)) F) = x (Fin.last n)

def ConjCol : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (A : GL (Fin n) F) (x : Fin n → F),
    E F n A * col x = col ((A : Matrix (Fin n) (Fin n) F) *ᵥ x) * E F n A

def RowExists : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ) (r : Fin (n + 1) → F), r ≠ 0 →
    ∃ g : GL (Fin (n + 1)) F, ∀ j, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = r j

def CharOrth : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (m : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 → ∀ r s : Fin m → F,
    (∑ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x))) = if r = s then (Fintype.card F : ℂ) ^ m else 0

def SepLemma : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X R ι : Type) [Fintype X] [Fintype R] [Fintype ι]
    (T : X → W →ₗ[ℂ] W) (χ χ' : R → X → ℂ) (N : ℂ), N ≠ 0 →
    (∀ r s, ∑ x, χ r x * χ' s x = if r = s then N else 0) →
    ∀ f : R × ι → W, (∀ x r i, T x (f (r, i)) = χ r x • f (r, i)) →
      (∀ r, LinearIndependent ℂ (fun i => f (r, i))) → LinearIndependent ℂ f

def StepOf : Prop := UnitriangularBlockExtension → ColFacts → ConjCol → RowExists → CharOrth → SepLemma → StepProp

theorem claim_all (hb : BaseProp) (hs : StepProp) (F : Type) [Field F] [Fintype F] : ∀ n, Claim F n := by
  intro n
  induction n with
  | zero => exact hb F
  | succ n ih => exact hs F n ih

theorem mirabolicBound_of (hb : BaseProp) (hs : StepProp) : MirabolicBound := by
  intro F _ _ k ψ₀ hψ V _ _ _ π _ hgen
  obtain ⟨ℓ, hℓ, hW⟩ := hgen
  cases k with
  | zero =>
    rw [Finset.Ico_eq_empty_of_le (by norm_num), Finset.prod_empty]
    have : Nontrivial V := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hℓ (by ext v; simp [Subsingleton.elim v 0])
    exact Module.finrank_pos
  | succ n =>
    obtain ⟨p, -, hli⟩ := claim_all hb hs F n ψ₀ hψ V π ℓ hℓ hW
    have h1 := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Subspace.dual_finrank_eq] at h1
    exact h1

theorem mirabolicBound_of_steps (hb : BaseProp) (hst : StepOf) (h1 : UnitriangularBlockExtension) (h2 : ColFacts) (h3 : ConjCol)
    (h4 : RowExists) (h5 : CharOrth) (h6 : SepLemma) : MirabolicBound :=
  mirabolicBound_of hb (hst h1 h2 h3 h4 h5 h6)

end

end PI.GGMirBoundW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.LastRowMul
namespace PI.GGMirBoundW

open Matrix Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

section Entries

variable {F : Type} [Field F] [Fintype F] {n : ℕ}

@[simp] theorem blkM_cc (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blkM A (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc]

@[simp] theorem blkM_cl (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    blkM A (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem blkM_lc (A : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    blkM A (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem blkM_ll (A : Matrix (Fin n) (Fin n) F) :
    blkM A (Fin.last n) (Fin.last n) = 1 := by
  simp [blkM, finSumFinEquiv_symm_last]

@[simp] theorem colM_cc (x : Fin n → F) (i j : Fin n) :
    colM x (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) F) i j := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc]

@[simp] theorem colM_cl (x : Fin n → F) (i : Fin n) :
    colM x (Fin.castSucc i) (Fin.last n) = x i := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem colM_lc (x : Fin n → F) (j : Fin n) :
    colM x (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem colM_ll (x : Fin n → F) :
    colM x (Fin.last n) (Fin.last n) = 1 := by
  simp [colM, finSumFinEquiv_symm_last]

theorem E_val (A : GL (Fin n) F) : ((E F n A : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    blkM (A : Matrix (Fin n) (Fin n) F) := rfl

theorem col_val (x : Fin n → F) : ((col x : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    colM x := rfl

end Entries

theorem blkFacts : UnitriangularBlockExtension := by
  intro F _ _ n u hu
  obtain ⟨hd, hl⟩ := hu
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [E_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using hd i
  · rw [E_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [blkM_cc]
        exact hl i j (Fin.castSucc_lt_castSucc_iff.mp hij)
  · rw [E_val]
    unfold superdiag
    simp [Fin.sum_univ_castSucc]

theorem colFacts : ColFacts := by
  intro F _ _ n x
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [col_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · rw [col_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [colM_cc]
        exact Matrix.one_apply_ne (ne_of_gt (Fin.castSucc_lt_castSucc_iff.mp hij))
  · rw [col_val]
    unfold superdiag
    have h0 : ∀ i j : Fin (n + 1),
        (if (j : ℕ) = (i : ℕ) + 1 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j else 0) = 0 := by
      intro i j
      split_ifs with h
      · rw [Matrix.one_apply_ne]
        intro e; subst e; omega
      · rfl
    have hl : ∀ i : Fin (n + 1), (n = (i : ℕ)) ↔ (i = Fin.last n) := by
      intro i; rw [Fin.ext_iff, Fin.val_last]; omega
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.sum_univ_castSucc (n := n + 1), colM_cc, colM_cl, colM_lc, colM_ll, Fin.val_castSucc,
      Fin.val_last, h0, ite_self, add_left_inj, hl]
    simp

theorem conjCol : ConjCol := by
  intro F _ _ n A x
  ext : 1
  simp only [Units.val_mul, E_val, col_val, blkM, colM]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp
  · simp

theorem baseProp : BaseProp := by
  intro F _ _ ψ₀ _ V _ _ π ℓ hℓ _
  have hD : D F (0 + 1) = 1 := by simp [D]
  show ∃ p : Fin (D F (0 + 1)) → GL (Fin (0 + 1)) F, _
  rw [hD]
  refine ⟨fun _ => 1, fun _ j => ?_, ?_⟩
  · simp only [Units.val_one]
    rw [Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · rw [linearIndependent_unique_iff]
    show ℓ ∘ₗ π 1 ≠ 0
    rw [map_one]
    intro h
    apply hℓ
    ext v
    simpa using LinearMap.congr_fun h v

theorem lastRowE_E {F : Type} [Field F] [Fintype F] {n : ℕ} (A : GL (Fin n) F) : LastRowE (E F n A) := by
  intro j
  rw [E_val]
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp [Fin.castSucc_ne_last]

theorem lastRow_mul {F : Type} [Field F] [Fintype F] {n : ℕ} {p : GL (Fin (n + 1)) F} (hp : LastRowE p)
    (g : GL (Fin (n + 1)) F) (j : Fin (n + 1)) :
    ((p * g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j := by
  have h2 : ∀ l, (p : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) l = if l = Fin.last n then 1 else 0 := hp
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [h2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

end PI.GGMirBoundW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.CardNonzero
namespace PI.GGMirBoundW

open Finset Matrix Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

theorem card_nonzero (F : Type) [Field F] [Fintype F] (m : ℕ) :
    Fintype.card {r : Fin m → F // r ≠ 0} = Fintype.card F ^ m - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin]

theorem stepOf : StepOf := by
  intro hB hC hJ hR hO hS F _ _ n IH ψ₀ hψ V _ _ π ℓ hℓ hW

  let π' : Representation ℂ (GL (Fin (n + 1)) F) V := π.comp (E F (n + 1))
  have hW' : IsWhit ψ₀ π' ℓ := by
    intro u hu v
    have h := hW (E F (n + 1) u) (hB F (n + 1) u hu).1 v
    simp only [psiU] at h ⊢
    rw [(hB F (n + 1) u hu).2] at h
    exact h
  obtain ⟨p, hpL, hpI⟩ := IH ψ₀ hψ V π' ℓ hℓ hW'
  let R := {r : Fin (n + 1) → F // r ≠ 0}
  choose g hg using fun r : R => hR F n r.1 r.2
  let A : R × Fin (D F (n + 1)) → GL (Fin (n + 1)) F := fun q => p q.2 * g q.1
  have hArow : ∀ q j, (A q : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j := by
    intro q j
    show ((p q.2 * g q.1 : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j
    rw [lastRow_mul (hpL q.2), hg]
  let f : R × Fin (D F (n + 1)) → Module.Dual ℂ V := fun q => ℓ ∘ₗ π (E F (n + 1) (A q))

  have hf : ∀ (x : Fin (n + 1) → F) (r : R) (i : Fin (D F (n + 1))),
      (π (col x)).dualMap (f (r, i)) = (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x • f (r, i) := by
    intro x r i
    ext v
    show ℓ (π (E F (n + 1) (A (r, i))) (π (col x) v)) = ψ₀ (r.1 ⬝ᵥ x) * ℓ (π (E F (n + 1) (A (r, i))) v)
    rw [← Module.End.mul_apply, ← map_mul, hJ F (n + 1) (A (r, i)) x, map_mul, Module.End.mul_apply,
      hW _ (hC F n _).1, psiU, (hC F n _).2]
    congr 2
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hArow]

  have hblock : ∀ r : R, LinearIndependent ℂ (fun i => f (r, i)) := by
    intro r
    have he : (fun i => f (r, i)) = (π (E F (n + 1) (g r))).dualMap ∘ (fun i => ℓ ∘ₗ π' (p i)) := by
      funext i
      ext v
      show ℓ (π (E F (n + 1) (p i * g r)) v) = ℓ (π (E F (n + 1) (p i)) (π (E F (n + 1) (g r)) v))
      rw [map_mul, map_mul, Module.End.mul_apply]
    rw [he]
    refine hpI.map' _ (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective ?_))
    intro v
    refine ⟨π (E F (n + 1) (g r))⁻¹ v, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hN : ((Fintype.card F : ℂ) ^ (n + 1)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  have horth : ∀ r s : R, ∑ x : Fin (n + 1) → F, (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x *
      (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x))) s x = if r = s then (Fintype.card F : ℂ) ^ (n + 1) else 0 := by
    intro r s
    rw [hO F (n + 1) ψ₀ hψ r.1 s.1]
    exact if_congr Subtype.val_inj rfl rfl
  have hind := hS (Module.Dual ℂ V) (Fin (n + 1) → F) R (Fin (D F (n + 1)))
    (fun x => (π (col x)).dualMap) (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x)))
    _ hN (fun r s => by convert horth r s) f hf hblock
  have hcard : Fintype.card (Fin (D F (n + 1 + 1))) = Fintype.card (R × Fin (D F (n + 1))) := by
    rw [Fintype.card_fin, Fintype.card_prod, card_nonzero, Fintype.card_fin, D, D,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ n + 1), mul_comm]
  let e : Fin (D F (n + 1 + 1)) ≃ R × Fin (D F (n + 1)) := Fintype.equivOfCardEq hcard
  refine ⟨fun k => E F (n + 1) (A (e k)), fun k => lastRowE_E _, ?_⟩
  exact hind.comp e e.injective

end

end PI.GGMirBoundW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.RowExists
namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

theorem rowExists : RowExists := by
  intro F _ _ n r hr
  obtain ⟨k, hk⟩ : ∃ k, r k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap k (Fin.last n) with hσ
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.updateRow 1 (Fin.last n) (fun j => r (σ j)) with hA
  have hAtri : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.mpr (Fin.le_last j))
    rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]
  have hdetA : A.det = r k := by
    rw [Matrix.det_of_lowerTriangular A hAtri, Finset.prod_eq_single (Fin.last n)]
    · rw [hA, Matrix.updateRow_self]
      simp [hσ]
    · intro i _ hi
      rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_eq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := A.submatrix id σ with hB
  have hdetB : B.det ≠ 0 := by
    rw [hB, Matrix.det_permute', hdetA]
    refine mul_ne_zero ?_ hk
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  refine ⟨hunit.unit, fun j => ?_⟩
  rw [IsUnit.unit_spec]
  simp [hB, hA, hσ, Matrix.updateRow_self, Equiv.swap_apply_self]

end

end PI.GGMirBoundW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.CharSumOne
namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

theorem addChar_sum {F : Type} [Field F] (ψ₀ : AddChar F ℂ) {m : ℕ} (g : Fin m → F) :
    ψ₀ (∑ i, g i) = ∏ i, ψ₀ (g i) := by
  have h : ∀ s : Finset (Fin m), ψ₀ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ₀ (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  exact h _

theorem charSum_one {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) (a : F) :
    ∑ t : F, ψ₀ (a * t) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  split_ifs with ha
  · subst ha
    simp [AddChar.map_zero_eq_one]
  · rw [show (∑ t : F, ψ₀ (a * t)) = ∑ t : F, ψ₀ t from
        Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun t => rfl)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem charSum {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) {m : ℕ} (ν : Fin m → F) :
    ∑ c : Fin m → F, ψ₀ (∑ i, ν i * c i) = if ν = 0 then (Fintype.card F : ℂ) ^ m else 0 := by
  have hps : ∑ c : Fin m → F, ∏ i, ψ₀ (ν i * c i) = ∏ i, ∑ t : F, ψ₀ (ν i * t) := by
    first
      | exact (Fintype.prod_sum (fun i t => ψ₀ (ν i * t))).symm
      | (rw [Finset.prod_univ_sum]; simp)
  simp_rw [addChar_sum ψ₀]
  rw [hps]
  simp_rw [charSum_one ψ₀ hψ]
  split_ifs with hν
  · subst hν
    simp
  · obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hν (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem charOrth : CharOrth := by
  intro F _ _ m ψ₀ hψ r s
  have h : ∀ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x)) = ψ₀ (∑ i, (r - s) i * x i) := by
    intro x
    rw [← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_dotProduct]
    rfl
  simp_rw [h]
  rw [charSum ψ₀ hψ (r - s)]
  simp only [sub_eq_zero]

theorem sepLemma : SepLemma := by
  intro W _ _ X R ι _ _ _ T χ χ' N hN horth f hf hind
  have hf' : ∀ x (q : R × ι), T x (f q) = χ q.1 x • f q := fun x q => hf x q.1 q.2
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  obtain ⟨s, i⟩ := p
  have h1 : ∑ x, χ' s x • T x (∑ q, g q • f q) = 0 := by
    rw [hg]
    simp
  have h2 : ∑ x, χ' s x • T x (∑ q, g q • f q) =
      ∑ q, (if q.1 = s then N * g q else 0) • f q := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum, map_smul, hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have ho := horth q.1 s
    calc ∑ x, χ' s x * (g q * χ q.1 x) = g q * ∑ x, χ q.1 x * χ' s x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = _ := by
          rw [ho]
          split_ifs <;> ring
  have h3 : ∑ q : R × ι, (if q.1 = s then N * g q else 0) • f q = N • ∑ j, g (s, j) • f (s, j) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · simp [Finset.smul_sum, smul_smul]
    · intro r _ hr
      simp [hr]
    · intro h
      exact absurd (Finset.mem_univ s) h
  rw [h2, h3] at h1
  have key : ∑ j, g (s, j) • f (s, j) = 0 := (smul_eq_zero.mp h1).resolve_left hN
  exact (Fintype.linearIndependent_iff.mp (hind s)) (fun j => g (s, j)) key i

end

end PI.GGMirBoundW
end

namespace PI.GGMirBoundW

theorem mirabolicBound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  mirabolicBound_of_steps baseProp stepOf blkFacts colFacts conjCol rowExists charOrth sepLemma

end PI.GGMirBoundW
end

theorem mirabolic_bound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  PI.GGMirBoundW.mirabolicBound
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WhitFunctDual
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WhittakerFunctionalDual.StableOfIrreducible
namespace PI.WhitFunctDualWork

open Formalism.L2.SG.GGMirabolic

theorem stable_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, π g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  have := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    show (⊥ : Submodule ℂ V) = ⊤
    ext x
    simp [Subsingleton.elim x 0]
  · rcases IsSimpleOrder.eq_bot_or_eq_top
        (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation π) with h1 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem isIrr_dual {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr (Representation.dual π) := by
  obtain ⟨hnt, hst⟩ := stable_of_irreducible π h
  refine ⟨Module.nontrivial_of_finrank_pos (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos),
    fun W hW => ?_⟩
  have hU : ∀ g, ∀ v ∈ W.dualCoannihilator, π g v ∈ W.dualCoannihilator := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hv _ (hW g⁻¹ f hf)
  have hW' : W = W.dualCoannihilator.dualAnnihilator :=
    Subspace.dualCoannihilator_dualAnnihilator_eq.symm
  rcases hst _ hU with h0 | h0
  · right
    rw [hW', h0, Submodule.dualAnnihilator_bot]
  · left
    rw [hW', h0, Submodule.dualAnnihilator_top]

theorem besselEdge_zero (i j : ℕ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge 0 0 i j ↔ j = i + 1 := by
  unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge
  constructor <;> intro h <;> omega

theorem whit_mem {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V)
    (ℓ : Module.Dual ℂ V) (hℓ : IsWhit ψ₀ π ℓ) :
    ℓ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := by
  intro u
  beta_reduce
  obtain ⟨hdiag, hlow, -⟩ := u.2
  have huni : IsUni k (u : GL (Fin k) F) := ⟨hdiag, hlow⟩
  have hp : psiU ψ₀ (u : GL (Fin k) F) ≠ 0 := by
    intro h0
    have h3 := AddChar.map_add_eq_mul ψ₀ (superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
      (-superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at h3
    unfold psiU at h0
    rw [h0, zero_mul] at h3
    exact one_ne_zero h3
  have hchar : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar ψ₀⁻¹ 0 0 k (u : GL (Fin k) F) =
      (psiU ψ₀ (u : GL (Fin k) F))⁻¹ := by
    unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar psiU superdiag
    rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
    congr 2
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : (j : ℕ) = (i : ℕ) + 1 <;> simp [hij, besselEdge_zero]
  ext v
  have hinv : π (u : GL (Fin k) F) (π ((u : GL (Fin k) F)⁻¹) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hw := hℓ (u : GL (Fin k) F) huni (π ((u : GL (Fin k) F)⁻¹) v)
  rw [hinv] at hw
  rw [Representation.dual_apply, LinearMap.smul_apply, hchar, smul_eq_mul,
    Module.Dual.transpose_apply, LinearMap.comp_apply, hw, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem whitFunctDual_main : PI.WhitFunctDual := by
  intro hGG F _ _ k ψ₀ hψ V _ _ _ π hπ ℓ₁ ℓ₂ h1 h2 hne
  have hψ' : ψ₀⁻¹ ≠ 1 := inv_ne_one.mpr hψ
  have hirr := isIrr_dual π hπ
  have hdim := hGG F (Module.Dual ℂ V) k ψ₀⁻¹ (Representation.dual π) hψ' hirr
  have m1 : ℓ₁ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₁ h1
  have m2 : ℓ₂ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₂ h2
  have hne' : (⟨ℓ₁, m1⟩ : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) ≠ 0 :=
    fun h0 => hne (congrArg Subtype.val h0)
  have hpos : 0 < Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne'⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne').mp (le_antisymm hdim hpos) ⟨ℓ₂, m2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

end PI.WhitFunctDualWork
end

theorem whittaker_functional_dual : PI.WhitFunctDual := PI.WhitFunctDualWork.whitFunctDual_main
end

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

section Terms

variable (D : D7) (u u' : D.what₂.Word)

theorem TermEqIff_holds : Formalism.L2.SG.TermDef.TermEqIff D u u' := term_eq_iff_relation D u u'
theorem TermStable_holds : Formalism.L2.SG.TermDef.TermStable D u u' := term_carrier_stable D u u'
theorem TermFun_holds : Formalism.L2.SG.TermDef.TermFun D u u' := term_function_const D u u'

theorem TermInSFun_holds : Formalism.L2.SG.FourParts.TermInSFun D u u' := in_s_class_constant D u u'
theorem TermInSRel_holds : Formalism.L2.SG.FourParts.TermInSRel D u u' := in_s_relevant D u u'
theorem TermIdIffInS_holds : Formalism.L2.SG.FourParts.TermIdIffInS D u u' := term_id_iff_in_s D u u'

theorem ScalarEquiv_holds : Formalism.L2.SG.Corank.ScalarEquiv D u u' := Formalism.L2.SG.Corank.scalarEquiv_of_G (D := D) scalar_equiv_general u u'
theorem ScalarRepFree_holds : Formalism.L2.SG.Corank.ScalarRepFree D u u' := scalar_rep_free D u u'
theorem BetaFree_holds : Formalism.L2.SG.Corank.BetaFree D u u' := scalPairs_betaFree D u u'

theorem ScalarDr_holds : Formalism.L2.SG.Corank.ScalarDr D u u' := by
  intro F0 what₂ hrows p hp
  exact scalar_pair_dr D u u' F0 what₂ hrows p.lam p.mem p.fst p.snd p.G_fst p.G_snd p.beta p.isPair
    hp.1 hp.2

end Terms

theorem CorankPosG_holds : PI.PairCorankPos.CorankPosG := pair_corank_pos
theorem ScalarEquivG_holds : Formalism.L2.SG.Corank.ScalarEquivG := scalar_equiv_general

theorem GelfandGraevMultOne_holds : Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne := whittaker_functional_dual Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_graev_multiplicity_one
theorem MirabolicBound_holds : Formalism.L2.SG.GGMirabolic.MirabolicBound := mirabolic_bound
theorem GGMatrixBoundOfLit_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit := gg_matrix_bound
theorem GGMatrixBound_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBound :=
  GGMatrixBoundOfLit_holds GelfandGraevMultOne_holds MirabolicBound_holds
theorem TermsGGBound_holds : Formalism.L2.SG.GGMirabolic.TermsGGBound :=
  Formalism.L2.SG.GGMirabolic.termsGGBound_of_matrix GGMatrixBound_holds

theorem IsSplitRow_holds (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) :
    Formalism.L2.SG.Saturated.IsSplitRow D F0 Λ := split_row_iso D u F0 Λ hΛ

end Formalism.L2.SG.Closed
