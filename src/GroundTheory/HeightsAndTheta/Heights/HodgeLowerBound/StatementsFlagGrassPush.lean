module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.FlagLine
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DataHodge

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def FlagGrassPush.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf : ℚ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    -hFl Ψ N II (FA Ψ N j cf) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j) =
      (Jint Ψ N j cf : ℝ) *
        II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j)) (grassIdeal (Fintype.card Ψ) j (N - j))
          (dimN Ψ N j + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j)))

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section General

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

structure AdaptedBasis {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D) where

  e : ∀ τ, Fin D.N → E τ
  e_indep : ∀ τ, LinearIndependent Ω (e τ)
  e_span : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤
  e_head : ∀ τ, Submodule.span Ω (Set.range (e τ ∘ headIdx D.j_le_N)) = H.F τ

def ComponentData.flagDim0 (D : ComponentData II Ψ K ι Ω E) : ℕ :=
  Fintype.card Ψ * (D.j * (D.j - 1) / 2 + (D.N - D.j) * (D.N - D.j - 1) / 2)

namespace PlueckerData

variable {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)

def xV : (Σ k, ι k) → (Σ k, Pl.ιY k) := fun p => ⟨Sum.inl p.1, p.2⟩

theorem isBlockMap_xV : IsBlockMap (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))) Pl.xV := by
  refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    cases h
    rfl
  · rintro ⟨k', i⟩ ⟨k, rfl⟩
    exact ⟨⟨k, i⟩, rfl⟩

def ofΩHom : Ω →+* Pl.ΩY :=
  (algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY).comp C

theorem ofΩHom_apply (x : Ω) : Pl.ofΩHom x = Pl.ofΩ x := rfl

theorem ofΩHom_injective : Function.Injective Pl.ofΩHom :=
  (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY).comp (C_injective _ _)

variable {H : HodgeData D} (B : AdaptedBasis H)

def gvar0 (τ : Ψ) (a b : Fin D.N) : Pl.ΩY :=
  if (a : ℕ) < D.j ∧ D.j ≤ (b : ℕ) then 0 else Pl.gvar τ a b

def pluecker0 (τ : Ψ) (i : Fin (D.N - 1)) (m : Fin (Pl.M τ i)) : Pl.ΩY :=
  ∑ c : Fin ((i : ℕ) + 1) → Fin D.N, (∏ a, Pl.gvar0 τ (headIdx (step_le i) a) (c a)) *
    Pl.ofΩ (Pl.gen τ i m (exteriorPower.ιMulti Ω _ (B.e τ ∘ c)))

def flagGenericPoint : (Σ k, Pl.ιY k) → Pl.ΩY
  | ⟨Sum.inl k, t⟩ => Pl.ofΩ (D.y ⟨k, t⟩)
  | ⟨Sum.inr q, m⟩ => Pl.pluecker0 B q.1 q.2 m

def flagPrime : Ideal (MRing Pl.ιY) := mCoordIdeal (Pl.flagGenericPoint B)

theorem mConeMap_flagGenericPoint_rename (f : MRing ι) :
    mConeMap (Pl.flagGenericPoint B) (rename Pl.xV f) =
      rename (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))) (MvPolynomial.map Pl.ofΩHom (mConeMap D.y f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, xV, flagGenericPoint, ofΩHom_apply]

theorem imageZ_forget_flagPrime : imageZ Pl.xV (Pl.flagPrime B) = mCoordIdeal D.y := by
  have hinj : Function.Injective fun g : MvPolynomial K Ω =>
      rename (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))) (MvPolynomial.map Pl.ofΩHom g) :=
    (rename_injective _ Sum.inl_injective).comp (map_injective _ Pl.ofΩHom_injective)
  ext f
  show mConeMap (Pl.flagGenericPoint B) (rename Pl.xV f) = 0 ↔ mConeMap D.y f = 0
  rw [mConeMap_flagGenericPoint_rename]
  exact ⟨fun h => hinj (h.trans (by simp)), fun h => by simp [h]⟩

end PlueckerData

end General

def HodgeFlagArith.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H),
    IsArithVar (Pl.flagPrime B) (D.n + 1 + D.flagDim0)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def ZhangLowerX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (e : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (n + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → e ≤ IndefiniteRowSideFullHecke.HeightsSet.height (II K ι) A W) →
    ((n + 1 : ℕ) : ℝ) * e * geomDeg P A n ≤ II K ι P (n + 1) (fun _ => A)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PWedgeTransition
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open GroundTheory.Heights₂.Heights.LowerBoundFree Submodule Module

namespace WedgeTransition

theorem alternating_sum_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : M [⋀^Fin n]→ₗ[R] R) (v : Fin n → M) (A : Matrix (Fin n) (Fin n) R) :
    f (fun q => ∑ a, A a q • v a) = A.det * f v := by
  let T : (Fin n → R) →ₗ[R] M := (Pi.basisFun R (Fin n)).constr R v
  have h := congrArg (fun g => g (fun q a => A a q))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun R (Fin n)) (f.compLinearMap T))
  have hT : ∀ x, T x = ∑ a, x a • v a := fun x => by
    simp [T, Basis.constr_apply_fintype]
  have hTe : (fun i => T (Pi.basisFun R (Fin n) i)) = v := funext fun i => by simp [T]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, Pi.basisFun_det_apply,
    smul_eq_mul] at h
  have e1 : (fun i => T fun a => A a i) = fun q => ∑ a, A a q • v a := funext fun q => hT _
  rw [e1, hTe] at h
  rw [h, mul_comm]
  congr 1
  exact Matrix.det_transpose A

def splitEquiv {j N : ℕ} (hj : j ≤ N) : Fin j ⊕ Fin (N - j) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hj))

theorem splitEquiv_inl {j N : ℕ} (hj : j ≤ N) (a : Fin j) : splitEquiv hj (Sum.inl a) = Fin.castLE hj a :=
  Fin.ext (by simp [splitEquiv])

theorem splitEquiv_inr {j N : ℕ} (hj : j ≤ N) (a : Fin (N - j)) : splitEquiv hj (Sum.inr a) = tailIdx hj a :=
  Fin.ext (by simp [splitEquiv, tailIdx])

theorem sum_split {M : Type*} [AddCommMonoid M] {j N : ℕ} (hj : j ≤ N) (g : Fin N → M) :
    ∑ p, g p = ∑ a, g (Fin.castLE hj a) + ∑ a, g (tailIdx hj a) := by
  rw [← (splitEquiv hj).sum_comp, Fintype.sum_sum_type]
  simp [splitEquiv_inl, splitEquiv_inr]

theorem det_split_of_zero {R : Type*} [CommRing R] {j N : ℕ} (hj : j ≤ N) (G : Matrix (Fin N) (Fin N) R)
    (h0 : ∀ a a', G (tailIdx hj a) (Fin.castLE hj a') = 0) :
    G.det = (G.submatrix (Fin.castLE hj) (Fin.castLE hj)).det *
      (G.submatrix (tailIdx hj) (tailIdx hj)).det := by
  rw [← Matrix.det_submatrix_equiv_self (splitEquiv hj) G,
    ← Matrix.fromBlocks_toBlocks (G.submatrix (splitEquiv hj) (splitEquiv hj))]
  have h21 : (G.submatrix (splitEquiv hj) (splitEquiv hj)).toBlocks₂₁ = 0 := by
    ext a a'
    simp [Matrix.toBlocks₂₁, splitEquiv_inl, splitEquiv_inr, h0]
  rw [h21, Matrix.det_fromBlocks_zero₂₁]
  congr 2

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (F : Submodule Ω V) {N j : ℕ} (hj : j ≤ N)

theorem exists_form_quotWedge_eq_one {b' : Fin N → V} (hli : LinearIndependent Ω b')
    (hsp : span Ω (Set.range b') = ⊤) (hF : span Ω (Set.range (b' ∘ Fin.castLE hj)) = F) :
    ∃ ℓ : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω, ℓ (quotWedge F hj b') = 1 := by
  let B := Basis.mk hli hsp.ge
  have : Module.Finite Ω V := Module.Finite.of_basis B
  have hV : Module.finrank Ω V = N := by simpa using Module.finrank_eq_card_basis B
  have hFr : Module.finrank Ω F = j := by
    rw [← hF, finrank_span_eq_card (hli.comp _ (Fin.castLE_injective hj))]
    simp
  have hQ := Submodule.finrank_quotient_add_finrank F
  let w : Fin (N - j) → V ⧸ F := fun a => F.mkQ (b' (tailIdx hj a))
  have hspan : ⊤ ≤ span Ω (Set.range w) := by
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective F x
    have h1 : F.mkQ v ∈ span Ω (F.mkQ '' Set.range b') := by
      rw [← Submodule.map_span, hsp]
      exact ⟨v, trivial, rfl⟩
    refine (Submodule.span_le.mpr ?_) h1
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i.val < j
    · have hmem : b' i ∈ F := hF ▸ subset_span ⟨⟨i, hi⟩, rfl⟩
      have : F.mkQ (b' i) = 0 := by simpa using hmem
      rw [SetLike.mem_coe, this]
      exact zero_mem _
    · have : i = tailIdx hj ⟨i - j, by omega⟩ := Fin.ext (by simp [tailIdx]; omega)
      rw [this]
      exact subset_span ⟨_, rfl⟩
  have hli' : LinearIndependent Ω w :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp; omega)
  let Q := Basis.mk hli' hspan
  refine ⟨exteriorPower.alternatingMapLinearEquiv Q.det, ?_⟩
  rw [quotWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have : (fun a => F.mkQ (b' (tailIdx hj a))) = ⇑Q := funext fun a => (Basis.mk_apply hli' hspan a).symm
  rw [this, Basis.det_self]

end WedgeTransition

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end
