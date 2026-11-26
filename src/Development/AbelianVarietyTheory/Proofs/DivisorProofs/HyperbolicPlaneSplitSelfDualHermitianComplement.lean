module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnimodularPlaneSplitAlongVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeFromConjugateComplement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapTraceEq
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions
open Formalism.MainNotions.S (FlagG LieU perpS)

namespace GlobalTheory.RelFlag

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_eq_form (x y : S.V) : S.hT y x = form (starRingEnd E) S.gram (co S x) (co S y) := by
  rw [hT_eq_sum, form, Matrix.dotProduct_mulVec]; rfl

variable (F : FlagG S r T)

variable {F}

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RelFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem posIndex_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature M p q) : posIndex M = p ∧ posIndex (-M) = q := by
  obtain ⟨e, P, hP⟩ := h
  set A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix _ _ ℂ).map (starRingEnd ℂ) with hA
  have hAc : A.map (starRingEnd ℂ) = (P : Matrix _ _ ℂ) := by
    ext i j; simp [hA]
  have hdet : A.det ≠ 0 := by
    have hu := Matrix.isUnits_det_units P
    have h2 := RingHom.map_det (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    rw [RingHom.mapMatrix_apply] at h2
    rw [hA, ← h2]
    exact (map_ne_zero _).2 hu.ne_zero
  have hc : A.transpose * M.reindex e e * A.map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    rw [hAc, ← hP]; rfl
  have hcn : A.transpose * (-M).reindex e e * A.map (starRingEnd ℂ) = -Formalism.UG.Jpq p q := by
    rw [← hc]
    have : (-M).reindex e e = -(M.reindex e e) := by ext; simp
    rw [this, Matrix.mul_neg, Matrix.neg_mul]
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  have hJn : -Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => 1)) := by
    rw [hJ, Matrix.diagonal_neg]
    congr 1
    ext i; rcases i with i | i <;> simp
  have hre : ∀ N : Matrix n n ℂ, posIndex N = posIndex (N.reindex e e) := fun N =>
    (posIndex_submatrix_equiv N e.symm).symm
  constructor
  · rw [hre, ← posIndex_congr _ hdet, hc, hJ, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp
  · rw [hre, ← posIndex_congr _ hdet, hcn, hJn, posIndex_diagonal, Finset.card_filter, Fintype.sum_sum_type]
    simp

theorem hT_coords {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (u : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = ∑ b, ∑ a, star (u a) * S.gram a b * u b := by
  rw [Module.Basis.equivFun_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, Formalism.BasicNotions.HSpace.gram]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [starRingEnd_apply]
  ring

end GlobalTheory.IsoNegIdx

namespace GlobalTheory.IsoNegIdx

open ReciprocityTheory.ChartRestriction.G GlobalTheory.Inertia

theorem exists_isotropic_of_negIdx : ∀ (D : D7) (S : HSp D) (k : ℕ), NegIdx S k → 1 ≤ k → k + 1 ≤ S.rank → 3 ≤ S.rank →
    ∃ x : S.V, x ≠ 0 ∧ S.hT x x = 0 := by
  intro D S k hS hk1 hk2 hn
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, star x = FD.cc x := fun _ => rfl

  have hsig : ∀ φ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S.gram.map φ) (S.rank - k) k := by
    intro φ
    obtain ⟨ρ, h | h⟩ := GlobalTheory.MassLink.tauE_or' D φ
    · subst h
      simpa [gramAt] using hS ρ
    · have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hS ρ)
      rw [Matrix.map_map] at h1
      have e : (⇑(starRingEnd ℂ) ∘ ⇑(tauE D ρ)) = ⇑φ := by
        funext x
        rw [Function.comp_apply, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [e] at h1

  set G : Matrix (Fin S.rank) (Fin S.rank) D.host.E := S.gram.transpose with hGdef
  have hG : ∀ a b, FD.cc (G a b) = G b a := fun a b => by
    simp only [hGdef, Matrix.transpose_apply, ← hst]
    exact S.herm.eq _ _
  have hform : ∀ u, S.hT (S.frame.equivFun.symm u) (S.frame.equivFun.symm u) = FD.herm G u u := fun u => by
    rw [hT_coords, FD.herm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [hGdef, Matrix.transpose_apply, hst]
    ring
  have hGφ : ∀ φ : D.host.E →+* ℂ, G.map φ = S.gram.map (ComplexEmbedding.conjugate φ) := fun φ => by
    ext a b
    simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq]
    rw [← hG b a, GlobalTheory.Published.embedding_cc]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  have key : ∀ u, FD.herm G (P.mulVec u) (P.mulVec u) = FD.herm (Matrix.diagonal d) u u := fun u => by
    rw [GlobalTheory.Published.LandherrSt.herm_mulVec, hPd]
  have hne : ∀ u, u ≠ 0 → S.frame.equivFun.symm (P.mulVec u) ≠ 0 := fun u hu h => by
    apply hu
    apply Matrix.eq_zero_of_mulVec_eq_zero hP
    have h3 := congrArg S.frame.equivFun h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h3
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨_, hne (Pi.single i 1) (by simp), ?_⟩
    rw [hform, key, GlobalTheory.UTrans.herm_diagonal_self]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Pi.single_apply, hj]
  push_neg at hz

  have hs : ∀ φ : D.host.E →+* ℂ, (∃ i, 0 < (φ (d i)).re) ∧ ∃ j, (φ (d j)).re < 0 := by
    intro φ
    have hc : (P.map φ).transpose * G.map φ * (P.map φ).map (starRingEnd ℂ) = Matrix.diagonal fun i => φ (d i) := by
      have h1 : (P.map φ).map (starRingEnd ℂ) = (P.map FD.cc).map φ := by
        ext a b
        simp [GlobalTheory.Published.embedding_cc]
      rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPd, Matrix.diagonal_map (map_zero φ)]
    have hdet : (P.map φ).det ≠ 0 := by
      have h2 := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h2
      rw [← h2]
      exact (map_ne_zero φ).2 hP
    obtain ⟨hp, hq⟩ := posIndex_of_hasSignature (hGφ φ ▸ hsig (ComplexEmbedding.conjugate φ))
    have hcn : (P.map φ).transpose * (-G.map φ) * (P.map φ).map (starRingEnd ℂ) =
        Matrix.diagonal fun i => -φ (d i) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hc, Matrix.diagonal_neg]
    rw [← posIndex_congr _ hdet, hc, posIndex_diagonal] at hp
    rw [← posIndex_congr _ hdet, hcn, posIndex_diagonal] at hq
    constructor
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hp]; omega)
      exact ⟨i, (Finset.mem_filter.1 hi).2⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < _ by rw [hq]; omega)
      refine ⟨i, ?_⟩
      have := (Finset.mem_filter.1 hi).2
      simp only [Complex.neg_re] at this
      linarith
  obtain ⟨z, hz0, hzz⟩ := GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hz hs
  exact ⟨_, hne z hz0, by rw [hform, key, hzz]⟩

end GlobalTheory.IsoNegIdx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicHermitianSpaceOfNegativeIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_hermitianSpace_of_negativeIndex : ∀ (D : D7) (S : HSp D) (k : ℕ), NegIdx S k → 1 ≤ k → k + 1 ≤ S.rank → 3 ≤ S.rank →
    ∃ x : S.V, x ≠ 0 ∧ S.hT x x = 0 := by
  first | exact @GlobalTheory.IsoNegIdx.exists_isotropic_of_negIdx | exact GlobalTheory.IsoNegIdx.exists_isotropic_of_negIdx | (intros; apply GlobalTheory.IsoNegIdx.exists_isotropic_of_negIdx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneCompl

theorem gram_sum {D : D7} (S : HSp D) (a b : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (a i) * S.gram i j * b j = S.hT (S.frame.equivFun.symm a) (S.frame.equivFun.symm b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply]
  simp only [Finset.mul_sum, RingHom.id_apply]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_compl : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  intro D S Λ x y s hΛ hxx hyy hxy hsplit
  have hyx : S.hT y x = 1 := by rw [← S.herm.eq x y, hxy, map_one]
  let W : Submodule D.host.E S.V := LinearMap.ker (LinearMap.pi fun j : Fin 2 => S.hT (![x, y] j))
  have hW : ∀ w, w ∈ W ↔ S.hT x w = 0 ∧ S.hT y w = 0 := by
    intro w
    simp only [W, LinearMap.mem_ker, funext_iff, LinearMap.pi_apply, Fin.forall_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.zero_apply, Matrix.head_cons]
  have hdec : ∀ z, z - S.hT y z • x - S.hT x z • y ∈ W := by
    intro z
    rw [hW]
    constructor <;> simp [map_sub, hxx, hyy, hxy, hyx]
  have hind : LinearIndependent D.host.E ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (S.hT x) hab
    have h2 := congrArg (S.hT y) hab
    simp [hxx, hyy, hxy, hyx] at h1 h2
    exact ⟨h2, h1⟩
  have hrk : 2 + Module.finrank D.host.E W = S.rank := by
    have := GlobalTheory.WittLow.finrank_orth S.herm S.nondeg ![x, y] hind
    rw [S.rank_eq] at this
    exact this

  have hrad : ∀ v : W, (∀ w : W, S.hT w v = 0) → v = 0 := by
    intro v hv
    have hv' := (hW v).1 v.2
    apply Subtype.ext
    apply S.nondeg.2 (v : S.V)
    intro z
    have e : z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y := by abel
    have h0 := hv ⟨_, hdec z⟩
    rw [e, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, LinearMap.smul_apply, hv'.1, hv'.2, h0]
    simp
  let h' : W →ₗ⋆[D.host.E] W →ₗ[D.host.E] D.host.E := S.hT.domRestrict₁₂ W W
  have hs' : h'.IsSymm := ⟨fun a b => S.herm.eq _ _⟩
  have hnd' : h'.Nondegenerate := ⟨fun a ha => hrad a fun b => by
    rw [← S.herm.eq]; exact (congrArg _ (ha b)).trans (map_zero _), fun a ha => hrad a ha⟩
  let Λ' : Submodule (𝓞 D.host.E) S.V := Λ.comap ((S.frame.equivFun : S.V →ₗ[D.host.E] (Fin S.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hΛ'm : ∀ z, z ∈ Λ' ↔ GlobalTheory.SqStepK.InLat S Λ z := fun z => Iff.rfl
  have hΛ'lat : Submodule.IsLattice D.host.E Λ' := GlobalTheory.ColRows.isLattice_comap_equiv S.frame.equivFun Λ hΛ.1
  have hΛ'd : ∀ z, z ∈ Λ' ↔ ∀ w ∈ Λ', ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT w z := by
    intro z
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, hΛ.2]
    constructor
    · intro h w hw
      obtain ⟨b, hb⟩ := h _ hw
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
    · intro h a ha
      obtain ⟨b, hb⟩ := h (S.frame.equivFun.symm a) (by rw [hΛ'm, GlobalTheory.SqStepK.InLat, LinearEquiv.apply_symm_apply]; exact ha)
      exact ⟨b, by rw [hb, gram_sum]; simp⟩
  let L0 : Submodule (𝓞 D.host.E) W := Λ'.comap (W.subtype.restrictScalars (𝓞 D.host.E))
  have hL0m : ∀ u : W, u ∈ L0 ↔ (u : S.V) ∈ Λ' := fun u => Iff.rfl
  have hL0lat : Submodule.IsLattice D.host.E L0 := GlobalTheory.isLattice_comap_subtype_ringOfIntegers Λ' hΛ'lat W
  have hwz : ∀ z, z ∈ Λ' → z - S.hT y z • x - S.hT x z • y ∈ Λ' := by
    intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z ((hΛ'm z).1 hz)
    rw [hΛ'm, GlobalTheory.SqStepK.InLat, map_sub, map_sub]
    exact Λ.sub_mem (Λ.sub_mem hz hs1) hr1
  have hL0d : ∀ u : W, u ∈ L0 ↔ ∀ u' ∈ L0, ∃ b : 𝓞 D.host.E, (b : D.host.E) = S.hT u' u := by
    intro u
    have hu := (hW u).1 u.2
    rw [hL0m, hΛ'd]
    constructor
    · intro h u' hu'
      exact h _ hu'
    · intro h z hz
      obtain ⟨b, hb⟩ := h ⟨_, hdec z⟩ (hwz z hz)
      refine ⟨b, ?_⟩
      rw [hb]
      simp [map_sub, hu.1, hu.2]
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular h' L0 := by
    ext v
    rw [GlobalTheory.WittLow.mem_dual, hL0d]
    refine forall₂_congr fun u' _ => ?_
    rw [Submodule.mem_one]
    rfl

  let S₁ : HSp D :=
    { V := W, hT := h', herm := hs', nondeg := hnd', rank := Module.finrank D.host.E W, rank_eq := rfl,
      frame := Module.finBasis D.host.E W, sig := s, L0 := L0, standardTuple_isLattice := hL0lat, baseLattice_isUnimodular := hun }
  let e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) ≃ₗ[D.host.E] W := (Module.finBasis D.host.E W).equivFun.symm
  let Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E) :=
    L0.comap ((e₁ : (Fin (Module.finrank D.host.E W) → D.host.E) →ₗ[D.host.E] W).restrictScalars (𝓞 D.host.E))
  have hΛ₁m : ∀ v, v ∈ Λ₁ ↔ e₁ v ∈ L0 := fun v => Iff.rfl
  have hΛ₁lat : Submodule.IsLattice D.host.E Λ₁ := GlobalTheory.ColRows.isLattice_comap_equiv e₁ L0 hL0lat
  have hin : ∀ u : W, GlobalTheory.SqStepK.InLat S₁ Λ₁ u ↔ GlobalTheory.SqStepK.InLat S Λ (W.subtype u) := by
    intro u
    change (Module.finBasis D.host.E W).equivFun u ∈ Λ₁ ↔ _
    rw [hΛ₁m]
    change (Module.finBasis D.host.E W).equivFun.symm ((Module.finBasis D.host.E W).equivFun u) ∈ L0 ↔ _
    rw [LinearEquiv.symm_apply_apply, hL0m, hΛ'm]
    rfl
  refine ⟨S₁, Λ₁, W.subtype, ⟨?_, fun _ _ => rfl, hxx, hyy, hyx, fun u => ⟨((hW u).1 u.2).1, ((hW u).1 u.2).2⟩, hin, ?_⟩, ⟨hΛ₁lat, ?_⟩, rfl⟩
  · change S.rank = Module.finrank D.host.E W + 2
    omega
  · intro z hz
    obtain ⟨hs1, hr1⟩ := hsplit z hz
    refine ⟨S.hT y z, S.hT x z, ⟨_, hdec z⟩, hs1, hr1, (hin _).2 (hwz z hz), ?_⟩
    change z = S.hT y z • x + (z - S.hT y z • x - S.hT x z • y) + S.hT x z • y
    abel
  · intro v
    simp only [gram_sum]
    rw [hΛ₁m, hL0d]
    constructor
    · intro h a ha
      exact h _ ha
    · intro h u' hu'
      have := h (e₁.symm u') (by rw [hΛ₁m, LinearEquiv.apply_symm_apply]; exact hu')
      obtain ⟨b, hb⟩ := this
      refine ⟨b, ?_⟩
      rw [hb]
      change S.hT (e₁ (e₁.symm u') : S.V) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory.PlaneCompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualOrthogonalComplementHyperbolicPlanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x y : S.V)
    (s : (D.host.E →+* ℂ) → ℕ × ℕ), IsSelfDualC S Λ → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y)) →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ IsSelfDualC S₁ Λ₁ ∧ S₁.sig = s := by
  first | exact @GlobalTheory.PlaneCompl.exists_compl | exact GlobalTheory.PlaneCompl.exists_compl | (intros; apply GlobalTheory.PlaneCompl.exists_compl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HypPairSelfDual

theorem exists_partner : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : S.V),
    IsSelfDualC S Λ → x ≠ 0 → S.hT x x = 0 →
    ∃ y : S.V, S.hT y y = 0 ∧ S.hT x y = 1 ∧
      ∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y) := by
  intro D S Λ x hΛ hx0 hxx
  set σ : D.host.E →ₐ[D.host.F] D.host.E := D.sp.cm.sig with hσdef
  have hσs : ∀ e : D.host.E, σ e = star e := fun _ => rfl
  have hσ : ∀ e, σ (σ e) = e := fun e => by rw [hσs, hσs, star_star]
  set J : Matrix (Fin S.rank) (Fin S.rank) D.host.E := Matrix.transpose (HSpace.gram S) with hJ
  set co : S.V ≃ₗ[D.host.E] (Fin S.rank → D.host.E) := S.frame.equivFun with hco

  have hform : ∀ a b : S.V, S.hT a b = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co b) (co a) := fun a b => by
    rw [GlobalTheory.RelFlag.hT_eq_form]
    simp only [GlobalTheory.SgAlg.form, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.IntPair.co, dotProduct, Matrix.mulVec, hJ,
      Matrix.transpose_apply, hσs, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hco]; ring
  have hframe : ∀ i, co (S.frame i) = Pi.single i 1 := fun i => by
    ext j; simp [hco, Module.Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hherm : ∀ i j, σ (J j i) = J i j := fun i j => by
    have h1 := S.herm.eq (S.frame i) (S.frame j)
    have e1 : S.hT (S.frame i) (S.frame j) = J j i := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    have e2 : S.hT (S.frame j) (S.frame i) = J i j := by
      rw [hform, hframe, hframe]
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [e1, e2] at h1
    rw [hσs]; simpa [starRingEnd_apply] using h1
  have hfg : Λ.FG := hΛ.1.fg
  have hdual : ∀ w, w ∈ Λ ↔ ∀ v ∈ Λ, IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v) := fun w => by
    rw [hΛ.2 w]
    refine forall₂_congr fun v _ => ?_
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J w v = ∑ i, ∑ j, star (v i) * S.gram i j * w j := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, hJ, Matrix.transpose_apply, hσs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, ← GlobalTheory.PlaneSplit.mem_range_iff]
    simp [RingHom.mem_range, eq_comm]
  have hfu : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
    haveI := GlobalTheory.HeckeAdjoint.unramified_host D; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified D.host.F D.host.E σ
    (GlobalTheory.AdelicU.isCMExt_host D) hfu
  have hcx0 : co x ≠ 0 := fun h => hx0 (co.injective (by rw [h, map_zero]))
  have hcxx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (co x) (co x) = 0 := by rw [← hform]; exact hxx
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing D.host.F D.host.E σ hσ S.rank J Λ hfg hherm hdual (co x) hcx0
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module D.host.F D.host.E σ S.rank J Λ hfg (co x) ⟨z0, hz0L, hz0⟩
  obtain ⟨y, hyy, hxy, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice D.host.F D.host.E σ hσ S.rank J Λ hherm hdual θ hθ (co x) y₀ hcxx hy₀1 hy₀L
  have hconj : ∀ a b, σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun a b => by
    have hh' : ∀ i j, σ (J i j) = J j i := fun i j => hherm j i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hh']
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨co.symm y, ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [hform, co.apply_symm_apply]; exact hyy
  · rw [hform, co.apply_symm_apply, ← hconj, hxy, map_one]
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform, co.apply_symm_apply]
    exact (hL _ hz).1
  · unfold GlobalTheory.SqStepK.InLat
    rw [map_smul, hform]
    change _ • co (co.symm y) ∈ Λ
    rw [co.apply_symm_apply]
    exact (hL _ hz).2

end GlobalTheory.HypPairSelfDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPartnerSplittingSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolicPartner_splitting_selfDualLattice : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : S.V),
    IsSelfDualC S Λ → x ≠ 0 → S.hT x x = 0 →
    ∃ y : S.V, S.hT y y = 0 ∧ S.hT x y = 1 ∧
      ∀ z, GlobalTheory.SqStepK.InLat S Λ z → GlobalTheory.SqStepK.InLat S Λ (S.hT y z • x) ∧ GlobalTheory.SqStepK.InLat S Λ (S.hT x z • y) := by
  first | exact @GlobalTheory.HypPairSelfDual.exists_partner | exact GlobalTheory.HypPairSelfDual.exists_partner | (intros; apply GlobalTheory.HypPairSelfDual.exists_partner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPred
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPred
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplementSig

open Matrix

theorem hasSignature_plane : Formalism.UG.HasSignature (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp)
    (Matrix.of fun i k => Sum.elim (fun _ => ![1, 1 / 2] i) (fun _ => ![1, -1 / 2] i) k) ?_
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] <;> norm_num

theorem sig : ∀ (D : D7) (S S₁ : HSp D) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) (q : ℕ), S.rank = S₁.rank + 2 →
    Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ u, S.hT x (ι u) = 0 ∧ S.hT y (ι u) = 0) → NegIdx S (q + 1) →
    ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S₁.gram.map τ) (S₁.rank - q) q := by
  intro D S S₁ ι x y q hr hι hxx hyy hxy ho hneg τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have hS : Formalism.UG.HasSignature (S.gram.map τ) (S.rank - (q + 1)) (q + 1) := by
    obtain ⟨ρ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D τ
    · subst hσ
      simpa [gramAt] using hneg ρ
    · subst hσ
      have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hneg ρ)
      rw [Matrix.map_map] at h1
      exact h1
  obtain ⟨⟨a, b⟩, h₁⟩ := GlobalTheory.WittLow.exists_sig S₁ τ
  have c₁ := (Formalism.UG.P.sig_data _ _ _ h₁).1
  have cS := (Formalism.UG.P.sig_data _ _ _ hS).1
  simp only [Fintype.card_fin] at c₁ cS
  let v : Fin S₁.rank ⊕ Fin 2 → S.V := Sum.elim (fun i => ι (S₁.frame i)) ![x, y]
  have hyx : S.hT y x = 1 := by
    have h := S.herm.eq x y
    rw [hxy, map_one] at h
    exact h.symm
  have hv : (Matrix.of fun k l => S.hT (v k) (v l)) =
      fromBlocks S₁.gram 0 0 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E) := by
    ext (i | i) (j | j)
    · simp only [v, Matrix.of_apply, fromBlocks_apply₁₁, Sum.elim_inl, HSpace.gram]; exact hι _ _
    · fin_cases j
      · have h := S.herm.eq x (ι (S₁.frame i))
        rw [(ho _).1, map_zero] at h
        simp [v, ← h]
      · have h := S.herm.eq y (ι (S₁.frame i))
        rw [(ho _).2, map_zero] at h
        simp [v, ← h]
    · fin_cases i
      · simpa [v] using (ho _).1
      · simpa [v] using (ho _).2
    · fin_cases i <;> fin_cases j <;> simp [v, hxx, hyy, hxy, hyx]
  have hF : Formalism.UG.HasSignature ((Matrix.of fun k l => S.hT (v k) (v l)).map τ) (a + 1) (b + 1) := by
    rw [hv, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ)]
    have e : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E).map τ = !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]
    exact GlobalTheory.FrameComplement.hasSignature_fromBlocks h₁ hasSignature_plane
  have key := Formalism.BasicNotions.sig_family S τ hτ v hF hS
  have hb : b = q := by omega
  have ha : a = S₁.rank - q := by omega
  subst hb ha
  exact h₁

end GlobalTheory.PlaneComplementSig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementNegativeIndexPredStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicPlaneComplement_negativeIndex_pred : ∀ (D : D7) (S S₁ : HSp D) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) (q : ℕ), S.rank = S₁.rank + 2 →
    Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ u, S.hT x (ι u) = 0 ∧ S.hT y (ι u) = 0) → NegIdx S (q + 1) →
    ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S₁.gram.map τ) (S₁.rank - q) q := by
  first | exact @GlobalTheory.PlaneComplementSig.sig | exact GlobalTheory.PlaneComplementSig.sig | (intros; apply GlobalTheory.PlaneComplementSig.sig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneSplitSelfDualHermitianComplement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplement

theorem plane_split_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  intro D S Λ q hΛ hneg hq h3
  obtain ⟨x, hx0, hxx⟩ := GlobalTheory.T.exists_isotropic_hermitianSpace_of_negativeIndex D S (q + 1) hneg (by omega) (by omega) h3
  obtain ⟨y, hyy, hxy, hsp⟩ := GlobalTheory.T.exists_hyperbolicPartner_splitting_selfDualLattice D S Λ x hΛ hx0 hxx
  obtain ⟨S₁, Λ₁, ι, hPS, hSD, hs⟩ := GlobalTheory.T.exists_selfDual_orthogonalComplement_hyperbolicPlane D S Λ x y (fun _ => (S.rank - 2 - q, q)) hΛ hxx hyy hxy hsp
  have hrk : S.rank = S₁.rank + 2 := hPS.1
  have hsig := GlobalTheory.T.hyperbolicPlaneComplement_negativeIndex_pred D S S₁ ι x y q hrk hPS.2.1 hxx hyy hxy
    (fun u => ⟨(hPS.2.2.2.2.2.1 u).1, (hPS.2.2.2.2.2.1 u).2⟩) hneg
  have e : S.rank - 2 - q = S₁.rank - q := by omega
  refine ⟨S₁, Λ₁, ι, x, y, hPS, fun τ => ?_, hSD, fun τ => ?_⟩
  · rw [hs]; simp only [e]; exact hsig τ
  · exact hsig _

end GlobalTheory.PlaneComplement

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneSplitSelfDualHermitianComplementStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (q : ℕ),
    IsSelfDualC S Λ → NegIdx S (q + 1) → q + 2 ≤ S.rank → 3 ≤ S.rank →
    ∃ (S₁ : HSp D) (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V),
      GlobalTheory.SqStepK.PlaneSplit S S₁ Λ Λ₁ ι x y ∧ S₁.SigOK ∧ IsSelfDualC S₁ Λ₁ ∧ NegIdx S₁ q := by
  first | exact @GlobalTheory.PlaneComplement.plane_split_complement | exact GlobalTheory.PlaneComplement.plane_split_complement | (intros; apply GlobalTheory.PlaneComplement.plane_split_complement <;> assumption)
end
