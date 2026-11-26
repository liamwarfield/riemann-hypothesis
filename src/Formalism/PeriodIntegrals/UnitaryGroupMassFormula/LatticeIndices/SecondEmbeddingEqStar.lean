module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplitLat
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstRaisingMemEquivariant
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatFreeHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOf
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

section Gen

variable {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]

theorem dual_basis_iff (P : GL n K) (J : Matrix n n K) (z : n → K) :
    (∀ y : n → K, (∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O) → z ⬝ᵥ (J *ᵥ y) ∈ O) ↔
      ∀ i, ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) i ∈ O := by
  have key : ∀ c : n → K, z ⬝ᵥ (J *ᵥ ((P : Matrix n n K) *ᵥ c)) =
      ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) ⬝ᵥ c := by
    intro c
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul]
  have hPP : ∀ c : n → K, ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ ((P : Matrix n n K) *ᵥ c) = c := by
    intro c
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hPP' : ∀ y : n → K, (P : Matrix n n K) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro h i
    have h1 := h ((P : Matrix n n K) *ᵥ Pi.single i 1) (by
      intro j
      rw [hPP]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij])
    rw [key, dotProduct_single_one] at h1
    exact h1
  · intro h y hy
    rw [← hPP' y, key]
    exact sum_mem fun i _ => mul_mem (h i) (hy i)

end Gen

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

abbrev OpX : ValuationSubring (FpX X p) := p.1.adicCompletionIntegers X.B.I.F

def iota1 : X.B.I.E →+* FpX X p := (th1 X p θ).comp (inclR (FpX X p))

def iota2 : X.B.I.E →+* FpX X p := (th2 X p θ).comp (inclR (FpX X p))

def Mlat1 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota1 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def Mlat2 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota2 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def LatSplitP : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (fun j => th1 X p θ (x j)) ∈ Mlat1 X p θ ∧ (fun j => th2 X p θ (x j)) ∈ Mlat2 X p θ

def LatFreeP : Prop :=
  ∃ P : GL (Fin X.B.I.n) (FpX X p), ∀ y, y ∈ Mlat1 X p θ ↔
    ∀ i, (((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *ᵥ y) i ∈ OpX X p

def LatDualP : Prop :=
  ∀ z, z ∈ Mlat2 X p θ ↔ ∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p

theorem latBasis_of (hS : LatSplitP X p θ) (hF : LatFreeP X p θ) (hD : LatDualP X p θ) :
    ∃ P, LatBasis X p θ P := by
  obtain ⟨P, hP⟩ := hF
  refine ⟨P, fun x => ?_⟩
  rw [hS x, hD, hP]
  refine and_congr Iff.rfl ?_
  rw [← dual_basis_iff (OpX X p) P (J1 X p θ)]
  exact ⟨fun h y hy => h y ((hP y).2 hy), fun h y hy => h y ((hP y).1 hy)⟩

theorem latBasisAll_of
    (hS : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatSplitP X p θ)
    (hF : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatFreeP X p θ)
    (hD : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatDualP X p θ) :
    LatBasisAll X p := fun θ hθ => latBasis_of X p θ (hS θ hθ) (hF θ hθ) (hD θ hθ)

end Loc

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGl
noncomputable section

namespace MassDataIdxLatFree

open scoped Matrix
open Module

variable {K : Type} [Field K] (O : ValuationSubring K) [IsPrincipalIdealRing O]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_gl (M : Submodule O (n → K)) (hfg : M.FG)
    (hsp : Submodule.span K (M : Set (n → K)) = ⊤) :
    ∃ P : GL n K, ∀ y, y ∈ M ↔ ∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O := by
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let bM : Module.Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (n → K) := fun i => (bM i : n → K)
  have hliO : LinearIndependent O v := bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliO
  have hsmul : ∀ (r : O) (w : n → K), r • w = (r : K) • w := fun r w => rfl
  have hMsp : (M : Set (n → K)) ⊆ Submodule.span K (Set.range v) := by
    intro y hy
    have h1 := bM.sum_repr ⟨y, hy⟩
    have h2 : y = ∑ i, (bM.repr ⟨y, hy⟩ i : K) • v i := by
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      rfl
    rw [h2]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hsp]
    exact Submodule.span_le.mpr hMsp
  let bK : Module.Basis ι K (n → K) := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have hcard : Fintype.card ι = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fintype_fun_eq_card]
  let e : ι ≃ n := Fintype.equivOfCardEq hcard
  let Pm : Matrix n n K := fun i j => bK (e.symm j) i
  let Qm : Matrix n n K := fun i j => bK.repr (Pi.single j 1) (e.symm i)
  have hQ : ∀ y : n → K, Qm *ᵥ y = fun i => bK.repr y (e.symm i) := by
    intro y
    funext i
    have hy : y = ∑ j, y j • (Pi.single j (1 : K) : n → K) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Qm]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hQP : Qm * Pm = 1 := by
    ext i k
    have h1 := congrFun (hQ (fun j => Pm j k)) i
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    have h2 : (fun j => Pm j k) = bK (e.symm k) := rfl
    rw [h2, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    simp [e.symm.injective.eq_iff, eq_comm]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.mp hQP
  refine ⟨(⟨Pm, Qm, hPQ, hQP⟩ : GL n K), fun y => ?_⟩
  show y ∈ M ↔ ∀ i, (Qm *ᵥ y) i ∈ O
  rw [hQ]
  constructor
  · intro hy i
    have h2 : y = ∑ j, (bM.repr ⟨y, hy⟩ j : K) • bK j := by
      have h1 := bM.sum_repr ⟨y, hy⟩
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      exact Finset.sum_congr rfl (fun j _ => by rw [hbK]; rfl)
    have h4 : bK.repr y (e.symm i) = (bM.repr ⟨y, hy⟩ (e.symm i) : K) := by
      conv_lhs => rw [h2]
      simp [Module.Basis.repr_self, Finsupp.single_apply]
    show bK.repr y (e.symm i) ∈ O
    rw [h4]
    exact (bM.repr ⟨y, hy⟩ (e.symm i)).2
  · intro hc
    have hc' : ∀ j, bK.repr y j ∈ O := by
      intro j
      have := hc (e j)
      simpa using this
    rw [← bK.sum_repr y]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have h5 : bK.repr y j • bK j = (⟨bK.repr y j, hc' j⟩ : O) • (bM j : n → K) := by
      rw [hsmul, hbK]
    rw [h5]
    exact M.smul_mem _ (bM j).2

end MassDataIdxLatFree
end
end

noncomputable section

namespace MassDataIdxLatFree

open NumberField

variable {E K : Type} [Field E] [NumberField E] [Field K] (O : ValuationSubring K) (ι : E →+* K)
  {n : Type} [Fintype n] [DecidableEq n]

theorem int_mem (a : 𝓞 E) : ι (a : E) ∈ O := by
  have h1 : IsIntegral ℤ (ι (a : E)) := (RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom
  have h2 : IsIntegral O (ι (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

def Mι (L : Submodule (𝓞 E) (n → E)) : Submodule O (n → K) :=
  Submodule.span O ((fun l : n → E => fun j => ι (l j)) '' (L : Set (n → E)))

theorem fg (L : Submodule (𝓞 E) (n → E)) (hL : L.FG) : (Mι O ι L).FG := by
  classical
  obtain ⟨S, hS⟩ := hL
  refine ⟨S.image (fun l : n → E => fun j => ι (l j)), ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.2
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
    exact Submodule.subset_span ⟨l, hS ▸ Submodule.subset_span hl, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    rw [← hS] at hl
    induction hl using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
    | zero =>
        have : (fun j => ι ((0 : n → E) j)) = 0 := by funext j; simp
        beta_reduce; rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
        have : (fun j => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
          funext j; simp
        beta_reduce; rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        have : (fun j => ι ((a • x) j)) = (⟨ι (a : E), int_mem O ι a⟩ : O) • (fun j => ι (x j)) := by
          funext j
          simp [Algebra.smul_def]
        beta_reduce; rw [this]; exact Submodule.smul_mem _ _ hx

theorem span_top (L : Submodule (𝓞 E) (n → E)) (hL : Submodule.span E (L : Set (n → E)) = ⊤) :
    Submodule.span K (Mι O ι L : Set (n → K)) = ⊤ :=
  by apply _root_.UpperTheory.Reformulated.B.SpanTopFamily.span_top <;> assumption

end MassDataIdxLatFree

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting

theorem latFree_holds {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    LatFreeP X p θ :=
  MassDataIdxLatFree.exists_gl (OpX X p) (Mlat1 X p θ)
    (MassDataIdxLatFree.fg (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_fg)
    (MassDataIdxLatFree.span_top (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_span)

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

def UnitElt : Prop :=
  ∃ a : 𝓞 X.B.I.E, ∃ w ∈ OpX X p, w * (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E)) = 1

theorem firstSplitCoord_smul (c : FpX X p) (t : TpX X p) : th1 X p θ (c • t) = c * th1 X p θ t := by
  show (θ (c • t)).1 = c * (θ t).1
  rw [map_smul]
  rfl

theorem secondSplitCoord_smul (c : FpX X p) (t : TpX X p) : th2 X p θ (c • t) = c * th2 X p θ t := by
  show (θ (c • t)).2 = c * (θ t).2
  rw [map_smul]
  rfl

theorem osmul_eq (c : OpX X p) (t : TpX X p) : c • t = (c : FpX X p) • t := rfl

theorem th_incl (e : X.B.I.E) : θ (inclR (FpX X p) e) = (iota1 X p θ e, iota2 X p θ e) := rfl

theorem first_raising_mem_equivariant (h : UnitElt X p θ) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    (fun j => θ.symm (iota1 X p θ (l j), 0)) ∈
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  obtain ⟨a, w, hw, hwa⟩ := h
  have hc2 : iota2 X p θ (a : X.B.I.E) ∈ OpX X p := MassDataIdxLatFree.int_mem (OpX X p) (iota2 X p θ) a
  have heq : (fun j => θ.symm (iota1 X p θ (l j), 0)) =
      (⟨w, hw⟩ : OpX X p) • (ratV (F := X.B.I.F) (FpX X p) (a • l) -
        (⟨iota2 X p θ (a : X.B.I.E), hc2⟩ : OpX X p) • ratV (F := X.B.I.F) (FpX X p) l) := by
    funext j
    apply θ.injective
    rw [AlgEquiv.apply_symm_apply]
    show _ = θ ((w : FpX X p) • (inclR (FpX X p) ((a : X.B.I.E) * l j) -
      (iota2 X p θ (a : X.B.I.E)) • inclR (FpX X p) (l j)))
    rw [map_smul, map_sub, map_smul, map_mul, map_mul]
    simp only [th_incl]
    refine Prod.ext ?_ ?_
    · show iota1 X p θ (l j) = w * (iota1 X p θ (a : X.B.I.E) * iota1 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota1 X p θ (l j))
      linear_combination (-(iota1 X p θ (l j))) * hwa
    · show (0 : FpX X p) = w * (iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j) -
        iota2 X p θ (a : X.B.I.E) * iota2 X p θ (l j))
      ring
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
  · exact Submodule.subset_span ⟨a • l, X.B.I.L.smul_mem a hl, rfl⟩
  · exact Submodule.subset_span ⟨l, hl, rfl⟩

theorem firstLattice_mem_local (h : UnitElt X p θ) (y : Fin X.B.I.n → FpX X p) (hy : y ∈ Mlat1 X p θ) :
    (fun j => θ.symm (y j, 0)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact first_raising_mem_equivariant X p θ h l hl
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1 <;> funext j <;> simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, add_zero]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply, osmul_eq X p]
    rw [← map_smul, Prod.smul_mk, smul_zero]
    rfl

theorem secondLattice_mem_local (h : UnitElt X p θ) (z : Fin X.B.I.n → FpX X p) (hz : z ∈ Mlat2 X p θ) :
    (fun j => θ.symm (0, z j)) ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, hl, rfl⟩ := hz
    have h1 := first_raising_mem_equivariant X p θ h l hl
    have h2 : ratV (F := X.B.I.F) (FpX X p) l ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    convert Submodule.sub_mem _ h2 h1 using 1
    funext j
    apply θ.injective
    change θ (θ.symm (0, iota2 X p θ (l j))) = θ (inclR (FpX X p) (l j) - θ.symm (iota1 X p θ (l j), 0))
    rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, th_incl]
    ext <;> simp
  | zero =>
    convert Submodule.zero_mem (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) using 1 <;> funext j <;> simp
  | add y y' _ _ hy hy' =>
    convert Submodule.add_mem _ hy hy' using 1
    funext j
    simp only [Pi.add_apply]
    rw [← map_add, Prod.mk_add_mk, zero_add]
  | smul c y _ hy =>
    convert Submodule.smul_mem _ c hy using 1
    funext j
    simp only [Pi.smul_apply, osmul_eq X p]
    rw [← map_smul, Prod.smul_mk, smul_zero]
    rfl

theorem latSplit_of (h : UnitElt X p θ) : LatSplitP X p θ := by
  unfold LatSplitP
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.subset_span ⟨l, hl, rfl⟩⟩
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _)]
      exact ⟨Submodule.add_mem _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩
    | smul c x _ hx =>
      simp only [Pi.smul_apply, osmul_eq X p, firstSplitCoord_smul, secondSplitCoord_smul]
      exact ⟨Submodule.smul_mem _ c hx.1, Submodule.smul_mem _ c hx.2⟩
  · rintro ⟨h1, h2⟩
    have hx : x = (fun j => θ.symm (th1 X p θ (x j), 0)) + (fun j => θ.symm (0, th2 X p θ (x j))) := by
      funext j
      simp only [Pi.add_apply]
      rw [← map_add (f := _), Prod.mk_add_mk, add_zero, zero_add]
      apply θ.injective
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [hx]
    exact Submodule.add_mem _ (firstLattice_mem_local X p θ h _ h1) (secondLattice_mem_local X p θ h _ h2)

end Loc

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem sigR_incl (e : X.B.I.E) :
    sigR (FpX X p) X.B.I.cm.sig (inclR (FpX X p) e) = inclR (FpX X p) (star e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rfl

theorem secondEmbedding_eq_star (hθ : IsSplitEquiv X p θ) (e : X.B.I.E) : iota2 X p θ e = iota1 X p θ (star e) := by
  have h := hθ (inclR (FpX X p) e)
  rw [sigR_incl, th_incl, th_incl] at h
  have h1 := congrArg Prod.fst h
  simp only [Prod.fst_swap] at h1
  exact h1.symm

theorem unitElt_holds (hθ : IsSplitEquiv X p θ) : UnitElt X p θ := by
  classical
  have hint : ∀ o : 𝓞 X.B.I.E, Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E o)) ≤ 1 := by
    intro o
    have h0 : IsIntegral ℤ (algebraMap (𝓞 X.B.I.E) X.B.I.E o) := RingOfIntegers.isIntegral_coe o
    exact (Valuation.mem_integer_iff _ _).1
      (Valuation.Integers.mem_of_integral (Valuation.integer.integers _)
        (IsIntegral.map_of_comp_eq (Int.castRingHom _) (iota1 X p θ) (RingHom.ext_int _ _) h0))
  have halg : ∀ f : X.B.I.F,
      iota1 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
    intro f
    show (θ (Algebra.TensorProduct.includeRight (algebraMap X.B.I.F X.B.I.E f))).1 = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply X.B.I.F (FpX X p) (TpX X p),
      AlgEquiv.commutes]
    rfl
  let P : Ideal (𝓞 X.B.I.E) :=
    { carrier := {x | Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add (f := _)] at hx hy ⊢
        exact Valuation.map_add_lt _ hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx }
  have hmemP : ∀ x, x ∈ P ↔ Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) < 1 :=
    fun x => Iff.rfl
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : 𝓞 X.B.I.E) ∈ P := by rw [htop]; exact Submodule.mem_top
      rw [hmemP] at h1
      simp at h1
    · intro x y hxy
      rw [hmemP, map_mul, map_mul, Valuation.map_mul] at hxy
      by_contra hn
      rw [not_or, hmemP, hmemP, not_lt, not_lt] at hn
      exact absurd hxy (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  have hPne : P ≠ ⊥ := by
    obtain ⟨f, hfp, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.1.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) f ∈ P := by
      rw [hmemP, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, halg,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hfp
    rw [hbot, Ideal.mem_bot] at hmem
    apply hf0
    first
    | exact (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (by rw [hmem, map_zero])
    | exact (NoZeroSMulDivisors.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (by rw [hmem, map_zero])
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPne
  obtain ⟨a, t, ht, hat⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
  rw [hmemP, not_lt] at hat
  have hv1 : Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E (a - t))) = 1 :=
    le_antisymm (hint _) hat
  have hdeq : iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E) =
      iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E (a - t)) := by
    rw [secondEmbedding_eq_star X p θ hθ, map_sub, map_sub, ht]
  have hv : Valued.v (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E)) = 1 := by
    rw [hdeq]
    exact hv1
  have hd0 : iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  refine ⟨a, (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E))⁻¹, ?_, inv_mul_cancel₀ hd0⟩
  rw [OpX, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]

theorem herm_entry (i j : Fin X.B.I.n) : star (X.B.I.J i j) = X.B.I.J j i := by
  have h : Formalism.UG.cT (starRingEnd X.B.I.E) X.B.I.J = X.B.I.J := X.B.I.J_herm
  have h2 := congrFun (congrFun h j) i
  simpa only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply] using h2

theorem firstForm_apply (a b : Fin X.B.I.n) : J1 X p θ a b = iota1 X p θ (X.B.I.J a b) := rfl

open scoped Matrix in
theorem dual_gen (hθ : IsSplitEquiv X p θ) (l l' : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L)
    (hl' : l' ∈ X.B.I.L) :
    (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) ∈ OpX X p := by
  have hint : ∀ o : 𝓞 X.B.I.E, iota1 X p θ (o : X.B.I.E) ∈ OpX X p := by
    intro o
    rw [OpX, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have h0 : IsIntegral ℤ ((o : X.B.I.E)) := RingOfIntegers.isIntegral_coe o
    exact (Valuation.mem_integer_iff _ _).1
      (Valuation.Integers.mem_of_integral (Valuation.integer.integers _)
        (IsIntegral.map_of_comp_eq (Int.castRingHom _) (iota1 X p θ) (RingHom.ext_int _ _) h0))
  obtain ⟨o, ho⟩ := (X.B.I.L_dual l).1 hl l' hl'
  have key : (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) =
      iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l' l) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply,
      secondEmbedding_eq_star X p θ hθ, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key, ← ho]
  exact hint o

end Loc

end MassDataIdxSteps
