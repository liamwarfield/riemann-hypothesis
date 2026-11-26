module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFormalGroupLawOfChartOfJetChart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemSupSpanXPowIffAndIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTranspose
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CoeffActAdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddCurve

section Rings
variable (R : Type) [CommRing R] (l : ℕ)

abbrev Tr : Type := AdjoinRoot (Polynomial.X ^ l : Polynomial R)

variable {R l}

def cf (n : ℕ) : Tr R l →ₗ[R] R := (Polynomial.lcoeff R n).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow l))

variable (R l)

end Rings

section Points
variable {k : Type} [CommRing k]

variable {B : Over (Spec (CommRingCat.of k))}

variable {R : Type} [CommRing R] [Algebra k R]

end Points

end GlobalTheory.AddCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupSeriesSeparatedByTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupSeriesSeparatedByTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem mem_span_of_killed {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (N : ℕ)
    (h : ∀ q : QF F N, (∀ φ : QF F N →ₐ[R] R, φ q = 0) → q = 0) (f : PS R 1 d)
    (hf : ∀ φ, Killed F N φ → φ f = 0) : f ∈ Ideal.span (Set.range (mulF F N)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine h _ fun φ => ?_
  refine hf (φ.comp (Ideal.Quotient.mkₐ R _)) fun j => ?_
  have : Ideal.Quotient.mk (Ideal.span (Set.range (mulF F N))) (mulF F N j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  simp [this]

theorem mem_span_mulF_of_killed_and_eq_zero_of_tors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hc d F hFH
  have h1 : ∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) →
      f ∈ Ideal.span (Set.range (mulF F.F (p ^ k))) :=
    fun k f hf => mem_span_of_killed F.F (p ^ k) (hFH k).2.2 f hf
  refine ⟨h1, fun f hf => ?_⟩
  have hH := ((mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2
    hc).toIsHausdorff
  refine hH.haus f fun k => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  refine (Ideal.span_le.2 ?_) (h1 k f fun φ hφ => hf φ ⟨k, hφ⟩)
  rintro _ ⟨j, rfl⟩
  exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow O d F).2.2.2 p k j

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupSeriesSeparatedByTorsionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_series_separated_by_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  first | exact @GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors | exact GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors | (intros; apply GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSum
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSum
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem td_mem {C OE κ : Type} [Field C] [CommRing OE] [Fintype κ] [DecidableEq κ]
    (ρ : OE → Matrix κ κ C) (τ : OE →+* C) (x : κ → C) :
    x ∈ (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap C C))) (τ a)) ↔
      ∀ a, ρ a *ᵥ x = τ a • x := by
  simp [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

private theorem td_reindex {C OE κ κ' : Type} [Field C] [CommRing OE] [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ'] (e : κ' ≃ κ) (ρ : OE → Matrix κ κ C) (τ : OE →+* C) :
    eigDim C (fun a => (ρ a).submatrix e e) τ = eigDim C ρ τ := by
  unfold eigDim
  rw [← LinearEquiv.finrank_map_eq (LinearEquiv.funCongrLeft C C e)
    (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap C C))) (τ a))]
  refine congrArg (fun S : Submodule C _ => Module.finrank C ↥S) ?_
  ext x
  rw [Submodule.mem_map_equiv, td_mem (fun a => (ρ a).submatrix e e), td_mem ρ]
  refine forall_congr' fun a => ?_
  rw [Matrix.submatrix_mulVec_equiv]
  have hx : (LinearEquiv.funCongrLeft C C e).symm x = x ∘ e.symm := by
    ext i; simp
  rw [hx]
  constructor
  · intro h
    ext i
    have := congrFun h (e.symm i)
    simpa using this
  · intro h
    ext i
    have := congrFun h (e i)
    simpa using this

private theorem td_base {C O OE κ : Type} [Field C] [CommRing O] [Algebra O C] [CommRing OE] [Fintype κ]
    [DecidableEq κ] (ρ : OE → Matrix κ κ O) (τ : OE →+* C) :
    eigDim C ρ τ = eigDim C (fun a => (ρ a).map (algebraMap O C)) τ := by
  rfl

private theorem td_twist {C OE κ : Type} [Field C] [CommRing OE] [Fintype κ]
    [DecidableEq κ] (ρ : OE → Matrix κ κ C) (τ : OE →+* C) (s : OE →+* OE) (hs : ∀ a, s (s a) = a) :
    eigDim C (fun a => ρ (s a)) τ = eigDim C ρ (τ.comp s) := by
  unfold eigDim
  refine congrArg (fun S : Submodule C _ => Module.finrank C ↥S) ?_
  ext x
  rw [td_mem (fun a => ρ (s a)), td_mem ρ]
  constructor
  · intro h a
    have := h (s a)
    rw [hs] at this
    simpa using this
  · intro h a
    have := h (s a)
    simpa [hs] using this

private theorem td_field {C OE : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] {g : ℕ}
    (ρ : OE →+* Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C) (L : OE →+* Matrix (Fin g) (Fin g) C)
    (s : OE →+* OE) (hs : ∀ a, s (s a) = a) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C)
    (hE : IsUnit E.det) (hinv : ∀ a, (ρ a)ᵀ * E = E * ρ (s a))
    (H B : Matrix (Fin g) (Fin g ⊕ Fin g) C) (hH : ∀ a, H * ρ a = (L (s a))ᵀ * H) (c : C) (hc : c ≠ 0)
    (hform : Bᵀ * H - Hᵀ * B = c • E) (τ : OE →+* C) :
    eigDim C ρ τ = eigDim C L τ + eigDim C L (τ.comp s) := by
  set A : Matrix (Fin g ⊕ Fin g) (Fin g) C := E⁻¹ * Hᵀ with hA
  set A' : Matrix (Fin g) (Fin g ⊕ Fin g) C := (-c⁻¹) • B with hA'
  set B' : Matrix (Fin g ⊕ Fin g) (Fin g) C := c⁻¹ • (E⁻¹ * Bᵀ) with hB'
  have h1 : A * A' + B' * H = 1 := by
    have : A * A' + B' * H = c⁻¹ • (E⁻¹ * (Bᵀ * H - Hᵀ * B)) := by
      simp only [hA, hA', hB', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_sub, smul_sub,
        neg_smul, Matrix.mul_neg]
      abel
    rw [this, hform, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hE, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : Matrix.fromRows A' H * Matrix.fromCols A B' = 1 := by
    rw [← Matrix.fromCols_mul_fromRows_eq_one_comm (Equiv.refl _), Matrix.fromCols_mul_fromRows, h1]
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  obtain ⟨h21, -, h23, h24⟩ := h2
  have hρA : ∀ a, ρ a * A = A * L a := by
    intro a
    have e1 : ρ a * E⁻¹ = E⁻¹ * (ρ (s a))ᵀ := by
      have := hinv (s a)
      rw [hs] at this
      calc ρ a * E⁻¹ = E⁻¹ * (E * ρ a) * E⁻¹ := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hE, Matrix.one_mul]
        _ = E⁻¹ * (ρ (s a))ᵀ * (E * E⁻¹) := by rw [← this]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]
    have e2 := congrArg Matrix.transpose (hH (s a))
    rw [hs, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at e2
    rw [hA, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, e2, Matrix.mul_assoc]
  let e : Fin (g + g) ≃ Fin g ⊕ Fin g := finSumFinEquiv.symm
  let ρ' : OE →+* Matrix (Fin (g + g)) (Fin (g + g)) C :=
    (Matrix.reindexAlgEquiv C C e.symm).toRingEquiv.toRingHom.comp ρ
  have hρ' : ∀ a, ρ' a = (ρ a).submatrix e e := fun a => rfl
  let LT : OE →+* Matrix (Fin g) (Fin g) C :=
    { toFun := fun a => (L (s a))ᵀ
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_comm a b, map_mul, map_mul, Matrix.transpose_mul]
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hsp : SplitEx (A.submatrix e id) (H.submatrix id e) := by
    refine ⟨?_, A'.submatrix id e, B'.submatrix e id, ?_, ?_, ?_⟩
    · rw [Matrix.submatrix_mul_equiv, h23]; simp
    · rw [Matrix.submatrix_mul_equiv, h21]; simp
    · rw [Matrix.submatrix_mul_equiv, h24]; simp
    · rw [← Matrix.submatrix_one_equiv e, ← h1]
      ext i j
      simp [Matrix.mul_apply]
  have k1 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C C OE (g + g) g g _ _ hsp ρ' L LT
    (fun a => by
      rw [hρ', Matrix.submatrix_mul_equiv, hH]
      ext i j
      simp [Matrix.mul_apply, LT])
    (fun a => by
      rw [hρ', Matrix.submatrix_mul_equiv, hρA]
      ext i j
      simp [Matrix.mul_apply]) τ).1
  let Z : OE →+* Matrix (Fin 0) (Fin 0) C :=
    { toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _ }
  have k2 := (GlobalTheory.T.eigenspaceDim_add_split_exact_transpose C C OE g g 0 _ _ (splitEx_one g) (L.comp s) (L.comp s) Z
    (fun a => Subsingleton.elim _ _) (fun a => by simp) τ).2
  have k3 : eigDim C ρ' τ = eigDim C ρ τ := td_reindex e ρ τ
  have k4 : eigDim C LT τ = eigDim C L (τ.comp s) := k2.trans (td_twist L τ s hs)
  rw [← k3, k1, k4]

theorem eigDim_tate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (τ : OE →+* C), eigDim C (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) τ = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ + eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hU g H τ
  let j : OE →+* ℤ_[p] ⊗[ℤ] OE := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  let f : ℤ_[p] →+* C := (algebraMap O C).comp (algebraMap ℤ_[p] O)
  let s : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hs : ∀ a, s (s a) = a := fun a => star_star a
  have hj : ∀ a, sigE p OE (j a) = j (s a) := fun a => rfl
  let ρ : OE →+* Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) C := (f.mapMatrix.comp H.ρ.toRingHom).comp j
  let L : OE →+* Matrix (Fin g) (Fin g) C := ((algebraMap O C).mapMatrix.comp H.ρL).comp j
  have hρ : ∀ a, ρ a = (H.ρ (j a)).map f := fun a => rfl
  have hL : ∀ a, L a = (H.ρL (j a)).map (algebraMap O C) := fun a => rfl
  have hc : algebraMap O C cp ≠ 0 := by
    intro h
    have h1 := hU.cp_val
    have h2 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    rw [h, map_zero, zero_pow h2] at h1
    exact hU.p_ne h1.symm
  have key := td_field ρ L s hs (H.E.map f)
    (by
      have := H.isUnit_det_E.map f
      rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this)
    (fun a => by
      rw [hρ, hρ, ← hj, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant])
    (H.Ht.map (algebraMap O C)) (H.Bt.map (algebraMap O C))
    (fun a => by
      have := congrArg (fun M => M.map (algebraMap O C)) (H.Ht_equivariant.1 (j a))
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      rw [hρ, hL, ← hj, ← this]
      rfl)
    (algebraMap O C cp) hc
    (by
      have := congrArg (fun M => M.map (algebraMap O C)) H.form_eq_alt
      simp only [Matrix.map_sub _ (map_sub (algebraMap O C)), Matrix.map_mul, Matrix.transpose_map] at this
      rw [this]
      ext i k
      simp [f]) τ
  rw [td_base, td_base (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ, td_base (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a))]
  exact key

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSumStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_eigenspace_dim_eq_lieAlgebra_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (τ : OE →+* C), eigDim C (fun a : OE => (H.ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) τ = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) τ + eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) := by
  first | exact @GlobalTheory.ChF.eigDim_tate | exact GlobalTheory.ChF.eigDim_tate | (intros; apply GlobalTheory.ChF.eigDim_tate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndomorphismPairW0
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndomorphismPairW0
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit GlobalTheory.ActionEnd

namespace GlobalTheory.ActionEndSelf

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)


include hlg hex hh in
theorem isEnd_act_raw (a : O) : IsEnd X V (dLin (Y.B.A.act a)) (dLin (Y.B.A.act (star a))) := by
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine isEnd_of_hom_raw Y X hlg hex hh _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
  have h := Y.gauge.ad a
  rw [actK_self, actK_self] at h
  rw [← h]
  have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
    show MvPowerSeries.map (RingHom.id C) _ = _
    rw [MvPowerSeries.map_id]; rfl
  rw [e]
  exact Y.intAd a


include hlg hex hh in
theorem gauge_at_linearPart_action_eq_hermitianLift (a : O) : un1 (Y.B.hL C Y.h a) =
    hAt X (endP X 1 (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C))
      (endP X (dLin (Y.B.A.act a)) (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C)) := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
  have hs : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
  have e1 := matrixEnd_eq_subst' Y X hlg hex (pt C dd 0) q0 (by
    rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
  rw [germLinearPart_coordinatePoint_zero] at e1
  have e2 := matrixEnd_eq_subst' Y X hlg hex _ (g a) (Y.B.A.hom a) _ hX
  have e3 : comp1 (Y.B.A.act a) (pt C dd (0 : Fin 1)) = Y.B.A.act a := by
    funext i
    rw [germComp1_eq_subst]
    have : (fun q : Fin 1 × Fin dd => pt C dd (0 : Fin 1) q.2) = MvPowerSeries.X := by
      funext ⟨s, x⟩
      obtain rfl : s = 0 := Subsingleton.elim _ _
      rfl
    rw [this, MvPowerSeries.subst_self]; rfl
  have e4 : un1 (Y.B.hL C Y.h a) = MvPowerSeries.subst
      (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) (Y.B.hL C Y.h a) := by
    rw [← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]; rfl
  rw [e4, FB.hL, actK_self, e3, ev, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 2 × Fin dd => pair_points_zero_constant q0 (g a) q.1 q.2) hs,
    hAt, hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s
  · exact (e1 x).symm
  · exact (e2 x).symm

theorem linear_parts_w0_sum_one : dLin (Y.B.A.act Y.w0) + dLin (Y.B.A.act (star Y.w0)) = 1 := by
  rw [← germLinearPart_coordinatePoint_zero, ← Y.B.A.one_act, ← Y.halfIntegralGenerator_add_conj_eq_one]
  ext i j
  exact (Nab.coeff_act_add Y.B _ _ i j).symm

end Chart

theorem exists_endomorphism_w0 : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∃ W W' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf p) V W W' ∧ W + W' = 1 ∧ (∀ (v : Fin 2 × Fin dd → C) (x : Fin 2 × Fin dd), W.mulVec v x = linAct (Y.B.A.act Y.w0) (fun i => v (x.1, i)) x.2) ∧ ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)) = hEnd (Y.rawSelf p) 1 W := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  let X : RawChart C d (fun _ => I0) (Fin dd) :=
    { lg := fun i => un1 (Y.lg i), ex := fun i => un1 (Y.ex i), h := Y.h, k := 0, u := fun _ => p.e,
      ty := fun _ => p.ty0, n := 0, j := 0, j' := 0, big := fun _ _ => True }
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp)]
    simp
  have hex : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  have hh : MvPowerSeries.constantCoeff X.h = 0 := by
    have := coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl (by
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' _ _ hg']
      rfl) Y.gauge.ax0 0 (by simp)
    simpa using this
  have blk : ∀ M M' : Matrix (Fin dd) (Fin dd) C, M + M' = 1 →
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M x.2 y.2 else 0) +
        (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M' x.2 y.2 else 0) = 1 := by
    intro M M' h
    ext ⟨a, i⟩ ⟨b, j⟩
    have := congrFun (congrFun h i) j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Prod.mk.injEq] at this ⊢
    by_cases hab : a = b
    · simp [hab, this]
    · simp [hab]
  have hone : (1 : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C) =
      fun x y => if x.1 = y.1 then (1 : Matrix (Fin dd) (Fin dd) C) x.2 y.2 else 0 := by
    rw [← blk 1 0 (add_zero _)]
    ext x y
    simp
  refine ⟨_, _, teichSelf_double C V dd d d _ _ X (Y.rawSelf p) hlg hex hh rfl rfl rfl _ _
    (isEnd_act_raw Y X rfl rfl rfl Y.w0), blk _ _ (linear_parts_w0_sum_one Y), fun v x => ?_, ?_⟩
  · show _ = (dLin (Y.B.A.act Y.w0)).mulVec (fun i => v (x.1, i)) x.2
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
      fun i => by simp
    have hX' : ∀ i : Fin 2 × Fin dd,
        MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun i => by simp
    have hlg' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).lg i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hlg _)
    have hex' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).ex i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hex _)
    unfold hEnd
    rw [hone]
    refine Eq.trans ?_ (teichSelf_hAt_col X (Y.rawSelf p) rfl _ _ (teichSelf_cc_endP _ hlg' hex' _ _ hX')
      (teichSelf_cc_endP _ hlg' hex' _ _ hX')).symm
    refine Finset.sum_congr rfl fun col _ => ?_
    have c : ∀ y : Fin dd, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (col, y) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun _ => hX' _
    rw [gauge_at_linearPart_action_eq_hermitianLift Y X rfl rfl rfl, inCol, teichSelf_subst_hAt X _ _ (teichSelf_cc_endP X hlg hex _ _ hX)
      (teichSelf_cc_endP X hlg hex _ _ hX) _ c]
    simp only [teichSelf_subst_endP X hlg _ _ hX _ c,
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero c)]
    congr 1 <;> funext y <;> exact (teichSelf_endP_col X (Y.rawSelf p) hlg rfl rfl _ _ hX' (col, y)).symm

end GlobalTheory.ActionEndSelf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndomorphismPairW0Statement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endomorphism_pair_w0 : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∃ W W' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf p) V W W' ∧ W + W' = 1 ∧ (∀ (v : Fin 2 × Fin dd → C) (x : Fin 2 × Fin dd), W.mulVec v x = linAct (Y.B.A.act Y.w0) (fun i => v (x.1, i)) x.2) ∧ ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)) = hEnd (Y.rawSelf p) 1 W := by
  first | exact @GlobalTheory.ActionEndSelf.exists_endomorphism_w0 | exact GlobalTheory.ActionEndSelf.exists_endomorphism_w0 | (intros; apply GlobalTheory.ActionEndSelf.exists_endomorphism_w0 <;> assumption)
end
end
