module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVacuumFinitePlacesRationalDarboux
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulBlockUnitaryDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.BCT.GlobLev GlobalTheory.SplitPts GroundTheory.Automorphic Topology

noncomputable section

namespace GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_one_entry {R : Type} [Ring R] (f : Ad E →+* R) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem sub_one_entry_mem {w : Pl E} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ w.adicCompletionIntegers E := by
  rw [mem_KGL_iff_val] at hg
  refine sub_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hg.1 i j)) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _


omit [IsCMField E] in
theorem af_ext {a b : Af E} (h : ∀ u : Pl E, pLoc E u a = pLoc E u b) : a = b := Subtype.ext (funext h)

omit [IsCMField E] in
theorem pLoc_singleNU_self (w : Pl E) (y : w.adicCompletion E) : pLoc E w (GlobalTheory.GLTwoHecke.singleNU w y) = y :=
  GlobalTheory.AdelicU.evalV_singleFin_self w y

omit [IsCMField E] in
theorem pLoc_singleNU_ne {u w : Pl E} (h : u ≠ w) (y : w.adicCompletion E) :
    pLoc E u (GlobalTheory.GLTwoHecke.singleNU w y) = 0 :=
  GlobalTheory.AdelicU.evalV_singleFin_ne h y

theorem entry_eq_one_add {w : Pl E} {N N' : Set (Af E)} (h0 : (0 : Af E) ∈ N')
    (hadd : ∀ a ∈ N', ∀ b ∈ N', a + b ∈ N)
    (hw : ∀ y ∈ w.adicCompletionIntegers E, GlobalTheory.GLTwoHecke.singleNU w y ∈ N')
    (hc : ∀ y ∈ (conjSrc (conjE E) w).adicCompletionIntegers E,
      GlobalTheory.GLTwoHecke.singleNU (conjSrc (conjE E) w) y ∈ N')
    (z : UA E n) (hz : z ∈ locU n w) (hK : cLoc w z ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    ∃ a ∈ N, ((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + (show Ad E from ((0 : InfiniteAdeleRing E), a)) := by
  have hKc := integral_conjSrc z w hK
  have hfin : z ∈ finU (E := E) (n := n) := (Subgroup.mem_inf.1 hz).1
  have hout : ∀ u : Pl E, u ≠ w → u ≠ conjSrc (conjE E) w → cLoc u z = 1 := by
    intro u huw huc
    have hne : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := fun h =>
      (eq_or_eq_conjSrc h).elim huw huc
    exact (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hz).2 u) hne)
  generalize conjSrc (conjE E) w = c at hc hKc hout
  refine ⟨GlobalTheory.GLTwoHecke.singleNU w ((cLoc w z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
    (if c = w then 0 else GlobalTheory.GLTwoHecke.singleNU c ((cLoc c z).val i j - (1 : Matrix (Fin n) (Fin n) _) i j)),
    hadd _ (hw _ (sub_one_entry_mem hK i j)) _ ?_, ?_⟩
  · split_ifs
    · exact h0
    · exact hc _ (sub_one_entry_mem hKc i j)
  refine Prod.ext ?_ ?_
  · have h1 : GeneralLinearGroup.map (pInf E) (z : GA E n) = 1 := hfin
    have h2 : pInf E (((z : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
        pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
      rw [map_one_entry]
      have := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) h1
      simpa using this
    have h3 := (infEq E).symm.injective h2
    change _ = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 + 0
    rw [add_zero]
    exact h3
  · apply af_ext
    intro u
    change (cLoc u z).val i j = ((pLoc E u).comp (pFin E)) ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      (show Ad E from ((0 : InfiniteAdeleRing E), _)))
    rw [map_add (f := _), map_one_entry]
    change _ = _ + pLoc E u (GlobalTheory.GLTwoHecke.singleNU w _ + _)
    rw [map_add (f := _)]
    by_cases huw : u = w
    · subst huw
      rw [pLoc_singleNU_self]
      split_ifs with hcw
      · rw [map_zero]; abel
      · rw [pLoc_singleNU_ne (Ne.symm hcw)]; abel
    · rw [pLoc_singleNU_ne huw]
      by_cases huc : u = c
      · subst huc
        rw [if_neg huw, pLoc_singleNU_self]; abel
      · rw [hout u huw huc]
        split_ifs
        · simp
        · rw [pLoc_singleNU_ne huc]; simp

theorem eventually_locU_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))),
    IsOpen (L : Set (finU (E := E) (n := n))) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) →
      ∀ h : x ∈ finU (E := E) (n := n), (⟨x, h⟩ : finU (E := E) (n := n)) ∈ L := by
  intro E _ _ _ n L hL
  have h1 : (L : Set (finU (E := E) (n := n))) ∈ 𝓝 (1 : finU (E := E) (n := n)) := hL.mem_nhds L.one_mem
  rw [nhds_subtype, Filter.mem_comap] at h1
  obtain ⟨V1, hV1, hV1L⟩ := h1
  rw [nhds_subtype, Filter.mem_comap] at hV1
  obtain ⟨V, hV, hVV1⟩ := hV1
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  let Φ : Af E → Ad E := fun a => show Ad E from ((0 : InfiniteAdeleRing E), a)
  have hΦ : Continuous Φ := continuous_const.prodMk continuous_id
  have hΦ0 : Φ 0 = 0 := rfl
  let ψ : (Bool × Fin n × Fin n → Af E) →
      Matrix (Fin n) (Fin n) (Ad E) × (Matrix (Fin n) (Fin n) (Ad E))ᵐᵒᵖ :=
    fun y => (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (false, i, j)),
      MulOpposite.op (Matrix.of fun i j => (1 : Matrix (Fin n) (Fin n) (Ad E)) i j + Φ (y (true, i, j))))
  have hψ : Continuous ψ := by
    refine Continuous.prodMk ?_ (MulOpposite.continuous_op.comp ?_) <;>
    exact continuous_pi fun i => continuous_pi fun j => continuous_const.add (hΦ.comp (continuous_apply _))
  have hψ0 : ψ 0 = Units.embedProduct _ (1 : GA E n) := by
    refine Prod.ext ?_ ?_
    · ext i j; simp [ψ, hΦ0]
    · refine MulOpposite.unop_injective ?_
      ext i j; simp [ψ, hΦ0]
  have hS : ψ ⁻¹' W ∈ 𝓝 (0 : Bool × Fin n × Fin n → Af E) :=
    hψ.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hW)
  rw [nhds_pi, Filter.mem_pi'] at hS
  obtain ⟨I, t, ht, hIt⟩ := hS
  have hN : (⋂ i, t i) ∈ 𝓝 (0 : Af E) := Filter.iInter_mem.2 ht
  obtain ⟨N', hN', hadd⟩ := exists_nhds_zero_half hN
  have h0 : (0 : Af E) ∈ N' := mem_of_mem_nhds hN'
  have hev := GlobalTheory.GLTwoHecke.eventually_singleNU_mem hN'
  have hev2 := (conjSrc_injective (conjE E)).tendsto_cofinite.eventually hev
  filter_upwards [hev, hev2] with w hw hw2 x hxw hxK hx
  have hxw' : x⁻¹ ∈ locU n w := inv_mem hxw
  have hxK' : cLoc w x⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := by rw [map_inv]; exact inv_mem hxK
  choose a ha hxa using entry_eq_one_add h0 hadd hw hw2 x hxw hxK
  choose b hb hxb using entry_eq_one_add h0 hadd hw hw2 x⁻¹ hxw' hxK'
  let y : Bool × Fin n × Fin n → Af E := fun p => if p.1 then b p.2.1 p.2.2 else a p.2.1 p.2.2
  have hy : y ∈ ψ ⁻¹' W := hIt fun p _ => by
    rcases p with ⟨_ | _, i, j⟩
    · exact Set.mem_iInter.1 (ha i j) _
    · exact Set.mem_iInter.1 (hb i j) _
  apply hV1L
  apply hVV1
  apply hWV
  have e : ψ y = Units.embedProduct _ ((x : GA E n)) := by
    refine Prod.ext ?_ ?_
    · ext i j
      exact (hxa i j).symm
    · refine MulOpposite.unop_injective ?_
      ext i j
      exact (hxb i j).symm
  show Units.embedProduct _ (x : GA E n) ∈ W
  rw [← e]
  exact hy

end GlobalTheory.BCT.GlobLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefiStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ h : x ∈ finU (E := E) (n := n), (⟨x, h⟩ : finU (E := E) (n := n)) ∈ L := by
  first | exact @GlobalTheory.BCT.GlobLev.eventually_locU_mem | exact GlobalTheory.BCT.GlobLev.eventually_locU_mem | (intros; apply GlobalTheory.BCT.GlobLev.eventually_locU_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFiniteIdem
noncomputable section

open Matrix
open Formalism.REAL (qdet qminor Tm)

namespace GlobalTheory.CentreFin

section Alg
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_mem {k : ℕ} {E : Fin k → Fin k → A} {S : Subalgebra ℂ A} (h : ∀ a b, E a b ∈ S) (u : ℂ) : qdet E u ∈ S := by
  unfold qdet qminor
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
  unfold Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem commute_qdet {k : ℕ} {E : Fin k → Fin k → A} {x : A} (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) :=
  ((Subalgebra.mem_centralizer_iff ℂ).1 (qdet_mem (S := Subalgebra.centralizer ℂ {x})
    (fun a b => (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact h a b) u) x rfl)

theorem exists_coef {k : ℕ} (E : Fin k → Fin k → A) (s : ℂ) {B : Subalgebra ℂ A} (hB : ∀ u, qdet E u ∈ B) :
    ∃ c : ℕ → A, c k = 1 ∧ (∀ j ≤ k, c j ∈ B) ∧ (∀ u, qdet E (u - s) = ∑ j ∈ Finset.range (k + 1), u ^ j • c j) ∧
      (∑ i, E i i = 0 ∨ ∃ j ≤ k, ∃ t : ℂ, ∑ i, E i i = c j + t • (1 : A)) := by
  cases k with
  | zero => exact ⟨fun _ => 1, rfl, fun _ _ => one_mem _, fun u => by simp [qdet, qminor], Or.inl (by simp)⟩
  | succ m =>
    obtain ⟨c, t, h1, h2, h3⟩ := GlobalTheory.T.shifted_capelli_determinant_subleading_coeff_trace A m E s
    refine ⟨c, h1, fun j hj => ?_, h3, Or.inr ⟨m, m.le_succ, -t, by rw [h2, neg_smul, add_neg_cancel_right]⟩⟩
    exact GlobalTheory.coeff_mem_of_poly_values_mem A (Subalgebra.toSubmodule B) _ c (fun u => h3 u ▸ hB _) j (Nat.lt_succ_of_le hj)

end Alg

section Loc
variable {n : ℕ} {J p q : Matrix (Fin n) (Fin n) ℂ}

end Loc

end GlobalTheory.CentreFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ColStd

theorem sum_smul_col {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) (c : Fin n → 𝓞 K) :
    (∑ j, c j • (fun a => (B : Matrix (Fin n) (Fin n) K) a j)) =
      (B : Matrix (Fin n) (Fin n) K) *ᵥ (fun j => algebraMap (𝓞 K) K (c j)) := by
  ext a
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mulVec_inj {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) {x y : Fin n → K}
    (h : (B : Matrix (Fin n) (Fin n) K) *ᵥ x = (B : Matrix (Fin n) (Fin n) K) *ᵥ y) : x = y := by
  have key : ∀ z : Fin n → K, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((B : Matrix (Fin n) (Fin n) K) *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← key x, h, key y]

theorem colLat_comap_eq_stdLat {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K) :
    (Formalism.L2.DIV.colLat B).comap ((Matrix.mulVecLin B.1).restrictScalars (𝓞 K)) = Formalism.L2.Pj.stdLat K n := by
  ext v
  simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    Formalism.L2.DIV.colLat]
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hv
    rw [sum_smul_col] at hc
    have := mulVec_inj B hc
    intro i
    exact ⟨c i, congrFun this i⟩
  · intro hv
    choose w hw using hv
    refine (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).2 ⟨w, ?_⟩
    rw [sum_smul_col]
    congr 1
    funext j
    exact hw j

end GlobalTheory.ColStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnLatticeComapEqStandardLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLattice_comap_eq_standardLattice : ∀ {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K),
    (Formalism.L2.DIV.colLat B).comap ((Matrix.mulVecLin B.1).restrictScalars (𝓞 K)) = Formalism.L2.Pj.stdLat K n := by
  first | exact @GlobalTheory.ColStd.colLat_comap_eq_stdLat | exact GlobalTheory.ColStd.colLat_comap_eq_stdLat | (intros; apply GlobalTheory.ColStd.colLat_comap_eq_stdLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareModelNegSpaceGoodSchroedinger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareModelNegSpaceGoodSchroedinger
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem squareModelW₁_good : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (-1 : D.host.E) • (spW₁ G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ)) dom) B.ψ := by
  intro D T L sc G μ₀ _hL t i j M hM B hB X Y hJ r s r' s' hX hY
  obtain ⟨co, hco⟩ := GlobalTheory.T.exists_rational_darboux_hermitian_tensor_adeles D.sp.cm.sig B X Y r s r' s' hB hX hY
  have hR : Node.InRange D.R.m (.grid (i : ℕ) (j : ℕ)) := ⟨i.2.le, j.2.le⟩
  have hH := (hM.vtx _ hR).haar_fund
  obtain ⟨dom, hh, hd⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_conjugateUnitaryAdelicIso (spW₁ G i j) (-1) (neg_ne_zero.2 one_ne_zero) hJ _ _ hH.1 hH.2
  let M0 : Model D.sp.cm.sig X Y := ⟨co, fun _ => 0, (M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ), dom⟩
  have hb := GlobalTheory.T.exists_latticeVacuum_finitePlaces_rationalDarboux D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  have hc := GlobalTheory.T.eventually_integralPointsIndicator_isVacuum D.sp.cm.sig B X Y r s r' s' hB hX hY M0 hco
  refine ⟨co, fun v => if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose, dom, ?_⟩
  refine ⟨hco, fun v => ?_, ?_, hh, hd⟩
  · change M0.IsVac B.ψ v (if M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
      then Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1 else (hb v).choose)
    by_cases h : M0.IsVac B.ψ v (Set.indicator {x : Fin _ × Fin _ → Fv _ v | ∀ k, x k ∈ v.adicCompletionIntegers _} 1)
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact (hb v).choose_spec
  · filter_upwards [hc] with v hv
    exact if_pos hv

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareModelNegSpaceGoodSchroedingerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareModel_negSpace_goodSchroedinger : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (hJ : X.J = (-1 : D.host.E) • (spW₁ G i j).gram) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∃ co vac dom, Model.IsGood (Model.mk (σ := D.sp.cm.sig) (X := X) (W := Y) co vac ((M.ν (.grid (i : ℕ) (j : ℕ))).map (conjU _ (-1) hJ)) dom) B.ψ := by
  first | exact @GlobalTheory.FunObj.squareModelW₁_good | exact GlobalTheory.FunObj.squareModelW₁_good | (intros; apply GlobalTheory.FunObj.squareModelW₁_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

def tensForm {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ) : ((κ ⊕ κ' → k) → ℂ) →ₗ[ℂ] ℂ where
  toFun f := l₁ fun x₁ => l₂ fun x₂ => f (Sum.elim x₁ x₂)
  map_add' f g := by
    rw [← map_add (f := _)]; congr 1; funext x₁; rw [Pi.add_apply, ← map_add (f := _)]; rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; funext x₁; rw [Pi.smul_apply, ← map_smul]; rfl

theorem tensForm_box {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ)
    (φ₁ : (κ → k) → ℂ) (φ₂ : (κ' → k) → ℂ) : tensForm l₁ l₂ (boxFun φ₁ φ₂) = l₁ φ₁ * l₂ φ₂ := by
  have e : (fun x₁ => l₂ fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = l₂ φ₂ • φ₁ := by
    funext x₁
    have : (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := by funext x₂; rfl
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  change l₁ _ = _
  rw [e, map_smul, smul_eq_mul, mul_comm]

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def repl (v : Pl (F := F)) (y : κ → AF F) (x : κ → Fv F v) : κ → AF F :=
  fun i => y i - liftV v (evFin F v (y i)) + liftV v (x i)

def proj (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ y := φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x)
  map_add' Φ Ψ := by
    funext y
    rw [Pi.add_apply, ← mul_add, ← map_add (f := _)]; rfl
  map_smul' c Φ := by
    funext y
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← smul_eq_mul c, ← map_smul]; rfl

theorem proj_apply (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (Φ : (κ → AF F) → ℂ)
    (y : κ → AF F) : proj v φ₀ l Φ y = φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x) := rfl

theorem evFin_repl (v : Pl (F := F)) (y : κ → AF F) (x : κ → Fv F v) (i : κ) : evFin F v (repl v y x i) = x i := by
  simp [repl, evFin_liftV]

theorem proj_tens (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (κ → Fv F v) → ℂ)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) :
    proj v φ₀ l (tens (evFin F v) φ r) = l φ • tens (evFin F v) φ₀ r := by
  funext y
  have e : (fun x => tens (evFin F v) φ r (repl v y x)) = r y • φ := by
    funext x
    have h1 : repl v y x = y + fun i => liftV v (x i - evFin F v (y i)) := by
      funext i; simp only [repl, Pi.add_apply, map_sub]; ring
    have h2 : r (repl v y x) = r y := by
      rw [h1]; exact hr _ _ fun u hu => funext fun i => at_liftV v _ u hu
    simp only [tens, evFin_repl, h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [proj_apply, e, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.MixedForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalProperties
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResidueEisenstein.FrameLeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem absE_det_of_scalesBy {k : ℕ} {X : Matrix (Fin n) (Fin k) E} {L : Matrix (Fin k) (Fin n) E} (hL : L * X = 1)
    {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X γ β) :
    absE F E (Matrix.GeneralLinearGroup.det β) = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F X = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hb : β.1 = (L * γ0.1.1 * X).map (inclR (F := F) (AF F)) := by
    have := congrArg (adMat F L * ·) e
    have h2 : adMat F L * (adMat F X * β.1) = β.1 := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
    rw [h2, hmat] at this
    rw [← this]
    simp only [adMat, Matrix.map_mul, Matrix.mul_assoc]
  set c : E := (L * γ0.1.1 * X).det with hc
  have hd : (Matrix.GeneralLinearGroup.det β).1 = inclR (F := F) (AF F) c := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb, hc, RingHom.map_det]
    rfl
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := (Matrix.GeneralLinearGroup.det β).mul_inv
      rw [hd, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim (Matrix.GeneralLinearGroup.det β) 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = Matrix.GeneralLinearGroup.det β from
      Units.ext (by simp [hd])] at this

end GlobalTheory.ResidueEisenstein.FrameLeviFacts

namespace GlobalTheory.ResidueEisenstein


open GlobalTheory.StdPar GlobalTheory.ResLine.LeviFacts in
theorem frame_levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hX : initCols X (Fin.last r) = X := rfl
  have hY : initCols Y (Fin.last r) = Y := rfl
  have hlev : ∀ m ∈ levi σ J X Y {Fin.last r}, m ∈ frameStab σ J X ⊤ ∧ m ∈ frameStab σ J Y ⊤ := fun m hm => by
    simp only [levi, Subgroup.mem_iInf] at hm
    exact hm _ (Finset.mem_singleton_self _)
  refine ⟨fun m hm u hu => conj_mem hW (Fin.last r) (hlev m hm).1 hu,
    fun g hg hm => eq_one h hJ hW (Fin.last r) hg (hlev g hm).2,
    fun u hu => (unipRad_fix hu).trans (by simp), fun m hm => ?_,
    fun γ hγ β e => FrameLeviFacts.absE_det_of_scalesBy (yx h hJ hW) hγ e, inf_le_left,
    (isClosed_levi {Fin.last r} h hJ hW).2⟩
  have h2 : m ∈ ⨅ k ∈ ({Fin.last r} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
  simp only [Subgroup.mem_iInf] at h2
  obtain ⟨B, hB, e⟩ := h2 _ (Finset.mem_singleton_self _)
  exact ⟨B, e, hB⟩

end GlobalTheory.ResidueEisenstein
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLeviNormalizesRadicalPropertiesStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrameLevi_normalizes_radical_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → (∀ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, ∀ u ∈ unipRad σ J X, m * u * m⁻¹ ∈ unipRad σ J X) ∧ (∀ g ∈ unipRad σ J X, g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} → g = 1) ∧ (∀ u ∈ unipRad σ J X, ScalesBy σ J X u 1) ∧ (∀ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ β, ScalesBy σ J X m β ∧ absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ (∀ γ ∈ ratPts σ J, ∀ β, ScalesBy σ J X γ β → absE F E (Matrix.GeneralLinearGroup.det β) = 1) ∧ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} ∧ IsClosed ((GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} : Subgroup (GAd σ J)) : Set (GAd σ J)) := by
  first | exact @GlobalTheory.ResidueEisenstein.frame_levi_facts | exact GlobalTheory.ResidueEisenstein.frame_levi_facts | (intros; apply GlobalTheory.ResidueEisenstein.frame_levi_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtends
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtends
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvInj

theorem finprod_ne_zero' {ι : Type} {g : ι → ℂ} (h : ∀ i, g i ≠ 0) : ∏ᶠ i, g i ≠ 0 := by
  classical
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun i _ => h i
  · exact one_ne_zero

theorem eq_zero_of_pure_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h0 : pure f φ = 0) : f = 0 := by
  classical
  have hS := Filter.eventually_cofinite.1 hstd
  set S := hS.toFinset
  have hpt : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0 := fun v => by
    by_contra hc
    push_neg at hc
    exact hne v (funext hc)
  choose pt hpt using hpt
  let yf : κ → Af F := fun i => ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (pt v i)
  have hyf : ∀ w i, evalV F w (yf i) = if w ∈ S then pt w i else 0 := by
    intro w i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [yf, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w]
      · exact GlobalTheory.AdelicU.evalV_singleFin_self w _
      · intro b _ hb; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _
      · intro h; exact absurd hw h
    · refine Finset.sum_eq_zero fun b hb => ?_
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _
  ext a
  let x : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), yf i)
  have hI : (fun i => evI F (x i)) = a := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
    exact RingEquiv.apply_symm_apply _ _
  have hF : ∀ w, (fun i => GlobalTheory.AdelicU.evFin F w (x i)) = fun i => if w ∈ S then pt w i else 0 := by
    intro w; funext i; exact hyf w i
  have hc : ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 0 := by
    refine finprod_ne_zero' fun v => ?_
    rw [hF v]
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact hpt v
    · simp only [hv, if_false]
      have : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
        by_contra hc'; exact hv (hS.mem_toFinset.2 hc')
      rw [this, Set.indicator_of_mem (by intro i; exact zero_mem _)]
      exact one_ne_zero
  have e := congrFun h0 x
  change f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) = 0 at e
  rw [hI] at e
  simpa using (mul_eq_zero.1 e).resolve_right hc

theorem ei_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.InjOn e (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) → Function.Injective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM e hinj ei ev _ hev
  refine (injective_iff_map_eq_zero ei).2 fun f hf => ?_
  have hSB : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v) := fun v => (hM.vac v).1
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA f M.vac hSB hM.std
  have h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = e 0 := by
    rw [hev f M.vac hSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac = 0 :=
    hinj hmem (schA F (Fin n × Fin d)).zero_mem h1
  exact eq_zero_of_pure_eq_zero f M.vac (fun v => (hM.vac v).2.1) hM.std h2

end GlobalTheory.EvInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtendsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_injective_extends : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.InjOn e (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Injective ei := by
  first | exact @GlobalTheory.EvInj.ei_injective | exact GlobalTheory.EvInj.ei_injective | (intros; apply GlobalTheory.EvInj.ei_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBound
open Filter Topology
open scoped SchwartzMap Uniformity

namespace GlobalTheory

theorem schwartz_family_uniform_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (I : Type)
    (lam : I → SchwartzMap V ℂ →L[ℂ] ℂ) (w : I → ℝ), (∀ i, 0 ≤ w i) →
    (∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖lam i f‖ ≤ C * w i ^ N) →
    ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)), ∀ i f,
      ‖lam i f‖ ≤ C * (T.sup (schwartzSeminormFamily ℂ V ℂ)) f * w i ^ N := by
  intro V _ _ _ I lam w hw hb
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace 𝓢(V, ℂ) := SchwartzComplete.completeSpace
  haveI : BaireSpace 𝓢(V, ℂ) := inferInstance
  let S : ℕ × ℕ → Set 𝓢(V, ℂ) := fun p => {f | ∀ i, ‖lam i f‖ ≤ (p.2 : ℝ) * w i ^ p.1}
  have hS : ∀ p, IsClosed (S p) := by
    intro p
    simp only [S, Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_norm.comp (lam i).continuous) continuous_const
  have hU : ⋃ p, S p = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    obtain ⟨N, C, hC⟩ := hb f
    obtain ⟨M, hM⟩ := exists_nat_ge C
    exact Set.mem_iUnion.2 ⟨(N, M), fun i =>
      (hC i).trans (mul_le_mul_of_nonneg_right hM (pow_nonneg (hw i) _))⟩
  obtain ⟨p, f₀, hf₀⟩ := nonempty_interior_of_iUnion_of_closed hS hU
  have hn : interior (S p) ∈ 𝓝 f₀ := isOpen_interior.mem_nhds hf₀
  have hn' : (fun g => f₀ + g) ⁻¹' interior (S p) ∈ 𝓝 (0 : 𝓢(V, ℂ)) := by
    have h : Tendsto (fun g : 𝓢(V, ℂ) => f₀ + g) (𝓝 0) (𝓝 f₀) := by
      simpa using (continuous_const_add f₀).tendsto 0
    exact h hn
  obtain ⟨⟨T, ε⟩, hε, hT⟩ := ((schwartz_withSeminorms ℂ V ℂ).hasBasis_zero_ball).mem_iff.1 hn'
  simp only at hε hT
  set q := T.sup (schwartzSeminormFamily ℂ V ℂ) with hq
  have hball : ∀ g, q g < ε → ∀ i, ‖lam i g‖ ≤ 2 * (p.2 : ℝ) * w i ^ p.1 := by
    intro g hg i
    have h1 : f₀ + g ∈ S p := interior_subset (hT (by simpa [Seminorm.mem_ball] using hg))
    have h2 : f₀ ∈ S p := interior_subset hf₀
    have h3 : lam i g = lam i (f₀ + g) - lam i f₀ := by simp
    rw [h3]
    calc ‖lam i (f₀ + g) - lam i f₀‖ ≤ ‖lam i (f₀ + g)‖ + ‖lam i f₀‖ := norm_sub_le _ _
      _ ≤ (p.2 : ℝ) * w i ^ p.1 + (p.2 : ℝ) * w i ^ p.1 := add_le_add (h1 i) (h2 i)
      _ = 2 * (p.2 : ℝ) * w i ^ p.1 := by ring
  refine ⟨p.1, 2 * (p.2 : ℝ) / ε, T, fun i f => ?_⟩
  set A := 2 * (p.2 : ℝ) * w i ^ p.1 / ε with hA
  have hA0 : 0 ≤ A := by
    have := pow_nonneg (hw i) p.1
    positivity
  have hq0 : 0 ≤ q f := apply_nonneg _ _
  have hscale : ∀ t, q f < t → ‖lam i f‖ ≤ t * A := by
    intro t ht
    have htpos : 0 < t := lt_of_le_of_lt hq0 ht
    have hc : ‖((ε / t : ℝ) : ℂ)‖ = ε / t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (div_pos hε htpos).le]
    have hg : q (((ε / t : ℝ) : ℂ) • f) < ε := by
      rw [map_smul_eq_mul, hc]
      calc ε / t * q f < ε / t * t := mul_lt_mul_of_pos_left ht (div_pos hε htpos)
        _ = ε := by field_simp
    have h := hball _ hg i
    rw [map_smul, norm_smul, hc] at h
    rw [hA, show t * (2 * (p.2 : ℝ) * w i ^ p.1 / ε) = (t / ε) * (2 * (p.2 : ℝ) * w i ^ p.1) by ring]
    have : ‖lam i f‖ = (t / ε) * (ε / t * ‖lam i f‖) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h (div_pos htpos hε).le
  have hfin : ‖lam i f‖ ≤ q f * A := by
    rcases hA0.lt_or_eq with hApos | hAz
    · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      have : q f < a / A := (lt_div_iff₀ hApos).2 ha
      calc ‖lam i f‖ ≤ a / A * A := hscale _ this
        _ = a := by field_simp
    · rw [← hAz, mul_zero]
      have := hscale (q f + 1) (by linarith)
      rwa [← hAz, mul_zero] at this
  calc ‖lam i f‖ ≤ q f * A := hfin
    _ = 2 * (p.2 : ℝ) / ε * q f * w i ^ p.1 := by rw [hA]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_schwartz_seminorm_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (I : Type)
    (lam : I → SchwartzMap V ℂ →L[ℂ] ℂ) (w : I → ℝ), (∀ i, 0 ≤ w i) →
    (∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖lam i f‖ ≤ C * w i ^ N) →
    ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)), ∀ i f, ‖lam i f‖ ≤ C * (T.sup (schwartzSeminormFamily ℂ V ℂ)) f * w i ^ N := by
  first | exact @GlobalTheory.schwartz_family_uniform_bound | exact GlobalTheory.schwartz_family_uniform_bound | (intros; apply GlobalTheory.schwartz_family_uniform_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open Filter Topology
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaIntAdm

theorem exists_clm_integral {S Ω : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [FirstCountableTopology S] [BarrelledSpace ℂ S] [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → S →L[ℂ] ℂ)
    (hint : ∀ f, Integrable (fun x => T x f) μ) : ∃ L : S →L[ℂ] ℂ, ∀ f, L f = ∫ x, T x f ∂μ := by
  let q : Seminorm ℂ S := Seminorm.of (fun f => ∫ x, ‖T x f‖ ∂μ)
    (fun f g => by
      have hf := (hint f).norm
      have hg := (hint g).norm
      have hfg := (hint (f + g)).norm
      rw [← integral_add hf hg]
      exact integral_mono hfg (hf.add hg) fun x => by simp only [map_add (f := _)]; exact norm_add_le _ _)
    (fun c f => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [map_smul, norm_mul]))
  have hq : ∀ f, q f = ∫ x, ‖T x f‖ ∂μ := fun f => rfl
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    apply IsSeqClosed.isClosed
    intro y y₀ hy hlim
    have hc : 0 ≤ c := le_trans (apply_nonneg _ _) (hy 0)
    show q y₀ ≤ c
    rw [hq, integral_norm_eq_lintegral_enorm (hint y₀).aestronglyMeasurable]
    apply ENNReal.toReal_le_of_le_ofReal hc
    have hpt : ∀ x, Tendsto (fun n => ‖T x (y n)‖ₑ) atTop (𝓝 ‖T x y₀‖ₑ) := fun x =>
      ((T x).continuous.enorm.continuousAt.tendsto).comp hlim
    calc ∫⁻ x, ‖T x y₀‖ₑ ∂μ = ∫⁻ x, liminf (fun n => ‖T x (y n)‖ₑ) atTop ∂μ := by
          congr 1; funext x; exact (hpt x).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖T x (y n)‖ₑ ∂μ) atTop :=
          lintegral_liminf_le' fun n => (hint (y n)).aestronglyMeasurable.enorm
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal c) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          show ∫⁻ x, ‖T x (y n)‖ₑ ∂μ ≤ ENNReal.ofReal c
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hint (y n))]
          exact ENNReal.ofReal_le_ofReal (hy n)
      _ = ENNReal.ofReal c := liminf_const _
  have hqc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous _ hlsc
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, T x f ∂μ
      map_add' := fun f g => by simp only [map_add (f := _)]; exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; exact integral_const_mul c _ }
  have hL0 : ContinuousAt L 0 := by
    rw [ContinuousAt, map_zero]
    refine squeeze_zero_norm (a := fun f => q f) (fun f => ?_) ?_
    · exact norm_integral_le_integral_norm _
    · have := hqc.tendsto 0
      rwa [map_zero] at this
  exact ⟨⟨L, continuous_of_continuousAt_zero L.toAddMonoidHom hL0⟩, fun f => rfl⟩

end GlobalTheory.ThetaIntAdm

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (theta)
open scoped Classical

theorem GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (χX χY : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : Rep σ X Y), M.IsWeil ψ χX χY om →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), M.Conv om Φ) →
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 := by
  intro F E _ _ _ _ _ σ n d X Y M ψ χX χY om hW hC
  obtain ⟨l₀, hl₀, hl₀e⟩ := GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F (Fin n × Fin d)
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW
  have pres : ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om p Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    hS.pres
  have adm : ∀ p, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d),
      l ∘ₗ om p ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := hS.adm
  have th : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), ∀ g, theta om Φ g 1 = l₀ (om (g, 1) Φ) :=
    fun Φ hΦ g => (hl₀e _ (pres _ Φ hΦ)).symm
  let fI : GlobalTheory.WeilM.schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => M.I om Φ.1 1
      map_add' := fun Φ Ψ => by
        have e : (fun g => theta om (Φ + Ψ).1 g 1) = fun g => theta om Φ.1 g 1 + theta om Ψ.1 g 1 := by
          funext g
          rw [th _ (Φ + Ψ).2, th _ Φ.2, th _ Ψ.2, Submodule.coe_add, map_add (f := _), map_add (f := _)]
        show ∫ g in M.dom, theta om (Φ + Ψ).1 g 1 ∂M.μ = ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ + ∫ g in M.dom, theta om Ψ.1 g 1 ∂M.μ
        rw [e]
        exact integral_add (hC _ Φ.2 1) (hC _ Ψ.2 1)
      map_smul' := fun c Φ => by
        have e : (fun g => theta om (c • Φ).1 g 1) = fun g => c * theta om Φ.1 g 1 := by
          funext g
          rw [th _ (c • Φ).2, th _ Φ.2, Submodule.coe_smul, map_smul, map_smul, smul_eq_mul]
        show ∫ g in M.dom, theta om (c • Φ).1 g 1 ∂M.μ = c • ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ
        rw [e, smul_eq_mul]
        exact integral_const_mul c _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend fI
  have hlΦ : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 :=
    fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, hlΦ⟩
  intro g₀ hg₀
  have mem : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, GlobalTheory.WeilM.pureA F f g₀ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f => Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  choose T hT using fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J => adm (x, 1) l₀ hl₀ g₀ hg₀
  have eT : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, (fun x => T x f) = fun x => theta om (GlobalTheory.WeilM.pureA F f g₀) x 1 := fun f => by
    funext x
    rw [← hT x f, th _ (mem f)]
    rfl
  haveI := GlobalTheory.T.schwartzMap_barrelledSpace' (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaIntAdm.exists_clm_integral (M.μ.restrict M.dom) T
    (fun f => by rw [eT f]; exact hC _ (mem f) 1)
  refine ⟨L, fun f => ?_⟩
  rw [hlΦ _ (mem f), hL, eT f]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adm_eq_thetaIntegral_of_conv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (χX χY : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : Rep σ X Y), M.IsWeil ψ χX χY om →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), M.Conv om Φ) →
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 := by
  first | exact @GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral | exact GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral | (intros; apply GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThird
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThird
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

attribute [local instance high] Submodule.module

theorem mumaxTop : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := fun hT =>
  GlobalTheory.LamMuMax.slopeMax_le (GlobalTheory.T.mass_bound_of_tamagawa_unitary hT)
    GlobalTheory.T.normOneTorusClassNumberBound_proof

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameThirdStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

attribute [local instance high] Submodule.module

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_third : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → GoodW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) → latW U (wtZ a n) ≠ ⊥ → slopeMax_sq (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n)) (latW U (wtZ a n)) ≤ 2 * lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 2 * Real.log (supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1)) + Real.log |(discr c.F : ℝ)| / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.mumaxTop | exact GlobalTheory.mumaxTop | (intros; apply GlobalTheory.mumaxTop <;> assumption)
end
end
