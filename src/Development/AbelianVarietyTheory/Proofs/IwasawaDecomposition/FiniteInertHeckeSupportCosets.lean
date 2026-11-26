module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Formalism.LocalToGlobal.Columns.TwQBOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd.CosetFin

theorem finite_cosets {G H : Type} [Group G] [Group H] (φ : G →* H) (H' : Subgroup H) (K : Subgroup H')
    (U : Subgroup G) (p : G → Prop) (F : Set (H' ⧸ K)) (hF : F.Finite)
    (hp : ∀ x, p x → ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) ∈ F)
    (hU : ∀ x y, p x → p y → ∀ hz : φ (x⁻¹ * y) ∈ H', (⟨φ (x⁻¹ * y), hz⟩ : H') ∈ K → x⁻¹ * y ∈ U) :
    Set.Finite {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} := by
  have hsub : {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x} ⊆
      ⋃ d ∈ F, {c : G ⧸ U | ∃ x : G, (x : G ⧸ U) = c ∧ p x ∧
        ∃ hx : φ x ∈ H', ((⟨φ x, hx⟩ : H') : H' ⧸ K) = d} := by
    rintro c ⟨x, hc, hx⟩
    obtain ⟨h1, h2⟩ := hp x hx
    exact Set.mem_biUnion h2 ⟨x, hc, hx, h1, rfl⟩
  refine (hF.biUnion fun d _ => Set.Subsingleton.finite ?_).subset hsub
  rintro c ⟨x, rfl, hx, hx1, hx2⟩ c' ⟨y, rfl, hy, hy1, hy2⟩
  have hk := QuotientGroup.eq.1 (hx2.trans hy2.symm)
  have hz : φ (x⁻¹ * y) ∈ H' := by
    rw [map_mul, map_inv]; exact H'.mul_mem (H'.inv_mem hx1) hy1
  refine QuotientGroup.eq.2 (hU x y hx hy hz ?_)
  convert hk using 1
  apply Subtype.ext
  simp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

variable {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

def locHom (D : InertDatum L n v w) : GAf L n →* GL (Fin n) (w.adicCompletion L) :=
  MonoidHom.mk' D.loc fun x y => by
    simp only [InertDatum.loc, Subgroup.coe_mul, map_mul, mul_assoc, mul_inv_cancel_left]

theorem entries_int {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {σ : K →+* K}
    {g : GU σ n} (hg : g ∈ KU σ n) (i j : Fin n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ intL K := by
  obtain ⟨-, k, hk⟩ := hg
  have hk' : bc (n := Fin n) (intL K).subtype k = (g : GL (Fin n) K) := hk
  rw [← hk']
  exact ((k : Matrix (Fin n) (Fin n) (intL K)) i j).2

theorem finite_inert_support : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ s : GU Dv.σw n, Set.Finite {c : GU Dv.σw n ⧸ KU Dv.σw n | ∃ a ∈ KU Dv.σw n, ((a * s : GU Dv.σw n) : GU Dv.σw n ⧸ KU Dv.σw n) = c}) → (∀ z : GAf L n, TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n) → ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} := by
  intro L _ _ _ n v w Dv hfin hint U hU h hh
  obtain ⟨-, S, hS⟩ := hh
  refine finite_cosets (locHom Dv) (GU Dv.σw n) (KU Dv.σw n) U
    (fun x => TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0) _
    (S.finite_toSet.biUnion fun s _ => hfin s) ?_ ?_
  · rintro x ⟨-, hx⟩
    have hm : Dv.loc x ∈ GU Dv.σw n := by
      by_contra hm
      exact hx (dif_neg hm)
    have hne : h ⟨Dv.loc x, hm⟩ ≠ 0 := by
      intro h0
      exact hx ((dif_pos hm).trans h0)
    obtain ⟨s, hs, a, b, e⟩ := hS _ hne
    refine ⟨hm, Set.mem_biUnion hs ⟨a, a.2, ?_⟩⟩
    have e' : (⟨locHom Dv x, hm⟩ : GU Dv.σw n) = (a : GU Dv.σw n) * s * b := e
    rw [e']
    exact (QuotientGroup.mk_mul_of_mem _ b.2).symm
  · rintro x y ⟨hx, -⟩ ⟨hy, -⟩ hz hk
    have ht : TrivOutside {v} (x⁻¹ * y) := trivOutside_mul (trivOutside_inv hx) hy
    exact (hU _ ht).2 (hint _ ht fun i j => entries_int hk i j)

end GlobalTheory.SatInd.CosetFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_inertHecke_support_cosets : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ s : GU Dv.σw n, Set.Finite {c : GU Dv.σw n ⧸ KU Dv.σw n | ∃ a ∈ KU Dv.σw n, ((a * s : GU Dv.σw n) : GU Dv.σw n ⧸ KU Dv.σw n) = c}) → (∀ z : GAf L n, TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n) → ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0} := by
  first | exact @GlobalTheory.SatInd.CosetFin.finite_inert_support | exact GlobalTheory.SatInd.CosetFin.finite_inert_support | (intros; apply GlobalTheory.SatInd.CosetFin.finite_inert_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmax

theorem tensor_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add (f := _), TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at h0 h1
  exact ⟨h0, h1⟩

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

omit [IsCMField L] in
theorem compAt_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : L) (a : AFplus L) :
    compAt L v (x ⊗ₜ[maximalRealSubfield L] a) = x ⊗ₜ[maximalRealSubfield L] (a v) := by
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul]
  rfl

theorem eq_zero_of_compAt (z : AL L) (hz : ∀ v, compAt L v z = 0) : z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨A, B, hAB⟩ := tensor_decomp b z
  have hoff : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB, map_add (f := _), compAt_tmul, compAt_tmul] at h
    exact tensor_decomp_zero b _ _ h
  have hA : A = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).1
  have hB : B = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).2
  rw [hAB, hA, hB]; simp


open Classical in
def sgl (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : AFplus L :=
  ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r, by
    refine Filter.mem_of_superset (Set.finite_singleton v).compl_mem_cofinite ?_
    intro w hw
    have hw' : w ≠ v := hw
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hw']
    exact zero_mem _⟩

omit [IsCMField L] in
theorem sgl_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : sgl L v r v = r := by
  classical
  exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r

omit [IsCMField L] in
theorem sgl_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) {w} (hw : w ≠ v) : sgl L v r w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) hw r

omit [IsCMField L] in
theorem one_tmul_sgl_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L))
    (hr : r ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v r : AL L) ∈ ALint L := by
  refine Subring.subset_closure (Or.inr ⟨sgl L v r, fun w => ?_, rfl⟩)
  rcases eq_or_ne w v with rfl | hw
  · rw [sgl_same]; exact hr
  · rw [sgl_ne L v r hw]; exact zero_mem _


omit [IsCMField L] in
theorem exists_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hy : y ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    ∃ Y ∈ ALint L, compAt L v Y = y := by
  have key : tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ≤ (ALint L).map (compAt L v) := by
    rw [tensInt, Subring.closure_le]
    rintro _ (⟨⟨_, s, rfl⟩, rfl⟩ | ⟨r, rfl⟩)
    · refine ⟨(s : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L),
        Subring.subset_closure (Or.inl ⟨s, rfl⟩), ?_⟩
      rw [compAt_tmul]; rfl
    · refine ⟨_, one_tmul_sgl_mem L v r r.2, ?_⟩
      rw [compAt_tmul, sgl_same]
  exact key hy

theorem mem_ALint_of_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : AL L)
    (hoff : ∀ w, w ≠ v → compAt L w x = 0)
    (hv : compAt L v x ∈ tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    x ∈ ALint L := by
  obtain ⟨Y, hY, hYv⟩ := exists_lift L v _ hv
  have h : x - Y * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1) = 0 := by
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, compAt_tmul]
    rcases eq_or_ne w v with rfl | hw
    · rw [sgl_same, hYv, ← Algebra.TensorProduct.one_def, mul_one, sub_self]
    · rw [sgl_ne L v 1 hw, hoff w hw, tmul_zero, mul_zero, sub_self]
  rw [sub_eq_zero.1 h]
  exact Subring.mul_mem _ hY (one_tmul_sgl_mem L v 1 (one_mem _))

theorem entries_mem_of_range {K : Type} [Field K] (S : Subring K) {n : ℕ} (P : GL (Fin n) K)
    (hP : P ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range) (i j : Fin n) :
    (P : Matrix (Fin n) (Fin n) K) i j ∈ S := by
  obtain ⟨Q, rfl⟩ := hP
  exact ((Q : Matrix (Fin n) (Fin n) S) i j).2

theorem mem_Umax_of_trivOutside_of_loc_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (z : GAf L n), TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n := by
  intro L _ _ _ n v w Dv z hz hint i j
  have hP := entries_mem_of_range _ _ Dv.Pint
  have hP' := entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hg : Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) =
      Dv.P * Dv.loc z * Dv.P⁻¹ := by
    unfold InertDatum.loc
    group
  have he : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) ∈
      intL (w.adicCompletion L) := by
    have h1 : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) =
        ((Dv.P * Dv.loc z * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j := by
      rw [← hg]; rfl
    rw [h1]
    simp only [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
      (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP i l) (hint l k)) (hP' k j)
  have hv := (Dv.integ _).2 he
  have hone : ∀ {R : Type} [CommRing R] (S : Subring R), (1 : Matrix (Fin n) (Fin n) R) i j ∈ S := by
    intro R _ S
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hc : ∀ u, compAt L u ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro u
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hd : (z.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈
      ALint L := by
    apply mem_ALint_of_supported L v
    · intro u hu
      have h := congrFun (congrFun (hz u hu) i) j
      rw [map_sub, hc, ← h, Matrix.map_apply, sub_self]
    · rw [map_sub, hc]
      exact Subring.sub_mem _ hv (hone _)
  have := Subring.add_mem _ hd (hone (ALint L))
  rwa [sub_add_cancel] at this

end GlobalTheory.InertUmax
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (z : GAf L n), TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n := by
  first | exact @GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral | exact GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral | (intros; apply GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Cut

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}

def frStab (P : HeightOneSpectrum (𝓞 E)) (C : Set (Sp E n)) : Subgroup ↥(GLint E n P) where
  carrier := {g | ∀ v, g.1 v ∈ C ↔ v ∈ C}
  one_mem' _ := Iff.rfl
  mul_mem' {a b} ha hb v := (ha (b.1 v)).trans (hb v)
  inv_mem' {a} ha v := by
    have h := ha ((a⁻¹).1 v)
    have e : a.1 ((a⁻¹).1 v) = v := LinearEquiv.apply_symm_apply a.1 v
    rw [e] at h
    exact h.symm

theorem mem_frStab {P : HeightOneSpectrum (𝓞 E)} {C : Set (Sp E n)} {g : ↥(GLint E n P)} :
    g ∈ frStab P C ↔ ∀ v, g.1 v ∈ C ↔ v ∈ C := Iff.rfl

def cutQ (Θ : LevQFam E K n Q) (C : ∀ P : Q, Set (Sp E n)) : LevQFam E K n Q := fun P =>
  ⟨(Θ P).H ⊓ frStab P.1 (C P), (Θ P).lam.comp (Subgroup.inclusion inf_le_left)⟩

theorem mem_cutQ_grp {Θ : LevQFam E K n Q} {C : ∀ P : Q, Set (Sp E n)} {t : GLQ E n Q} :
    t ∈ (cutQ Θ C).grp ↔ t ∈ Θ.grp ∧ ∀ P, t P ∈ frStab P.1 (C P) := by
  simp only [LevQFam.grp, Subgroup.mem_pi, Set.mem_univ, forall_const]
  exact forall_and

theorem cutQ_grp_le (Θ : LevQFam E K n Q) (C : ∀ P : Q, Set (Sp E n)) : (cutQ Θ C).grp ≤ Θ.grp := fun _ ht => (mem_cutQ_grp.1 ht).1

end Cut

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}


open Classical in
def cqOf (q : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) : Set (Sp X.E (R.N j)) :=
  cosetIn q ⟨P.1, Finset.mem_union_right _ P.2⟩

end Pt

end GlobalTheory.Mem.Col2.ChEx

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Inv

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

def InvActs (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) : Prop :=
  ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (g : FrmG Λ Θ) (r : PtY ST SG Q y) (P : Q),
    cq (ya Λ Θ g r) P = (fun v => (g.2.2.1 P).1 v) '' cq r P

def PtDet (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) : Prop :=
  ∀ r r' : PtY ST SG Q y, r.1.1 = r'.1.1 → bar r = bar r' → cq r = cq r' → r = r'

end Inv

theorem mem_map_conj {G : Type} [Group G] (S : Subgroup G) (k x : G) :
    x ∈ S.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ S := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨k⁻¹ * x * k, h, by simp [mul_assoc]⟩

section Main

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) (i : ℕ) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i

abbrev lvQ (a : I.ι) (i : ℕ) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i

abbrev rpT (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : PtAt B.R I.sel (I.tup a) (I.cst a) u i :=
  rp (lvG I a i) (lvQ I a i) ((I.Tp a).pref u i) (I.pref u a i) c

open Classical in
theorem q_sub_SQ (a : I.ι) : I.Q a ⊆ I.SQ := by
  intro P hP
  unfold ColIn.SQ
  exact Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hP⟩

theorem q_disj (hI : I.Ok) (a : I.ι) : ∀ P ∈ QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K), P ∉ (B.primes X).vGs := by
  intro P hP hG
  exact Finset.disjoint_left.1 (LevTwist.levOk_twists B X I hI).2.1 hG (q_sub_SQ I a hP)

theorem q_conj (hI : I.Ok) (a : I.ι) : ∀ P : I.Q a, conjPrime₂ P.1 ≠ P.1 := by
  intro P hc
  obtain ⟨-, hs⟩ := (LevTwist.levOk_twists B X I hI).1
  have hm : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    simp [uSG, q_sub_SQ I a P.2]
  exact hs _ hm (by rw [hc]; exact hm)

theorem cos_of_neT {u : B.Word} {a : I.ι} {i : ℕ} (h : i + 1 ≠ B.R.m) (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u i) :
    cosetIn q = cosetIn q' := by
  have e : ∀ r : PtAt B.R I.sel (I.tup a) (I.cst a) u i, r.1.2 = ∅ := fun r => by
    have hr := r.2
    rw [ysAt_ys_of_ne (h := h)] at hr
    exact Set.mem_singleton_iff.1 hr
  funext P
  ext z
  simp [cosetIn, e q, e q']

end Main

end GlobalTheory.Mem.Col2.ChEx
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

variable {D : D7}


set_option maxHeartbeats 2000000 in
def twFL (L : LocAll (lay0 D)) (F : TwFrameC D) : TwFrameC (withLoc L) := { F with }

set_option maxHeartbeats 4000000 in
theorem twTiedL (L : LocAll (lay0 D)) {F : TwFrameC D} {low : Finset ℕ} (h : TwistFrameLowIndexCompatibility D F low) :
    TwistFrameLowIndexCompatibility (withLoc L) (twFL L F) low := { h with }

set_option maxHeartbeats 4000000 in
theorem choiceL (L : LocAll (lay0 D)) {C : NChoice D} (h : ChoiceC D C) : ChoiceC (withLoc L) (chL L C) := { h with }


set_option maxHeartbeats 20000000 in
def mtVL (L : LocAll (lay0 D)) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [g : AddCommGroup W₀]
    [m : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (V : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) : @NX.MtVReal (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ :=
  @NX.MtVReal.mk (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ V.W V.acg V.mod V.fd V.ρ V.irr V.alg V.bc V.J V.χ V.J_open V.hyp V.QP V.QP_sub V.QP_cover V.QP_nconj V.DP V.DP_sub V.DP_cover V.DP_nconj V.sp V.sp_w V.redG V.J_mem V.chi_eq V.real


set_option maxHeartbeats 4000000 in
def expL (L : LocAll (lay0 D)) (X : NExpTied D) : NExpTied (withLoc L) :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      (@mtVL D L i j b k Q ψ X.sgnT (X.Wt i j b) (X.acgWt i j b) (X.modWt i j b) (X.rhoW i j b) (X.tauG i j b) (X.mtV i j b k Q ψ h1 h2 h)) }

set_option maxHeartbeats 4000000 in
theorem nctL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) (h : NChTie D C) : NChTie (withLoc L) (chL L C) := by
  obtain ⟨ψ0, h1, h2, -⟩ := h.psi_eq
  exact {
    twOf_eq := Sp.twOf_eq
    twSide_eq := Sp.twSide_eq
    Q_eq a := (Sp.Q_eq _ _ a ((L.X.locs_mem _ _ a).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
    psi_eq := ⟨ψ0, h1, h2, fun a g => Sp.psi_eq a g _ (h2 _ g)⟩
    embedding_baseField_condition := h.embedding_baseField_condition }

set_option maxHeartbeats 4000000 in
theorem chSideL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) {cf : CharFrame D} {X : NExpTied D} {tp : TupTied D cf C}
    (h : ChoiceSide D cf M X C tp) : ChoiceSide (withLoc L) (cfL L cf) (mtL L M) (expL L X) (chL L C) (tpL L tp) := by
  exact {
    nct := nctL Sp h.nct
    choice := choiceL L h.choice
    off := h.off
    adm := h.adm
    psi := h.psi
    eMt_level := h.eMt_level }



set_option maxHeartbeats 4000000 in
def chiDL (L : LocAll (lay0 D)) (K : NC.NChiData D) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E) : NC.NChiData (withLoc L) :=
  { K with psi := ψ }

set_option maxHeartbeats 4000000 in
theorem chiL (L : LocAll (lay0 D)) {K : NC.NChiData D} (h : NC.NormalizedCharacterCompatibility D K) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) :
    NC.NormalizedCharacterCompatibility (withLoc L) (chiDL L K ψ) :=
  { h with psi := hψ }

set_option maxHeartbeats 4000000 in
theorem deltaReadL (L : LocAll (lay0 D)) {cf : CharFrame D} (h : DeltaRead D cf) : DeltaRead (withLoc L) (cfL L cf) := h


end GlobalTheory.HeightCounting.FitTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
noncomputable section

open NumberField ReciprocityTheory.Aut Formalism.BasicNotions

namespace GlobalTheory.AlgWtF

section Rat

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem includeL_injective : Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
  haveI : Nontrivial (AFplus L) := Formalism.L2.GlobalTheoryTheory.Br.finiteAdeleRing_nontrivial
  exact Algebra.TensorProduct.includeLeft_injective (S := L) (RingHom.injective _)

abbrev incGL : GL (Fin n) L →* GL (Fin n) (AL L) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)

theorem incGL_injective : Function.Injective (incGL (L := L) (n := n)) := by
  intro a b h
  apply Units.ext
  ext i j
  apply includeL_injective (L := L)
  have := congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) h
  simpa using this

theorem mem_incGL (γ : GQ L n) : ((γ : GA L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map incGL :=
  Subgroup.mem_subgroupOf.1 γ.2

def ratFun (γ : GQ L n) : GL (Fin n) L := (Subgroup.mem_map.1 (mem_incGL γ)).choose

theorem ratFun_mem (γ : GQ L n) : ratFun γ ∈ GQ0 L n := (Subgroup.mem_map.1 (mem_incGL γ)).choose_spec.1

theorem incGL_ratFun (γ : GQ L n) :
    incGL (L := L) (n := n) (ratFun γ) = ((γ : GA L n) : GL (Fin n) (AL L)) :=
  (Subgroup.mem_map.1 (mem_incGL γ)).choose_spec.2

def ratHom : GQ L n →* GL (Fin n) L where
  toFun := ratFun
  map_one' := incGL_injective (by rw [incGL_ratFun, map_one]; rfl)
  map_mul' γ δ := incGL_injective (by rw [map_mul, incGL_ratFun, incGL_ratFun, incGL_ratFun]; rfl)

theorem ratHom_mem (γ : GQ L n) : ratHom (L := L) (n := n) γ ∈ GQ0 L n := ratFun_mem γ

theorem ratHom_eq_of_match (γ : GQ L n) (γ₀ : GL (Fin n) L)
    (h : (((γ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom)) :
    γ₀ = ratHom (L := L) (n := n) γ := by
  apply incGL_injective
  rw [show ratHom (L := L) (n := n) γ = ratFun γ from rfl, incGL_ratFun]
  exact (Units.ext h).symm

end Rat

section Rep

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι] {K : Type} [Field K]

instance finVV (lam : ι → DomWeight n) : FiniteDimensional K (Formalism.L2.DIV.VV K lam) :=
  Module.Finite.of_basis (Formalism.L2.DIV.bVV K lam)

instance finDualVV (lam : ι → DomWeight n) : FiniteDimensional K (Module.Dual K (Formalism.L2.DIV.VV K lam)) := inferInstance

def embGLF (emb : ι → L →+* K) : GL (Fin n) L →* (ι → GL (Fin n) K) :=
  MonoidHom.pi fun τ => Matrix.GeneralLinearGroup.map (emb τ)

def tenRepF (emb : ι → L →+* K) (lam : ι → DomWeight n) :
    Representation K (GQ L n) (Formalism.L2.DIV.VV K lam) :=
  (Formalism.L2.DIV.rhoK lam).comp ((embGLF emb).comp ratHom)

def wtRepF (emb : ι → L →+* K) (lam : ι → DomWeight n) :
    Representation K (GQ L n) (Module.Dual K (Formalism.L2.DIV.VV K lam)) :=
  (tenRepF emb lam).dual

def CMDist (emb : ι → L →+* K) : Prop :=
  Function.Injective emb ∧ ∀ τ τ', emb τ ≠ (emb τ').comp (IsCMField.complexConj L : L →+* L)

end Rep

end GlobalTheory.AlgWtF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatIso

theorem heckeFunI_eq_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)) (h : GU Dv.σw n → ℂ)
    (hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0}) :
    ∃ (C : Finset (GAf L n ⧸ U)) (a : GAf L n ⧸ U → ℂ) (x : GAf L n ⧸ U → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n U Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ := by
  classical
  refine ⟨hfin.toFinset,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      Dv.hval h (Dv.loc hc.choose) else 0,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      hc.choose else 1, fun W _ _ φ => ?_⟩
  funext g
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · simp only [dif_pos hc]
      rfl
    · simp only [dif_neg hc, zero_smul]
      rfl
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · rw [dif_pos hc] at hc0
      rw [Set.Finite.coe_toFinset]
      refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
      rw [h0, zero_smul]
    · exact absurd (dif_neg hc) hc0

theorem satAt_of_iso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n)
    (hiso : π.Iso π') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0})
    (hs : NG.SatAt π Dv α) : NG.SatAt π' Dv α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  obtain ⟨T, hT⟩ := hiso.2
  refine ⟨(T ⟨f, hfS⟩ : π'.S), (T ⟨f, hfS⟩).2, ?_, U, ?_, hUv, ?_⟩
  · intro h0
    have h1 : T ⟨f, hfS⟩ = 0 := Subtype.ext h0
    have h2 : (⟨f, hfS⟩ : π.S) = 0 := T.map_eq_zero_iff.mp h1
    exact hf0 (congrArg Subtype.val h2)
  · intro κ hκ
    exact (hT κ ⟨f, hfS⟩ ⟨f, hfS⟩ (hU κ hκ).symm).symm
  · intro h hh
    obtain ⟨C, a, x, hC⟩ := heckeFunI_eq_sum Dv U h (hfin U hUv h hh)
    have e := hH h hh
    rw [hC] at e
    rw [hC]
    have e1 : (∑ c ∈ C, a c • (⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ : π.S)) =
        SatU Dv.ϖ (qV (maximalRealSubfield L) v) h α • (⟨f, hfS⟩ : π.S) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact e
    have e2 := congrArg (fun y => ((T y : π'.S) : GAf L n → π'.W)) e1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hT (x c) ⟨f, hfS⟩ ⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ rfl]

end GlobalTheory.SatIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIsoStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertSatakeParameters_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), (∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0}) → NG.SatAt π Dv α → NG.SatAt π' Dv α := by
  first | exact @GlobalTheory.SatIso.satAt_of_iso | exact GlobalTheory.SatIso.satAt_of_iso | (intros; apply GlobalTheory.SatIso.satAt_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

def wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :=
  Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
    {c | ∃ a : 𝓞 X.B.I.E, (∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) ∧
      c = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E)}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ}
    (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t : ZMod g) : Prop :=
  c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w

def argS (X : HidaSetting D) (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem otherInstanceCharacter_eq_psi_symmetricArgument (X : HidaSetting D) (x : X.B.I.Gf) :
    X.chi2 x = X.psiEf (divN X.B.I X.B.g (argS X x)) := rfl


open Classical in
def side (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Bool := decide (GlobalTheory.Mem.SymFrame.EwAt X w)

def wtA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wtB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem wt_add (ρ k : ℕ) (s : Bool) {r : ℕ} (i j : Fin r) :
    wtA ρ k s i j + wtB ρ k s i j = 1 ∨ wtA ρ k s i j + wtB ρ k s i j = -1 := by
  unfold wtA wtB
  split_ifs <;> simp

theorem hA_smul_right' (X : HidaSetting D) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (x y : VA X.B.I) :
    hA X.B.I x (c • y) = c * hA X.B.I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_add_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y + z) = hA X.B.I x y + hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_zero_right' (X : HidaSetting D) (x : VA X.B.I) : hA X.B.I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

private theorem hA_int_L {D : D7} (X : HidaSetting D) {x : VA X.B.I} (hx : x ∈ X.B.I.Lf) {y : Fin X.B.I.n → X.B.I.E} (hy : y ∈ X.B.I.L) :
    hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y i)) ∈
      Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  let I := X.B.I
  change hA I x (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) ∈
      Formalism.MainNotions.S.IntAf I.F I.E
  have hsig : ∀ c ∈ Formalism.MainNotions.S.IntAf I.F I.E,
      Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) c ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    have key : Formalism.MainNotions.S.IntAf I.F I.E ≤
        (Formalism.MainNotions.S.IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨a, ha⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩)
      · obtain ⟨a', rfl⟩ := ha
        show Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)
            ((algebraMap (𝓞 I.E) I.E a') ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) ∈
          Formalism.MainNotions.S.IntAf I.F I.E
        rw [Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        have hi : IsIntegral ℤ (I.cm.sig (algebraMap (𝓞 I.E) I.E a')) :=
          map_isIntegral_int I.cm.sig.toRingHom (RingOfIntegers.isIntegral_coe a')
        exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨⟨_, hi⟩, rfl⟩⟩, rfl⟩)
      · show Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)
            ((1 : I.E) ⊗ₜ[I.F] b) ∈ Formalism.MainNotions.S.IntAf I.F I.E
        rw [Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
        exact Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩)
    exact fun c hc => key hc
  have hx' : x ∈ Submodule.span (Formalism.MainNotions.S.IntAf I.F I.E)
      (Set.range fun z : I.L => fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((z : Fin I.n → I.E) i)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hz
    have h1 : hA I (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (a i))
        (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) =
        Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.UG.hform I.cm.sig.toRingHom I.J a y) := by
      simp only [hA, Formalism.UG.hform, Matrix.map_apply, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have he : Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)
            (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (a i)) =
          Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (I.cm.sig (a i)) := by
        show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Formalism.MainNotions.S.Af I.F)))
            (a i ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = (I.cm.sig (a i)) ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)
        rw [Algebra.TensorProduct.map_tmul]; rfl
      rw [he]; rfl
    rw [h1]
    exact Subring.subset_closure (Or.inl ⟨⟨_, (I.L_dual y).1 hy a ha⟩, rfl⟩)
  | zero =>
    have : hA I 0 (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) = 0 := by
      simp [hA, Formalism.UG.hform]
    rw [this]; exact zero_mem _
  | add u v _ _ hu hv =>
    have : hA I (u + v) (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) =
        hA I u (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) +
        hA I v (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) := by
      simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    rw [this]; exact add_mem hu hv
  | smul c u _ hu =>
    have : hA I (c • u) (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) =
        Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F) (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) *
        hA I u (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i)) := by
      simp only [hA, Formalism.UG.hform, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact mul_mem (hsig _ c.2) hu

theorem hA_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {x v : VA X.B.I} (hx : x ∈ X.B.I.Lf)
    (hv : v ∈ wLf X w) : hA X.B.I x v ∈ wInt X w := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hv
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, y', hy', rfl⟩ := hy
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) := by
        funext i; simp [map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hint : hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) ∈
          Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        hA_int_L X hx hy'
      rw [mul_comm]
      exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span ⟨a, ha, rfl⟩)
    | zero =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) = 0 := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) ∈ wInt X w
      rw [e, hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) =
          (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) +
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (b i)) := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) ∈ wInt X w
      rw [e, hA_add_right']; exact add_mem ha hb
    | smul c a _ ha =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) := by
        funext i; simp [Algebra.smul_def, map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hc : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        Formalism.UG.P.easyc_inclE_mem _ _ _ (by first | exact ⟨c, rfl⟩ | exact c.2 | simp [Formalism.UG.intOE])
      exact (wInt X w).smul_mem (⟨_, hc⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) ha
  | zero => rw [hA_zero_right']; exact zero_mem _
  | add a b _ _ ha hb => rw [hA_add_right']; exact add_mem ha hb
  | smul c a _ ha =>
    show hA X.B.I x ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ wInt X w
    rw [hA_smul_right']
    exact (wInt X w).smul_mem c ha

theorem hA_sub_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y - z) = hA X.B.I x y - hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_sum_right' (X : HidaSetting D) {ι : Type} (s : Finset ι) (x : VA X.B.I) (y : ι → VA X.B.I) :
    hA X.B.I x (∑ j ∈ s, y j) = ∑ j ∈ s, hA X.B.I x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hA_zero_right' X x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right', ih]

theorem hA_isMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : GlobalTheory.Mem.SymFrame.IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) -
      ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j) ∈ wInt X w := by
  have h := hA_mem_wInt X w hy (hN i)
  rw [hA_sub_right', hA_sum_right'] at h
  simpa only [hA_smul_right'] using h

theorem wInt_of_zmod (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : ZMod' X.B.I X.B.g c) : c ∈ wInt X w := by
  obtain ⟨t, ht, rfl⟩ := hc
  obtain ⟨m, hm⟩ : D.host.g k ∣ X.B.g := by
    rw [X.g_eq]; fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hgen : ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
    · simp
    · simp
  have e : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t =
      ((m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (D.host.g k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    rw [hm, Nat.cast_mul]; ring
  rw [e]
  exact (wInt X w).smul_mem (⟨_, mul_mem (natCast_mem _ m) ht⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hgen

end GlobalTheory.Mem.SymChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem eIdem_all : ∀ D : D7, EIdem D := by
  intro D
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let φ : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp (algebraMap ↥D.LL0 D.what₂.LL)
  have hφ : Function.Injective φ := φ.injective
  let M := MonoidAlgebra.mapRingHom (G0g D.nd) φ
  have hM : Function.Injective M := by
    intro x y h
    refine MonoidAlgebra.ext (Finsupp.ext fun g => hφ ?_)
    have := congrArg (fun z => z.coeff g) h
    simpa [M, MonoidAlgebra.mapRingHom] using this
  have he : M (eL D) = D.ntypes.e0 := by
    refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
    have := D.nStage_trivialCharacter_coeff_eq g
    simpa [M, eL, MonoidAlgebra.mapRingHom, φ] using this
  have hc : ∀ a, D.ntypes.e0 * a = a * D.ntypes.e0 := fun a => by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_comm _ a
  have hi : D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
    rw [← GlobalTheory.RowLev.ES_good]; exact GlobalTheory.RowLev.ES_mul_self _
  have hs : ∀ g : G0g D.nd, M (MonoidAlgebra.of _ _ g) = MonoidAlgebra.of _ _ g := fun g => by
    simp [M, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom]
  refine ⟨hM ?_, fun g => hM ?_⟩
  · rw [map_mul, he, hi]
  · rw [map_mul, map_mul, he, hs, hc]

end GlobalTheory.HeightCounting.FormsStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal : ∀ D : D7, EIdem D := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.eIdem_all | exact GlobalTheory.HeightCounting.FormsStep.eIdem_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.eIdem_all <;> assumption)
end
end
