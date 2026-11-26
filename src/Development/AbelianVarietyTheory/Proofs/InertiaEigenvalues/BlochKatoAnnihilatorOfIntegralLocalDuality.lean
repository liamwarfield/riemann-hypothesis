module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRestrictScalarsTraceForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRestrictScalarsTraceForm
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLatDescent

theorem dualLat_resQ : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  intro l _ P K LL _ _ O _ _ V _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ _ _ lam n e f h1 h2 h3 ρ ρ' L L' LZ LZ' hT hT' Pr PQ hPQ hP
  obtain ⟨⟨hg, hl, hr, hrk⟩, hlat⟩ := hP

  have key : ∀ z : LL, (∀ a : LL, lam (a * z) = 0) → z = 0 := by
    intro z hz
    rw [h3 z]
    simp [hz]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g x y
    rw [hPQ, GlobalTheory.PstCoeff.resQ_apply, GlobalTheory.PstCoeff.resQ_apply, hg, hPQ]
    have : ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) := by
      simp [cycLL]
    rw [this, ← Algebra.smul_def, map_smul, smul_eq_mul]
  · intro x hx
    apply hl
    intro y
    apply key
    intro a
    rw [← smul_eq_mul, ← map_smul, ← hPQ]
    exact hx _
  · intro y hy
    apply hr
    intro x
    apply key
    intro a
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, ← hPQ]
    exact hy _
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', hrk]
  · intro y
    rw [hT', hlat]
    constructor
    · intro H x hx
      obtain ⟨a, ha⟩ := H x ((hT x).1 hx)
      obtain ⟨z, hz⟩ := h2 a
      exact ⟨z, by rw [hPQ, ha, hz]; rfl⟩
    · intro H x hx
      have hi : ∀ i, ∃ z : ℤ_[l], lam (algebraMap O LL (f i) * Pr x y) = (z : ℚ_[l]) := by
        intro i
        have hm : f i • x ∈ L.T := L.T.smul_mem _ hx
        obtain ⟨z, hz⟩ := H _ ((hT _).2 hm)
        refine ⟨z, ?_⟩
        rw [hPQ, ← algebraMap_smul LL (f i) x, map_smul, LinearMap.smul_apply, smul_eq_mul] at hz
        rw [hz]; rfl
      choose z hz using hi
      have ho : ∀ i, ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z i : ℚ_[l]) := fun i => h1 (z i)
      choose o ho using ho
      refine ⟨∑ i, o i * e i, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h3 (Pr x y), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i, map_mul, ho i, Algebra.smul_def]

end GlobalTheory.DualLatDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRestrictScalarsTraceFormStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_restrictScalars_traceForm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')),
    (∀ v, v ∈ LZ.T ↔ v ∈ L.T) → (∀ v, v ∈ LZ'.T ↔ v ∈ L'.T) →
    ∀ (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]),
    (∀ x y, PQ x y = lam (Pr x y)) → IsDualLat1 (P.PD K) L L' Pr →
    IsDualLat1 (P.PD K) LZ LZ' PQ := by
  first | exact @GlobalTheory.DualLatDescent.dualLat_resQ | exact GlobalTheory.DualLatDescent.dualLat_resQ | (intros; apply GlobalTheory.DualLatDescent.dualLat_resQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlLatticeOfCoefficientLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlLatticeOfCoefficientLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory

theorem latticeZl_of_latticeO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (L : Lattice (O := O) ρ),
    ∃ LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ), ∀ v, v ∈ LZ.T ↔ v ∈ L.T := by
  intro l _ K LL _ _ O _ _ V _ _ _ _ _ _ _ _ lam n e f h1 h2 h3 ρ L

  have hz : ∀ (z : ℤ_[l]) (v : V), z • v = ((z : ℚ_[l]) : ℚ_[l]) • v := fun z v => by
    rw [← algebraMap_smul ℚ_[l] z v]; rfl

  have hdec : ∀ (a : LL) (t : V), a • t = ∑ i, lam (algebraMap O LL (f i) * a) • (e i • t) := by
    intro a t
    conv_lhs => rw [h3 a]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_assoc, algebraMap_smul]
  let TZ : Submodule ℤ_[l] V :=
    { carrier := (L.T : Set V)
      add_mem' := fun ha hb => L.T.add_mem ha hb
      zero_mem' := L.T.zero_mem
      smul_mem' := by
        intro z v hv
        obtain ⟨o, ho⟩ := h1 z
        show z • v ∈ L.T
        rw [hz, ← algebraMap_smul LL (z : ℚ_[l]) v, ← ho, algebraMap_smul]
        exact L.T.smul_mem o hv }
  have hmem : ∀ v, v ∈ TZ ↔ v ∈ L.T := fun v => Iff.rfl

  have hfg : TZ.FG := by
    obtain ⟨S, hS⟩ := L.fg
    classical
    refine ⟨Finset.image (fun p : Fin n × V => e p.1 • p.2) (Finset.univ ×ˢ S), ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_product, Set.mem_prod, Finset.coe_univ,
        Set.mem_univ, true_and, Finset.mem_coe] at hx
      obtain ⟨⟨i, t⟩, ht, rfl⟩ := hx
      have : t ∈ L.T := hS ▸ Submodule.subset_span ht
      exact L.T.smul_mem (e i) this
    · intro x hx
      have hx' : x ∈ Submodule.span O (S : Set V) := by rw [hS]; exact hx
      obtain ⟨c, -, rfl⟩ := (Submodule.mem_span_finset).1 hx'
      refine Submodule.sum_mem _ fun t ht => ?_
      rw [← algebraMap_smul LL (c t) t, hdec]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨z, hz'⟩ := h2 (f i * c t)
      rw [← map_mul, hz', ← hz]
      refine Submodule.smul_mem _ z (Submodule.subset_span ?_)
      simp only [Finset.coe_image, Set.mem_image, Finset.coe_product, Set.mem_prod, Finset.coe_univ,
        Set.mem_univ, true_and, Finset.mem_coe]
      exact ⟨(i, t), ht, rfl⟩
  have hfin : Module.Finite ℤ_[l] TZ := Module.Finite.iff_fg.mpr hfg
  have htf : Module.IsTorsionFree ℤ_[l] TZ := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro z x h
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    right
    have h' : ((z : ℚ_[l]) : ℚ_[l]) • (x : V) = 0 := by
      rw [← hz]; exact congrArg Subtype.val h
    have hq : (z : ℚ_[l]) ≠ 0 := fun h0 => hz0 (PadicInt.coe_eq_zero.1 h0)
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left hq)
  refine ⟨{ T := TZ, stable := ?_, fg := hfg, free := ?_, span := ?_ }, hmem⟩
  · intro g x hx
    exact L.stable g x hx
  · exact Module.free_of_finite_type_torsion_free'
  · let W : Submodule LL V :=
      { carrier := (Submodule.span ℚ_[l] (TZ : Set V) : Set V)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := by
          intro a x hx
          induction hx using Submodule.span_induction with
          | mem t ht =>
            show a • t ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [hdec]
            refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
            exact L.T.smul_mem (e i) ht
          | zero => simp
          | add x y _ _ hx hy =>
            show a • (x + y) ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [smul_add]; exact Submodule.add_mem _ hx hy
          | smul q x _ hx =>
            show a • (q • x) ∈ Submodule.span ℚ_[l] (TZ : Set V)
            rw [← algebraMap_smul LL q x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
            exact Submodule.smul_mem _ q hx }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← L.span, Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ht
    rw [eq_top_iff]
    intro v _
    have : v ∈ W := hW ▸ Submodule.mem_top
    exact this
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlLatticeOfCoefficientLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zlLattice_of_coefficientLattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (ρ : Representation LL ↥(GK K) V) (L : Lattice (O := O) ρ),
    ∃ LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ), ∀ v, v ∈ LZ.T ↔ v ∈ L.T := by
  first | exact @GlobalTheory.latticeZl_of_latticeO | exact GlobalTheory.latticeZl_of_latticeO | (intros; apply GlobalTheory.latticeZl_of_latticeO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundary
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory


open Submodule in
theorem cobO_iff_forall_lam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL))),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l]))),
    L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
    ∀ (z : ↥(GK K) × ↥(GK K) → LL),
    (CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x))) := by
  intro l _ P K LL _ _ O _ _ lam n e f h1 h2 h3 L1 hL1 L1Z hL1Z z
  classical
  have memT : ∀ x : LL, x ∈ L1.T ↔ ∃ o : O, algebraMap O LL o = x := by
    intro x; rw [hL1]; simp [LinearMap.mem_range]
  have memZ : ∀ q : ℚ_[l], q ∈ L1Z.T ↔ ∃ w : ℤ_[l], (w : ℚ_[l]) = q := by
    intro q; rw [hL1Z]; simp [LinearMap.mem_range]
  have actT : ∀ g (a : LL), (repD L1 g) (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * a) := by
    intro g a
    simp [repD, Submodule.mapQ_apply, charRep, cycLL, Algebra.smul_def]
  have actZ : ∀ g (q : ℚ_[l]), (repD L1Z g) (Submodule.Quotient.mk q) =
      Submodule.Quotient.mk (((P.PD K).χ g : ℚ_[l]) * q) := by
    intro g q
    simp [repD, Submodule.mapQ_apply, charRep, cycLL]
  have lamc : ∀ (o : O) (c : ℚ_[l]) (y : LL),
      lam (algebraMap O LL o * (algebraMap ℚ_[l] LL c * y)) = c * lam (algebraMap O LL o * y) := by
    intro o c y
    have : algebraMap O LL o * (algebraMap ℚ_[l] LL c * y) = c • (algebraMap O LL o * y) := by
      rw [Algebra.smul_def]; ring
    rw [this, map_smul, smul_eq_mul]
  unfold CobO ReciprocityTheory.Def.B2
  constructor
  · intro H o
    obtain ⟨F, ⟨hFc, -⟩, hF⟩ := Submodule.mem_map.1 H
    choose Ft hFt using fun g => Submodule.Quotient.mk_surjective L1.T (F g)
    have hFeq : F = fun g => Submodule.Quotient.mk (Ft g) := funext fun g => (hFt g).symm
    subst hFeq
    let φ : LL ⧸ L1.T → ℚ_[l] ⧸ L1Z.T := fun q =>
      Submodule.Quotient.mk (lam (algebraMap O LL o * (Submodule.Quotient.mk_surjective L1.T q).choose))
    have hφ : ∀ a, φ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (lam (algebraMap O LL o * a)) := by
      intro a
      have hc := (Submodule.Quotient.mk_surjective L1.T (Submodule.Quotient.mk a)).choose_spec
      rw [Submodule.Quotient.eq] at hc
      obtain ⟨o', ho'⟩ := (memT _).1 hc
      obtain ⟨w, hw⟩ := h2 (o * o')
      show Submodule.Quotient.mk _ = _
      rw [Submodule.Quotient.eq, memZ]
      exact ⟨w, by rw [← hw, map_mul, ho', mul_sub, map_sub]⟩
    refine Submodule.mem_map.2 ⟨φ ∘ (fun g => Submodule.Quotient.mk (Ft g)), ⟨hFc.comp φ, fun _ => trivial⟩, ?_⟩
    funext x
    have hx := congrFun hF x
    simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply] at hx ⊢
    rw [actT, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at hx
    obtain ⟨o', ho'⟩ := (memT _).1 hx
    obtain ⟨w, hw⟩ := h2 (o * o')
    rw [hφ, hφ, hφ, actZ, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memZ]
    refine ⟨w, ?_⟩
    rw [← hw, map_mul, ho', mul_sub, mul_add, mul_sub, map_sub, map_add (f := _), map_sub, lamc]
  · intro H
    choose Fz hFzc hFz using fun i => Submodule.mem_map.1 (H (f i))
    choose Ft hFt using fun i g => Submodule.Quotient.mk_surjective L1Z.T (Fz i g)
    refine Submodule.mem_map.2 ⟨fun g => Submodule.Quotient.mk
      (∑ i, algebraMap ℚ_[l] LL (Ft i g) * algebraMap O LL (e i)), ⟨?_, fun _ => trivial⟩, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      have hev : ∀ᶠ y in nhds x, ∀ i, Fz i y = Fz i x :=
        Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hFzc i).1 x
      filter_upwards [hev] with y hy
      rw [Submodule.Quotient.eq, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hyi := hy i
      rw [← hFt i y, ← hFt i x, Submodule.Quotient.eq, memZ] at hyi
      obtain ⟨w, hw⟩ := hyi
      obtain ⟨o, ho⟩ := h1 w
      rw [memT]
      exact ⟨o * e i, by rw [map_mul, ho, hw, ← sub_mul, map_sub]⟩
    · funext x
      have key : ∀ i, ∃ w : ℤ_[l], (w : ℚ_[l]) = ((P.PD K).χ x.1 : ℚ_[l]) * Ft i x.2 - Ft i (x.1 * x.2)
          + Ft i x.1 - lam (algebraMap O LL (f i) * z x) := by
        intro i
        have hx := congrFun (hFz i) x
        simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk] at hx
        rw [← hFt i x.2, ← hFt i (x.1 * x.2), ← hFt i x.1, actZ, ← Submodule.Quotient.mk_sub,
          ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memZ] at hx
        exact hx
      choose w hw using key
      choose o ho using fun i => h1 (w i)
      simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk]
      rw [actT, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, memT]
      refine ⟨∑ i, o i * e i, ?_⟩
      have hl : ∀ i, lam (algebraMap O LL (f i) * z x) = ((P.PD K).χ x.1 : ℚ_[l]) * Ft i x.2
          - Ft i (x.1 * x.2) + Ft i x.1 - (w i : ℚ_[l]) := fun i => by rw [hw i]; ring
      conv_rhs => rw [h3 (z x)]
      simp_rw [hl]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ho, Algebra.smul_def]
      simp only [map_sub, map_add (f := _), map_mul]
      ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundaryStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundaryMod_iff_forall_traceForm_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL))),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l]))),
    L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
    ∀ (z : ↥(GK K) × ↥(GK K) → LL),
    (CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x))) := by
  first | exact @GlobalTheory.cobO_iff_forall_lam | exact GlobalTheory.cobO_iff_forall_lam | (intros; apply GlobalTheory.cobO_iff_forall_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctional
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.IntDual

theorem lattice_basis (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ_[l] LL),
      (∀ i, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (b i)) ∧
      ∀ x : LL, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x →
        ∀ i, ∃ z : ℤ_[l], b.repr x i = (z : ℚ_[l]) := by
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure ℤ_[l] LL
  haveI : IsIntegralClosure S ℤ_[l] LL := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] S := IsIntegralClosure.finite ℤ_[l] ℚ_[l] LL S
  have hinj : Function.Injective (algebraMap ℤ_[l] LL) := by
    intro a c h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] LL).injective h)
  haveI : Module.IsTorsionFree ℤ_[l] S := ⟨fun r hr a c hac => by
    have hr0 : algebraMap ℤ_[l] LL r ≠ 0 := by
      intro h0; exact hr.ne_zero (hinj (h0.trans (map_zero _).symm))
    apply Subtype.ext
    have h1 := congrArg (fun s : S => (s : LL)) hac
    simp only [Subalgebra.coe_smul, Algebra.smul_def] at h1
    exact mul_left_cancel₀ hr0 h1⟩
  haveI : Module.Free ℤ_[l] S := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[l])) LL :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] LL S
  let bO := (Module.Free.chooseBasis ℤ_[l] S).reindex (Fintype.equivFin _)
  let b := bO.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) LL
  have hb : ∀ i, b i = (bO i : LL) := fun i => Module.Basis.localizationLocalization_apply _ _ _ _ i
  refine ⟨_, b, fun i => ?_, fun x hx i => ?_⟩
  · rw [hb]; exact (bO i).2
  · have := bO.localizationLocalization_repr_algebraMap ℚ_[l] (nonZeroDivisors ℤ_[l]) LL ⟨x, hx⟩ i
    exact ⟨bO.repr ⟨x, hx⟩ i, this⟩

theorem intDual_coef : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  intro l _ LL _ _ _ O _ _ hO
  have H := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hfd, -, -, -⟩ := hO
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  haveI := hfd
  have hmem := H.1
  obtain ⟨n, b, hbint, hcoord⟩ := lattice_basis l LL
  let ι := algebraMap O LL
  have hιinj : Function.Injective ι := IsFractionRing.injective O LL
  let Tr := Algebra.trace ℚ_[l] LL
  let B := Algebra.traceForm ℚ_[l] LL
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ_[l] LL
  let f' := B.dualBasis hB b
  have hcoef : ∀ x i, Tr (f' i * x) = b.repr x i := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    have : ∀ j, Tr (f' i * (b.repr x j • b j)) = b.repr x j * (if j = i then 1 else 0) := by
      intro j
      rw [mul_smul_comm, map_smul, smul_eq_mul, ← LinearMap.BilinForm.apply_dualBasis_left hB b i j]
      rfl
    simp_rw [this, mul_ite, mul_one, mul_zero]
    simp

  let Zs : Subring ℚ_[l] := (algebraMap ℤ_[l] ℚ_[l]).range
  have hZ : ∀ q : ℚ_[l], q ∈ Zs ↔ ∃ z : ℤ_[l], q = (z : ℚ_[l]) := by
    intro q; constructor
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
  have hintO : ∀ o : O, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (ι o) :=
    fun o => (hmem (ι o)).1 ⟨o, rfl⟩
  have hf'M : ∀ i (s : O), Tr (f' i * ι s) ∈ Zs := by
    intro i s
    obtain ⟨z, hz⟩ := hcoord (ι s) (hintO s) i
    rw [hcoef, hZ]; exact ⟨z, hz⟩
  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n)) f'
  let D := ι c
  have hD : D ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero ⟨c, hc⟩ (hιinj (h0.trans (map_zero ι).symm))
  have ho : ∀ i, ∃ o : O, ι o = D * f' i := by
    intro i
    obtain ⟨o, ho⟩ := hcint i (Finset.mem_univ i)
    exact ⟨o, by rw [ho, Algebra.smul_def]⟩
  choose o hoD using ho
  let I : Ideal O :=
    { carrier := {a | ∀ s : O, Tr (D⁻¹ * ι a * ι s) ∈ Zs}
      add_mem' := by
        intro a a' ha ha' s
        have e : D⁻¹ * ι (a + a') * ι s = D⁻¹ * ι a * ι s + D⁻¹ * ι a' * ι s := by
          rw [map_add (f := _)]; ring
        rw [e, map_add (f := _)]; exact Zs.add_mem (ha s) (ha' s)
      zero_mem' := by
        intro s; simp only [map_zero, mul_zero, zero_mul]; exact Zs.zero_mem
      smul_mem' := by
        intro r a ha s
        have e : D⁻¹ * ι (r • a) * ι s = D⁻¹ * ι a * ι (r * s) := by
          rw [smul_eq_mul, map_mul, map_mul]; ring
        rw [e]; exact ha (r * s) }
  have hoI : ∀ i, o i ∈ I := by
    intro i s
    show Tr (D⁻¹ * ι (o i) * ι s) ∈ Zs
    rw [hoD i, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
    exact hf'M i s
  let g := Submodule.IsPrincipal.generator I
  have hgI : g ∈ I := Submodule.IsPrincipal.generator_mem I
  have ha : ∀ i, ∃ a : O, a * g = o i := by
    intro i
    have h := hoI i
    rw [← Submodule.IsPrincipal.span_singleton_generator I] at h
    exact Ideal.mem_span_singleton'.1 h
  choose a hag using ha
  let δ := D⁻¹ * ι g
  let lam : LL →ₗ[ℚ_[l]] ℚ_[l] := Tr.comp (LinearMap.mulLeft ℚ_[l] δ)
  have hlam : ∀ y, lam y = Tr (δ * y) := fun y => rfl
  have hδa : ∀ i, δ * ι (a i) = f' i := by
    intro i
    show D⁻¹ * ι g * ι (a i) = f' i
    rw [mul_assoc, ← map_mul, mul_comm g, hag, hoD, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  have he : ∀ i, ∃ e : O, ι e = b i := fun i => (hmem (b i)).2 (hbint i)
  choose e he using he
  refine ⟨lam, n, e, a, fun z => ?_, fun y => ?_, fun x => ?_⟩
  · have hz : ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem
        (algebraMap ℚ_[l] LL (z : ℚ_[l])) := RingHom.isIntegralElem_map _
    exact (hmem _).2 hz
  · have h := hgI y
    rw [hZ] at h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by rw [hlam]; exact hz⟩
  · conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlam, ← mul_assoc, hδa, hcoef, he]
end GlobalTheory.IntDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctionalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_functional : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  first | exact @GlobalTheory.IntDual.intDual_coef | exact GlobalTheory.IntDual.intDual_coef | (intros; apply GlobalTheory.IntDual.intDual_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDuality
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKIntDescent

theorem modTop_trans {F LL : Type} [Field F] [Field LL] [Algebra F LL] [TopologicalSpace F]
    [TopologicalSpace LL] [IsTopologicalRing LL] [IsModuleTopology F LL] (V : Type)
    [AddCommGroup V] [Module LL V] [Module F V] [IsScalarTower F LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology F V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e := (Module.finBasis LL V).equivFun
  let e' : (Fin (finrank LL V) → LL) ≃L[F] V :=
    { e.symm.restrictScalars F with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap }
  exact IsModuleTopology.iso e'

theorem csmul_trans {F LL V : Type} [Field F] [Field LL] [Algebra F LL] [AddCommGroup V] [Module LL V]
    [Module F V] [IsScalarTower F LL V] [TopologicalSpace V] [ContinuousConstSMul LL V] :
    ContinuousConstSMul F V :=
  ⟨fun c => by simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap F LL c)⟩

variable {l : ℕ} [Fact l.Prime]

theorem actVB_resQ (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD K) (GlobalTheory.PstCoeff.resQ ρ) g x = actVB (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

section Coch
variable (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V)

theorem mem_continuousCocycles_restrictScalars_Ql (c : ↥(GK K) → V) : c ∈ continuousCocycles (GlobalTheory.PstCoeff.resQ ρ) ↔ c ∈ continuousCocycles ρ := Iff.rfl

theorem mem_finiteCocycles_restrictScalars_Ql (c : ↥(GK K) → V) :
    c ∈ finiteCocycles (P.PD K) (GlobalTheory.PstCoeff.resQ ρ) ↔ c ∈ finiteCocycles (P.PD K) ρ := by
  change (c ∈ continuousCocycles _ ∧ ∃ x, ∀ g, _ = _) ↔ (c ∈ continuousCocycles _ ∧ ∃ x, ∀ g, _ = _)
  simp only [actVB_resQ, mem_continuousCocycles_restrictScalars_Ql]

end Coch

section Tor
variable {K : FinExt l}

theorem mk_liftD {LL O V G : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] [Group G] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (y : V ⧸ L.T) : Submodule.Quotient.mk (liftD L y) = y :=
  (Submodule.Quotient.mk_surjective _ y).choose_spec

theorem mem_Z1T_iff {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL ↥(GK K) V} [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (d : ↥(GK K) → V) :
    d ∈ latticeCocycles L ↔ d ∈ continuousCocycles ρ ∧ ∀ g, d g ∈ L.T := by
  simp only [latticeCocycles, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_pi, Set.mem_univ,
    true_implies]

theorem exists_quotEquiv {R S V : Type} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V] [Module S V]
    (N : Submodule R V) (M : Submodule S V) (h : ∀ v, v ∈ M ↔ v ∈ N) :
    ∃ q : (V ⧸ N) ≃+ (V ⧸ M), ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
  have e : N.toAddSubgroup = M.toAddSubgroup := by ext v; exact (h v).symm
  exact ⟨QuotientAddGroup.quotientAddEquivOfEq e, fun v => rfl⟩

variable {LL O V : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [Module O V]
  [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation LL ↥(GK K) V}

theorem q_actD (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (q : (V ⧸ L.T) ≃+ (V ⧸ LZ.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (g : ↥(GK K)) (y : V ⧸ L.T) : q (actD L g y) = actD LZ g (q y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hq]
  change q (Submodule.Quotient.mk (ρ g v)) = Submodule.Quotient.mk (GlobalTheory.PstCoeff.resQ ρ g v)
  rw [hq]
  rfl

theorem mem_quotientCocycles_iff (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (q : (V ⧸ L.T) ≃+ (V ⧸ LZ.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (c : ↥(GK K) → V ⧸ L.T) : c ∈ divisibleCocycles L ↔ (fun g => q (c g)) ∈ divisibleCocycles LZ := by
  change (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actD L g (c h)) ↔
    (IsLocallyConstant (fun g => q (c g)) ∧ ∀ g h, q (c (g * h)) = q (c g) + actD LZ g (q (c h)))
  refine and_congr ⟨fun h => h.comp q, fun h => IsLocallyConstant.desc c q h q.injective⟩ ?_
  refine forall₂_congr fun g h => ?_
  rw [← q_actD L LZ q hq, ← map_add (f := _)]
  exact q.injective.eq_iff.symm

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]

theorem mem_HfD_iff (P : LocPrime l) (L : Lattice (O := O) ρ) (c : ↥(GK K) → V ⧸ L.T) :
    c ∈ HfD (P.PD K) L ↔ ∃ z ∈ finiteCocycles (P.PD K) ρ, ∃ v : V, ∀ g, c g = Submodule.Quotient.mk (z g + (ρ g v - v)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz1, rfl⟩, _, ⟨v, rfl⟩, h⟩ := Submodule.mem_sup.1 hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨z, hz1, v, fun g => (congrFun h g).symm⟩
  · rintro ⟨z, hz, v, h⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk v, rfl⟩, funext fun g => (h g).symm⟩

theorem mem_HfD_iffZ (P : LocPrime l) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (c : ↥(GK K) → V ⧸ LZ.T) :
    c ∈ HfD (P.PD K) LZ ↔ ∃ z ∈ finiteCocycles (P.PD K) (GlobalTheory.PstCoeff.resQ ρ), ∃ v : V,
      ∀ g, c g = Submodule.Quotient.mk (z g + (ρ g v - v)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz1, rfl⟩, _, ⟨v, rfl⟩, h⟩ := Submodule.mem_sup.1 hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨z, hz1, v, fun g => (congrFun h g).symm⟩
  · rintro ⟨z, hz, v, h⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk v, rfl⟩, funext fun g => (h g).symm⟩

theorem HfD_iff (P : LocPrime l) (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (q : (V ⧸ L.T) ≃+ (V ⧸ LZ.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (c : ↥(GK K) → V ⧸ L.T) : c ∈ HfD (P.PD K) L ↔ (fun g => q (c g)) ∈ HfD (P.PD K) LZ := by
  rw [mem_HfD_iff, mem_HfD_iffZ]
  refine exists_congr fun z => and_congr (mem_finiteCocycles_restrictScalars_Ql P ρ z).symm
    (exists_congr fun v => forall_congr' fun g => ?_)
  rw [← hq, q.injective.eq_iff]

theorem mem_Z1T_Z (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (hLZ : ∀ v, v ∈ LZ.T ↔ v ∈ L.T) (d : ↥(GK K) → V) : d ∈ latticeCocycles LZ ↔ d ∈ latticeCocycles L := by
  rw [mem_Z1T_iff, mem_Z1T_iff, mem_continuousCocycles_restrictScalars_Ql]
  simp only [hLZ]

theorem mem_Z1fT_Z (P : LocPrime l) (L : Lattice (O := O) ρ) (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ))
    (hLZ : ∀ v, v ∈ LZ.T ↔ v ∈ L.T) (d : ↥(GK K) → V) : d ∈ latticeFiniteCocycles (P.PD K) LZ ↔ d ∈ latticeFiniteCocycles (P.PD K) L := by
  simp only [latticeFiniteCocycles, Submodule.mem_inf, Submodule.restrictScalars_mem, mem_Z1T_Z L LZ hLZ, mem_finiteCocycles_restrictScalars_Ql]

end Tor

section Cup
variable {K : FinExt l} {LL O V V' : Type} [Field LL] [Algebra ℚ_[l] LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] [Module O V']
  [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'}

theorem cup_smul_left (L' : Lattice (O := O) ρ') (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (o : O)
    (d : ↥(GK K) → V) (c : ↥(GK K) → V' ⧸ L'.T) (x : ↥(GK K) × ↥(GK K)) :
    cupLD L' Pr (o • d) c x = algebraMap O LL o * cupLD L' Pr d c x := by
  simp only [cupLD, Pi.smul_apply, ← algebraMap_smul LL o (d x.1), map_smul, LinearMap.smul_apply,
    smul_eq_mul]

theorem cup_smul_right (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (Pr : V →ₗ[LL] V' →ₗ[LL] LL)
    (hT : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, Pr x y = algebraMap O LL a) (o : O)
    (d : ↥(GK K) → V) (hd : ∀ g, d g ∈ L.T) (c : ↥(GK K) → V' ⧸ L'.T) (x : ↥(GK K) × ↥(GK K)) :
    ∃ a : O, algebraMap O LL o * cupLD L' Pr d c x - cupLD L' Pr d (o • c) x = algebraMap O LL a := by
  have h1 : o • liftD L' (c x.2) - liftD L' ((o • c) x.2) ∈ L'.T := by
    refine (Submodule.Quotient.eq _).1 ?_
    rw [Submodule.Quotient.mk_smul, mk_liftD, mk_liftD]
    rfl
  obtain ⟨a, ha⟩ := hT _ (hd x.1) _ (L'.stable x.1 _ h1)
  refine ⟨a, ?_⟩
  have e1 : ρ' x.1 (o • liftD L' (c x.2)) = algebraMap O LL o • ρ' x.1 (liftD L' (c x.2)) := by
    rw [← algebraMap_smul LL o, map_smul]
  rw [← ha, map_sub, map_sub, e1, map_smul, smul_eq_mul]
  rfl

theorem cup_congr (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (Pr : V →ₗ[LL] V' →ₗ[LL] LL)
    (hT : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ a : O, Pr x y = algebraMap O LL a)
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ')) (hLZ' : ∀ v, v ∈ LZ'.T ↔ v ∈ L'.T)
    (q : (V' ⧸ L'.T) ≃+ (V' ⧸ LZ'.T)) (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk v)
    (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]) (hPQ : ∀ x y, PQ x y = lam (Pr x y))
    (d : ↥(GK K) → V) (hd : ∀ g, d g ∈ L.T) (c : ↥(GK K) → V' ⧸ L'.T) (x : ↥(GK K) × ↥(GK K)) :
    ∃ z : ℤ_[l], lam (cupLD L' Pr d c x) - cupLD LZ' PQ d (fun g => q (c g)) x = (z : ℚ_[l]) := by
  have h1 : liftD L' (c x.2) - liftD LZ' (q (c x.2)) ∈ L'.T := by
    rw [← hLZ']
    refine (Submodule.Quotient.eq _).1 ?_
    rw [mk_liftD, ← hq, mk_liftD]
  obtain ⟨a, ha⟩ := hT _ (hd x.1) _ (L'.stable x.1 _ h1)
  obtain ⟨z, hz⟩ := hlam a
  refine ⟨z, ?_⟩
  rw [← hz, ← ha, map_sub, map_sub, map_sub]
  simp only [cupLD, hPQ, GlobalTheory.PstCoeff.resQ_apply]

end Cup

theorem cobO_congr (P : LocPrime l) (K : FinExt l) (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l])))
    (hL1Z : L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l])) (z z' : ↥(GK K) × ↥(GK K) → ℚ_[l])
    (h : ∀ x, ∃ a : ℤ_[l], z x - z' x = (a : ℚ_[l])) : CobO (P.PD K) L1Z z ↔ CobO (P.PD K) L1Z z' := by
  have e : (fun x => (Submodule.Quotient.mk (z x) : ℚ_[l] ⧸ L1Z.T)) = fun x => Submodule.Quotient.mk (z' x) := by
    funext x
    refine (Submodule.Quotient.eq _).2 ?_
    obtain ⟨a, ha⟩ := h x
    rw [hL1Z, ha]
    exact ⟨a, rfl⟩
  unfold CobO
  rw [e]

theorem coef_data (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) :=
  GlobalTheory.T.exists_integral_dual_functional l LL O hO

theorem cobO_iff (P : LocPrime l) (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {O : Type} [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O)
    (hZ : ∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l]))
    (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (hrec : ∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i))
    (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l])))
    (hL1Z : L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]))
    (z : ↥(GK K) × ↥(GK K) → LL) :
    CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x)) :=
  GlobalTheory.T.coboundaryMod_iff_forall_traceForm_coboundary l P K LL O lam n e f hZ hlam hrec L1 hL1 L1Z hL1Z z

theorem exists_latZ (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O)
    (hZ : ∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l]))
    (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (hrec : ∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i))
    (ρ : Representation LL ↥(GK K) V) (L : Lattice (O := O) ρ) :
    ∃ LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ), ∀ v, v ∈ LZ.T ↔ v ∈ L.T :=
  GlobalTheory.T.zlLattice_of_coefficientLattice l K LL O V lam n e f hZ hlam hrec ρ L

theorem dualLatZ (P : LocPrime l) (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [Module O V] [IsScalarTower O LL V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module O V'] [IsScalarTower O LL V'] [Module ℤ_[l] V'] [IsScalarTower ℤ_[l] ℚ_[l] V']
    [FiniteDimensional ℚ_[l] LL] [FiniteDimensional LL V] [FiniteDimensional LL V']
    (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O)
    (hZ : ∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l]))
    (hlam : ∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l]))
    (hrec : ∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i))
    (ρ : Representation LL ↥(GK K) V) (ρ' : Representation LL ↥(GK K) V')
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ')
    (LZ : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ)) (LZ' : Lattice (O := ℤ_[l]) (GlobalTheory.PstCoeff.resQ ρ'))
    (hLZ : ∀ v, v ∈ LZ.T ↔ v ∈ L.T) (hLZ' : ∀ v, v ∈ LZ'.T ↔ v ∈ L'.T)
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (PQ : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l])
    (hPQ : ∀ x y, PQ x y = lam (Pr x y)) (hP : IsDualLat1 (P.PD K) L L' Pr) :
    IsDualLat1 (P.PD K) LZ LZ' PQ :=
  GlobalTheory.T.dualLattice_restrictScalars_traceForm l P K LL O V V' lam n e f hZ hlam hrec ρ ρ' L L' LZ LZ' hLZ hLZ' Pr PQ hPQ hP

theorem bkBCore_of_integralDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l),
    GlobalTheory.Published.BlochKato.IntegralDuality (P.PD K) → bkBCore (P.PD K) := by
  intro l _ P K hI LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' Pr hdR hP
  obtain ⟨lam, n, e, f, hZ, hlam, hrec⟩ := coef_data LL O hO
  haveI : FiniteDimensional ℚ_[l] LL := hO.2.1
  haveI : IsModuleTopology ℚ_[l] LL := hO.2.2.1
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  letI : Module ℤ_[l] A.V := Module.compHom A.V (algebraMap ℤ_[l] ℚ_[l])
  letI : Module ℤ_[l] A'.V := Module.compHom A'.V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] A.V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℤ_[l] ℚ_[l] A'.V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : FiniteDimensional ℚ_[l] A'.V := Module.Finite.trans LL A'.V
  haveI : IsModuleTopology ℚ_[l] A.V := modTop_trans (LL := LL) A.V
  haveI : IsModuleTopology ℚ_[l] A'.V := modTop_trans (LL := LL) A'.V
  haveI : ContinuousConstSMul ℚ_[l] A.V := csmul_trans (LL := LL)
  haveI : ContinuousConstSMul ℚ_[l] A'.V := csmul_trans (LL := LL)
  obtain ⟨LZ, hLZ⟩ := exists_latZ K lam n e f hZ hlam hrec A.ρ LA
  obtain ⟨LZ', hLZ'⟩ := exists_latZ K lam n e f hZ hlam hrec A'.ρ LA'
  obtain ⟨L1Z, hL1Z⟩ := GlobalTheory.Published.BlochKato.exists_cyclotomicLattice l P K
  obtain ⟨q, hq⟩ := exists_quotEquiv LA'.T LZ'.T hLZ'
  let PQ : A.V →ₗ[ℚ_[l]] A'.V →ₗ[ℚ_[l]] ℚ_[l] := LinearMap.mk₂ ℚ_[l] (fun x y => lam (Pr x y))
    (fun x x' y => by beta_reduce; rw [map_add (f := _), LinearMap.add_apply, map_add (f := _)])
    (fun c x y => by
      beta_reduce
      rw [← algebraMap_smul LL c x, map_smul, LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul])
    (fun x y y' => by beta_reduce; rw [map_add (f := _), map_add (f := _)])
    (fun c x y => by
      beta_reduce
      rw [← algebraMap_smul LL c y, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul])
  have hPQ : ∀ x y, PQ x y = lam (Pr x y) := fun _ _ => rfl
  have hdRQ : IsDR (P.PD K) (GlobalTheory.PstCoeff.resQ A.ρ) := (GlobalTheory.PstCoeff.isDR_resQ_iff P A.ρ).mpr hdR
  have hPZ := dualLatZ P K lam n e f hZ hlam hrec A.ρ A'.ρ LA LA' LZ LZ' hLZ hLZ' Pr PQ hPQ hP
  obtain ⟨H1, H2⟩ := hI L1Z hL1Z A.V A'.V (GlobalTheory.PstCoeff.resQ A.ρ) (GlobalTheory.PstCoeff.resQ A'.ρ) LZ LZ' PQ
    A.cont A'.cont hdRQ hPZ
  have hT : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, ∃ a : O, Pr x y = algebraMap O LL a :=
    fun x hx y hy => (hP.2 y).1 hy x hx
  have hval : ∀ d, d ∈ latticeCocycles LA → ∀ g, d g ∈ LA.T := fun d hd => ((mem_Z1T_iff LA d).1 hd).2
  have key := cobO_iff P K lam n e f hZ hlam hrec L1 hL1 L1Z hL1Z
  have down : ∀ d : ↥(GK K) → A.V, (∀ g, d g ∈ LA.T) → ∀ c : ↥(GK K) → A'.V ⧸ LA'.T,
      CobO (P.PD K) L1 (cupLD LA' Pr d c) → CobO (P.PD K) L1Z (cupLD LZ' PQ d (fun g => q (c g))) := by
    intro d hd c h
    have h1 := (key _).1 h 1
    simp only [map_one, one_mul] at h1
    exact (cobO_congr P K L1Z hL1Z _ _ (cup_congr LA LA' Pr hT lam hlam LZ' hLZ' q hq PQ hPQ d hd c)).1 h1
  refine ⟨fun c hc => ?_, fun d hd => ?_⟩
  · have hc' := (mem_quotientCocycles_iff LA' LZ' q hq c).1 hc
    rw [HfD_iff P LA' LZ' q hq c, H1 _ hc']
    constructor
    · intro h d hd
      refine (key _).2 fun o => ?_
      have hod : o • d ∈ latticeFiniteCocycles (P.PD K) LA := Submodule.smul_mem _ o hd
      have e1 : (fun x => lam (algebraMap O LL o * cupLD LA' Pr d c x)) =
          fun x => lam (cupLD LA' Pr (o • d) c x) := by
        funext x
        rw [cup_smul_left]
      rw [e1]
      refine (cobO_congr P K L1Z hL1Z _ _ (cup_congr LA LA' Pr hT lam hlam LZ' hLZ' q hq PQ hPQ (o • d)
        (hval _ (Submodule.mem_inf.1 hod).1) c)).2 ?_
      exact h _ ((mem_Z1fT_Z P LA LZ hLZ _).2 hod)
    · intro h d hd
      have hd' := (mem_Z1fT_Z P LA LZ hLZ d).1 hd
      exact down d (hval d (Submodule.mem_inf.1 hd').1) c (h d hd')
  · have hdZ := (mem_Z1T_Z LA LZ hLZ d).2 hd
    rw [← mem_Z1fT_Z P LA LZ hLZ d, H2 d hdZ]
    constructor
    · intro h c hc hcf
      refine (key _).2 fun o => ?_
      have hoc : o • c ∈ divisibleCocycles LA' := Submodule.smul_mem _ o hc
      have hocf : o • c ∈ HfD (P.PD K) LA' := Submodule.smul_mem _ o hcf
      have h3 := h _ ((mem_quotientCocycles_iff LA' LZ' q hq _).1 hoc) ((HfD_iff P LA' LZ' q hq _).1 hocf)
      refine (cobO_congr P K L1Z hL1Z _ _ fun x => ?_).2 h3
      obtain ⟨a, ha⟩ := cup_smul_right LA LA' Pr hT o d (hval d hd) c x
      obtain ⟨z1, hz1⟩ := hlam a
      obtain ⟨z2, hz2⟩ := cup_congr LA LA' Pr hT lam hlam LZ' hLZ' q hq PQ hPQ d (hval d hd) (o • c) x
      refine ⟨z1 + z2, ?_⟩
      rw [PadicInt.coe_add, ← hz1, ← hz2, ← ha, map_sub]
      ring
    · intro h c' hc' hcf'
      obtain ⟨c, rfl⟩ : ∃ c : ↥(GK K) → A'.V ⧸ LA'.T, (fun g => q (c g)) = c' :=
        ⟨fun g => q.symm (c' g), funext fun g => q.apply_symm_apply _⟩
      exact down d (hval d hd) c (h c ((mem_quotientCocycles_iff LA' LZ' q hq c).2 hc') ((HfD_iff P LA' LZ' q hq c).2 hcf'))

end GlobalTheory.BKIntDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDualityStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.IntegralDuality (P.PD K) → bkBCore (P.PD K) := by
  first | exact @GlobalTheory.BKIntDescent.bkBCore_of_integralDuality | exact GlobalTheory.BKIntDescent.bkBCore_of_integralDuality | (intros; apply GlobalTheory.BKIntDescent.bkBCore_of_integralDuality <;> assumption)
end
