module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CompactRepField

open Polynomial IntermediateField

theorem exists_mem_adjoin_simple (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (j : Ω →+* PadicAlgCl l) (x : PadicAlgCl l) : ∃ y : Ω, x ∈ ℚ_[l]⟮j y⟯ := by
  have hint : ∀ z : PadicAlgCl l, IsIntegral ℚ_[l] z := fun z =>
    (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hfin : ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (PadicAlgCl l)).subset fun x' hx' => ?_
    exact (isConjRoot_iff_mem_minpoly_rootSet (hint x)).1 hx'.1
  have hop : IsOpen (⋂ x' ∈ ({x' | IsConjRoot ℚ_[l] x x' ∧ x ≠ x'} : Set (PadicAlgCl l)),
      {y : PadicAlgCl l | ‖x - y‖ < ‖x - x'‖}) :=
    hfin.isOpen_biInter fun x' _ => isOpen_lt (by fun_prop) continuous_const
  obtain ⟨y, hy⟩ := (GlobalTheory.denseRange_of_isAlgClosed_padicAlgCl l Ω j).exists_mem_open hop
    ⟨x, by
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, sub_self, norm_zero, norm_pos_iff, sub_ne_zero]
      exact fun x' h => h.2⟩
  refine ⟨y, IsKrasner.krasner (minpoly.irreducible (hint x)).separable (IsAlgClosed.splits _)
    (hint _) fun x' h1 h2 => ?_⟩
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy
  exact hy x' ⟨h1, h2⟩

theorem exists_countable_family (l : ℕ) [Fact l.Prime] :
    ∃ (ι : Type) (_ : Countable ι) (K : ι → IntermediateField ℚ_[l] (PadicAlgCl l)),
      (∀ i, FiniteDimensional ℚ_[l] (K i)) ∧
      ∀ s : Set (PadicAlgCl l), s.Finite → ∃ i, s ⊆ K i := by
  classical
  haveI halg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Countable (AlgebraicClosure ℚ) := by
    have h : {x : AlgebraicClosure ℚ | IsAlgebraic ℚ x}.Countable := Algebraic.countable ℚ _
    exact Set.countable_univ_iff.1 (h.mono fun x _ => halg.isAlgebraic x)
  let j : AlgebraicClosure ℚ →+* PadicAlgCl l :=
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := PadicAlgCl l)).toRingHom
  refine ⟨Finset (AlgebraicClosure ℚ), inferInstance,
    fun S => IntermediateField.adjoin ℚ_[l] (j '' (S : Set _)), fun S => ?_, fun s hs => ?_⟩
  · haveI : Finite (j '' (S : Set (AlgebraicClosure ℚ))) := (S.finite_toSet.image j).to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  · choose y hy using exists_mem_adjoin_simple l (AlgebraicClosure ℚ) j
    refine ⟨(hs.image y).toFinset, fun x hx => ?_⟩
    refine IntermediateField.adjoin.mono _ _ _ ?_ (hy x)
    rw [Set.singleton_subset_iff]
    exact ⟨y x, by simpa using ⟨x, hx, rfl⟩, rfl⟩

def entrySubgroup {F E G : Type} [Field F] [Field E] [Algebra F E] [Group G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) E) (K : IntermediateField F E) : Subgroup G where
  carrier := {g | ∀ i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K ∧
    (r g⁻¹ : Matrix (Fin a) (Fin a) E) i j ∈ K}
  one_mem' := fun i j => by
    have : (r 1 : Matrix (Fin a) (Fin a) E) i j ∈ K := by
      rw [map_one, Units.val_one, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    exact ⟨this, by rwa [inv_one]⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨sum_mem fun k _ => mul_mem (hg i k).1 (hh k j).1,
      sum_mem fun k _ => mul_mem (hh i k).2 (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem exists_finiteDimensional_entries_mem (l : ℕ) [Fact l.Prime] (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (n : ℕ)
    (r : G →* Matrix.GeneralLinearGroup (Fin n) (PadicAlgCl l))
    (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧
      ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ K := by
  obtain ⟨ι, _, K, hK, hcov⟩ := exists_countable_family l
  have hKcl : ∀ m, IsClosed (K m : Set (PadicAlgCl l)) := fun m =>
    haveI : FiniteDimensional ℚ_[l] (K m).toSubalgebra.toSubmodule := hK m
    Submodule.closed_of_finiteDimensional (K m).toSubalgebra.toSubmodule
  have hcl : ∀ m, IsClosed (entrySubgroup r (K m) : Set G) := fun m => by
    have : (entrySubgroup r (K m) : Set G) = ⋂ i, ⋂ j,
        ((fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m) ∩
         (fun g => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j) ⁻¹' (K m)) := by
      ext g
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      ((hKcl m).preimage (hr i j)).inter ((hKcl m).preimage ((hr i j).comp continuous_inv))
  have hun : ⋃ m, (entrySubgroup r (K m) : Set G) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨m, hm⟩ := hcov
      (Set.range (fun p : Fin n × Fin n => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2) ∪
       Set.range (fun p : Fin n × Fin n => (r g⁻¹ : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.1 p.2))
      ((Set.finite_range _).union (Set.finite_range _))
    exact Set.mem_iUnion.2 ⟨m, fun i j =>
      ⟨hm (Or.inl ⟨(i, j), rfl⟩), hm (Or.inr ⟨(i, j), rfl⟩)⟩⟩
  obtain ⟨m, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hun
  have hop : IsOpen (entrySubgroup r (K m) : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_interior_iff_mem_nhds.1 hx)
  haveI : Finite (G ⧸ entrySubgroup r (K m)) := Subgroup.quotient_finite_of_isOpen _ hop
  let s : Set (PadicAlgCl l) := Set.range fun p : (G ⧸ entrySubgroup r (K m)) × Fin n × Fin n =>
    (r p.1.out : Matrix (Fin n) (Fin n) (PadicAlgCl l)) p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI := hK m
  refine ⟨IntermediateField.adjoin ℚ_[l] s ⊔ K m, inferInstance, fun g i j => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (entrySubgroup r (K m)) g
  have hg : g = (g : G ⧸ entrySubgroup r (K m)).out * (h : G)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  rw [hg, map_mul, Units.val_mul, Matrix.mul_apply]
  refine sum_mem fun k _ => mul_mem ?_ ?_
  · exact (le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(g, i, k), rfl⟩)
  · exact (le_sup_right : K m ≤ _) (h.2 k j).2

theorem exists_finExt_entries_mem :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  intro l _ G _ _ _ _ _ a r hr L₀
  obtain ⟨K, hK, h⟩ := exists_finiteDimensional_entries_mem l G a r
    fun i j => hr.matrix_elem i j
  haveI := L₀.2
  exact ⟨⟨L₀.1 ⊔ K, inferInstance⟩, le_sup_left, fun g i j =>
    (le_sup_right : K ≤ L₀.1 ⊔ K) (h g i j)⟩

end GlobalTheory.CompactRepField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtensionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactGroup_rep_defined_over_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] (a : ℕ) (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l)), Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ L₀ : FinExt l, ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := by
  first | exact @GlobalTheory.CompactRepField.exists_finExt_entries_mem | exact GlobalTheory.CompactRepField.exists_finExt_entries_mem | (intros; apply GlobalTheory.CompactRepField.exists_finExt_entries_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Cyc

theorem exists_integral_cyclotomicChar : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∃ χ : GQ l →* ℤ_[l]ˣ, (∀ g, (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l])) ∧ Continuous χ ∧ ∀ (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 → ∃ g ∈ GK K, χ g = u := by
  intro l _ P
  have hχ : IsCyc P.χQ := P.χQ_cyc
  obtain ⟨hn, hc, hK⟩ := cyc_basic l P.χQ hχ
  let f : GQ l →* ℤ_[l] :=
    { toFun := fun g => ⟨(P.χQ g : ℚ_[l]), (hn g).le⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change (P.χQ (a * b) : ℚ_[l]) = (P.χQ a : ℚ_[l]) * (P.χQ b : ℚ_[l])
        rw [map_mul, Units.val_mul]) }
  have hf : Continuous f := hc.subtype_mk _
  refine ⟨f.toHomUnits, fun g => rfl, ?_, ?_⟩
  · rw [Units.continuous_iff]
    exact ⟨hf, hf.comp continuous_inv⟩
  · intro K s hs u hu
    have hu1 : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u
    obtain ⟨g, hg, hgu⟩ := exists_chi_eq K P.χQ hχ _ hu1
    have hG : g ∈ Gj K s := ((hK K g hg).1 s).2 (by
      rw [hgu]
      have := (PadicInt.norm_le_pow_iff_mem_span_pow ((u : ℤ_[l]) - 1) s).2
        (Ideal.mem_span_singleton.2 hu)
      rwa [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one] at this)
    refine ⟨g, IntermediateField.fixingSubgroup_antitone hs hG, ?_⟩
    exact Units.ext (Subtype.ext hgu)

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
noncomputable section
namespace GlobalTheory.ThetaTie
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.MemLoc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow {P : LocPrime l} (AI : LocAinf l P) (m n : ℕ) : AI.ζ (m + n) ^ l ^ n = AI.ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem isEps {P : LocPrime l} (AI : LocAinf l P) : IsEps (l := l) AI.ε := by
  constructor
  · refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
    have := zeta_pow AI 0 n
    rw [zero_add, AI.ζ_zero] at this
    rw [this]
  · have : ((frobeniusEquiv (Per.Fl l) l).symm AI.ε).untilt = AI.ζ 1 := by
      refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
      refine ⟨AI.ζ (1 + n), ?_, ?_⟩
      · rw [add_comm]
        exact (AI.ε_coeff (n + 1)).symm.trans (PreTilt.coeff_frobeniusEquiv_symm n _).symm
      · rw [zeta_pow AI 1 n]
    rw [this]
    exact AI.ζ_one

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  have : Subsingleton (Per.AinfP l ⧸ Per.kerP l ^ 0) := by
    rw [pow_zero, Ideal.one_eq_top]; infer_instance
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 0 y).2 (Subsingleton.elim _ _)

theorem mem_filD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact GlobalTheory.RingIface.exists_of_mem_FilD_nat l
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem alg_inj {e : Per.Fl l} (he : IsEps e) :
    Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := by
  have _ := he
  exact (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : ℂ_[l]) :
    AI.actC g x = Per.σC g x := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (GlobalTheory.RingIface.sigC_cont l g)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem log_mu {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have hm : algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
    refine GlobalTheory.RingIface.alg_mem_kerP l ?_
    rw [map_sub, WittVector.fontaineTheta_teichmuller, he.1, map_one, sub_self]
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  change Per.ev l 2 (algebraMap (Per.AinfP l) (Per.BdRp l)
    (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) - y) = 0
  rw [map_sub, ev_alg]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = m at hm h ⊢
  have h2 : Ideal.Quotient.mk (Per.kerP l ^ 2) (m ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hm 2)
  have hu : IsUnit ((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  have hs : (∑ k ∈ Finset.range 2, (-1) ^ k * (((2 : ℕ).factorial / (k + 1) : ℕ) : Per.AinfP l) *
      m ^ (k + 1)) = ((2 : ℕ) : Per.AinfP l) * m - m ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hs, map_sub, h2, sub_zero, map_mul, map_natCast] at h
  rw [sub_eq_zero]
  exact (hu.mul_left_cancel h).symm

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem eD_ιA (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  refine Eq.trans ?_ h
  simp

theorem fil_nat (n : ℕ) (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil n ↔
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (T.fil _ _ _).trans (mem_filD_nat n _)

theorem fil_zero (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil 0 ↔
    ∃ z, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (fil_nat T 0 x).trans ⟨fun ⟨z, _, h⟩ => ⟨z, h⟩, fun ⟨z, h⟩ => ⟨z, mem_filtration_zero' z, h⟩⟩

def th (x : P.R.BdR) : ℂ_[l] :=
  Per.θD l (Function.invFun (algebraMap (Per.BdRp l) (Per.BdR l)) (T.eD x))

theorem th_eq {x : P.R.BdR} {z : Per.BdRp l}
    (h : algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x) : th T x = Per.θD l z := by
  rw [th, ← h, Function.leftInverse_invFun (alg_inj (isEps AI))]

include T in
theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD (botExt l)).Fil (-1), P.ιB P.tB * s = 1 := by
  obtain ⟨h1, -, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l _ (isEps AI)
  obtain ⟨-, hk, hun, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hu := (P.PD (botExt l)).t_unit
  have t1 := (P.PD (botExt l)).mem_filtration_one
  have t2 := (P.PD (botExt l)).not_mem_filtration_two
  rw [P.PD_ι, P.period_datum_t_eq] at t1 t2
  rw [P.period_datum_t_eq] at hu
  obtain ⟨s, hs⟩ := (hu.map P.ιB).exists_right_inv
  refine ⟨s, ?_, hs⟩
  obtain ⟨z, hz, ez⟩ := (fil_nat T 1 _).1 t1
  obtain ⟨u, rfl⟩ := (h1 1 z).1 hz
  have huu : IsUnit u := hun u fun h0 => by
    obtain ⟨w, rfl⟩ := (h1 1 u).1 ((hk u).1 h0)
    exact t2 ((fil_nat T 2 _).2 ⟨_, (h1 2 _).2 ⟨w, by ring⟩, ez⟩)
  obtain ⟨v, hv⟩ := huu.exists_right_inv
  rw [T.fil, GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l _ (isEps AI)]
  refine ⟨v, ?_⟩
  have e1 : T.eD (P.ιB P.tB) * T.eD s = 1 := by rw [← map_mul, hs, map_one]
  have e2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv
  rw [← ez] at e1
  rw [show (- (-1 : ℤ)).toNat = 1 from rfl, show (-1 : ℤ).toNat = 0 from rfl]
  simp only [map_mul, map_one, pow_one, pow_zero, one_mul] at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi AI.ε)) = X at e1 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) u = U at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) v = V at e2 ⊢
  linear_combination V * e1 - (T.eD s * X) * e2

def thetaL : ThetaL P AI where
  θ := th T
  θ_one := by rw [th_eq T (z := 1) (by simp), map_one]
  θ_add x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a + b) (by rw [map_add (f := _), map_add (f := _), ha, hb]), map_add (f := _)]
  θ_mul x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a * b) (by rw [map_mul, map_mul, ha, hb]), map_mul]
  θ_onto c := by
    obtain ⟨z, hz⟩ := (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).1 c
    have e : algebraMap (Per.BdRp l) (Per.BdR l) z =
        T.eD (T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) z)) := (T.eD.apply_symm_apply _).symm
    exact ⟨_, (fil_zero T _).2 ⟨z, e⟩, (th_eq T e).trans hz⟩
  θ_ker x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    rw [th_eq T ha, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1]
    refine ⟨fun h => (fil_nat T 1 x).2 ⟨a, h, ha⟩, fun h => ?_⟩
    obtain ⟨z, hz, e⟩ := (fil_nat T 1 x).1 h
    rwa [← alg_inj (isEps AI) (e.trans ha.symm)]
  θ_act g x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    have e : algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g a) = T.eD (P.actQdR g x) := by
      rw [T.actD, ← ha]
      exact (GlobalTheory.RingIface.sigD_alg l g a).symm
    rw [th_eq T ha, th_eq T e, actC_eq, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.2]
  θ_Om x := by
    obtain ⟨y, h1, h2⟩ := T.om x
    rw [th_eq T h1.symm, h2]
  θ_int a := by
    rw [th_eq T (eD_ιA T a).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  θ_teich x y h := by
    rw [th_eq T (eD_ιA T _).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1, WittVector.fontaineTheta_teichmuller]
    have h1 := Ideal.Quotient.eq.1 ((PreTilt.mk_untilt_eq_coeff_zero x).trans h)
    have h2 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
    simpa using h2
  fil_succ_iff_mul_t a x := by
    have t1 := (P.PD (botExt l)).mem_filtration_one
    rw [P.PD_ι, P.period_datum_t_eq] at t1
    constructor
    · intro hx
      obtain ⟨s, hs, e⟩ := exists_inverse_fontaineElement_mem_fil_neg_one T
      refine ⟨s * x, ?_, by rw [← mul_assoc, e, one_mul]⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ hs hx
      rwa [show -1 + (a + 1) = a by ring] at this
    · rintro ⟨y, hy, rfl⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ t1 hy
      rwa [add_comm] at this
  t_μ := by
    obtain ⟨y, hy, e⟩ := T.t
    refine (fil_nat T 2 _).2 ⟨_, log_mu (isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, eD_ιA]
    rfl

theorem nonempty_thetaL (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] :
    Nonempty (ThetaL (D.loc l) (D.locA l)) :=
  ⟨thetaL (D.locT l)⟩

end GlobalTheory.ThetaTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodDataStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime], Nonempty (ThetaL (D.loc l) (D.locA l)) := by
  first | exact @GlobalTheory.ThetaTie.nonempty_thetaL | exact GlobalTheory.ThetaTie.nonempty_thetaL | (intros; apply GlobalTheory.ThetaTie.nonempty_thetaL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvFilD
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.Per.TiedField

theorem exists_inv_filD {l : ℕ} [Fact l.Prime] (x : Per.BdR l) (h0 : x ∈ Per.FilD l 0)
    (h1 : x ∉ Per.FilD l 1) : ∃ y ∈ Per.FilD l 0, x * y = 1 := by
  obtain ⟨-, hone, -, -, -, -, hlast⟩ := GlobalTheory.MemLoc.filD_laws l
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.FilLaws.exists_isEps l
  obtain ⟨z, hz⟩ := (GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l e he 0 x).1 h0
  rw [neg_zero, Int.toNat_zero, pow_zero, pow_zero, mul_one, one_mul] at hz
  subst hz
  have hz1 : Per.θD l z ≠ 0 := fun h => h1 ((hlast 1 z).2 ((hker z).1 h))
  obtain ⟨w, hw⟩ := (hunit z hz1).exists_right_inv
  refine ⟨algebraMap (Per.BdRp l) (Per.BdR l) w, ?_, by rw [← map_mul, hw, map_one]⟩
  have := Submodule.smul_mem _ w hone
  rwa [Algebra.smul_def, mul_one] at this

theorem tied_field : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    IsField P.R.BdR ∧ IsDomain P.R.B ∧ Function.Injective P.ιB ∧ Function.Injective P.φB ∧
      ∀ (K : FinExt l) (x : P.R.BdR), x ∈ (P.PD K).Fil 0 → x ∉ (P.PD K).Fil 1 →
        ∃ y ∈ (P.PD K).Fil 0, x * y = 1 := by
  intro l _ P AI T
  have hF : IsField P.R.BdR := T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1
  obtain ⟨K₁⟩ : Nonempty (FinExt l) := ⟨⟨⊥, inferInstance⟩⟩
  have hι : Function.Injective P.ιB := fun a b h =>
    (P.PD K₁).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)
  have hφ : Function.Injective P.φB := fun a b h =>
    (P.PD K₁).φ_inj (by rw [P.PD_φ, P.PD_φ]; exact h)
  refine ⟨hF, ?_, hι, hφ, fun K x h0 h1 => ?_⟩
  · have := hF.isDomain
    exact hι.isDomain (P.ιB : P.R.B →+* P.R.BdR)
  · obtain ⟨y, hy, hxy⟩ := exists_inv_filD (T.eD x) ((T.fil K 0 x).1 h0) (fun h => h1 ((T.fil K 1 x).2 h))
    refine ⟨T.eD.symm y, (T.fil K 0 _).2 (by rwa [RingEquiv.apply_symm_apply]), T.eD.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, hxy, map_one]

end GlobalTheory.Per.TiedField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

namespace GlobalTheory.BdRQuot

theorem isUnit_one_add {R : Type} [CommRing R] (I : Ideal R) (z : AdicCompletion I R)
    (hz : AdicCompletion.evalₐ I 1 z = 0) : IsUnit (1 + z) := by
  have h1 : z.val 1 = 0 := by
    have h' : (I ^ 1 • ⊤ : Ideal R) = I ^ 1 := by ext x; simp
    exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective).1 hz
  have hu : ∀ n, IsUnit (1 + z.val n) := by
    intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z.val (n + 1))
    have e1 := z.property (show 1 ≤ n + 1 by omega)
    have e2 := z.property (show n ≤ n + 1 by omega)
    rw [← hr, AdicCompletion.transitionMap_ideal_mk] at e1 e2
    rw [h1, Ideal.Quotient.eq_zero_iff_mem] at e1
    have hrI : r ∈ I := by simpa using e1
    refine IsNilpotent.isUnit_one_add ⟨n, ?_⟩
    rw [← e2, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    simpa using Ideal.pow_mem_pow hrI n
  let u : AdicCompletion I R := ⟨fun n => Ring.inverse (1 + z.val n), fun {m n} hmn => by
    have e := congrArg (AdicCompletion.transitionMap I R hmn) (Ring.inverse_mul_cancel _ (hu n))
    rw [AdicCompletion.transitionMap_map_mul, map_add (f := _), AdicCompletion.transitionMap_map_one,
      z.property hmn] at e
    exact left_inv_eq_right_inv e (Ring.mul_inverse_cancel _ (hu m))⟩
  refine IsUnit.of_mul_eq_one u ?_
  ext n
  exact Ring.mul_inverse_cancel _ (hu n)

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_FilP_zero : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_one, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 0)), Ideal.Quotient.eq_zero_iff_mem]
  simp

theorem mem_FilD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact fun h => GlobalTheory.RingIface.exists_of_mem_FilD_nat l h
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem mem_filtration_zero (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  simpa using Ideal.mul_mem_left _ y one_mem_FilP_zero

variable {P : LocPrime l} {AI : LocAinf l P}

theorem eD_ιA (T : LocTied l P AI) (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = Per.pD l (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA, ← GlobalTheory.RingIface.pD_eq_alg] at h
  simpa using h

theorem exists_approx (T : LocTied l P AI) (n : ℕ) (x : P.R.BdR) (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    ∃ (k : ℕ) (a : Ainf l), (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) := by
  obtain ⟨y, -, hy⟩ := (mem_FilD_nat 0 _).1 ((T.fil _ _ _).1 hx)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (Per.ev l n y)
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (S := Per.AinfP l) (l : Per.Ainf l) s
  refine ⟨k, a, (T.fil _ _ _).2 ((mem_FilD_nat n _).2
    ⟨(l : Per.BdRp l) ^ k * y - algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) _ a), ?_, ?_⟩)⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have e : ∀ r : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) r) =
        Ideal.Quotient.mk _ r := fun r => GlobalTheory.RingIface.ev_alg l n r
    rw [map_sub, e, ← ha, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_natCast,
      hs, mul_comm, sub_self]
  · rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, eD_ιA, hy,
      GlobalTheory.RingIface.pD_eq_alg]

theorem exists_inv (T : LocTied l P AI) (y : P.R.BdR) (hy : y ∈ (P.PD (botExt l)).Fil 1) :
    ∃ u ∈ (P.PD (botExt l)).Fil 0, (1 + y) * u = 1 := by
  obtain ⟨z, hz, e⟩ := (mem_FilD_nat 1 _).1 ((T.fil _ _ _).1 hy)
  have hU : IsUnit (1 + z : Per.BdRp l) := by
    obtain ⟨c, -, hc⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    have h := isUnit_one_add (Per.kerP l) (c z) (by rw [hc]; exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 1 z).1 hz)
    have h' := h.map c.symm
    rwa [map_add, map_one, RingEquiv.symm_apply_apply] at h'
  obtain ⟨v, hv'⟩ := hU.exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v), (T.fil _ _ _).2 ?_, T.eD.injective ?_⟩
  · rw [RingEquiv.apply_symm_apply]
    exact (mem_FilD_nat 0 _).2 ⟨v, mem_filtration_zero _, rfl⟩
  · rw [map_mul, map_add (f := _), map_one, RingEquiv.apply_symm_apply, ← e,
      ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_add, ← map_mul, hv']

theorem mul_mem_zero {a : ℤ} {x y : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0)
    (hy : y ∈ (P.PD (botExt l)).Fil a) : x * y ∈ (P.PD (botExt l)).Fil a := by
  simpa using (P.PD (botExt l)).Fil_mul 0 a x y hx hy

theorem pow_mem_Fil {a : ℤ} {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) (n : ℕ) :
    x ^ n ∈ (P.PD (botExt l)).Fil (n * a) := by
  induction n with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih hx

theorem theta_pow (J : ThetaL P AI) (a : Ainf l) (k : ℕ) :
    J.θ (P.ιB (AI.ιA (a ^ k))) = J.θ (P.ιB (AI.ιA a)) ^ k := by
  induction k with
  | zero => simpa using J.θ_one
  | succ k ih => rw [pow_succ, map_mul, map_mul, J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ (AI.ainf_image_mem_filtration_zero _ _), ih, pow_succ]

theorem εroot_pow (n : ℕ) : AI.εroot (n + 1) ^ l ^ n = AI.ε1 := by
  induction n with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    rfl

theorem ζ_pow (n : ℕ) : AI.ζ (n + 1) ^ l ^ n = AI.ζ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, AI.ζ_succ, ih]

theorem theta_teich (J : ThetaL P AI) :
    J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) = ((AI.ζ 1 : OC l) : PadicComplex l) := by
  have key : ∀ n : ℕ, ‖J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) -
      ((AI.ζ 1 : OC l) : PadicComplex l)‖ ≤ ‖(l : PadicComplex l)‖ ^ (n + 1) := by
    intro n
    let c : OC l := ⟨J.θ (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot (n + 1))))),
      (GlobalTheory.RingBasics.mem_OC _).2 (J.θ_int _)⟩
    have h1 := J.θ_teich (AI.εroot (n + 1)) (AI.ζ (n + 1)) (by
      rw [LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add, AI.ε_coeff])
    have h2 : ((l : ℕ) : OC l) ∣ c - AI.ζ (n + 1) := by
      have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (c - AI.ζ (n + 1))).2 (by simpa using h1)
      rwa [pow_one, Ideal.mem_span_singleton] at this
    have h3 := dvd_sub_pow_of_dvd_sub h2 n
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, GlobalTheory.RingBasics.mem_span_pow_OC, ζ_pow] at h3
    rw [← εroot_pow (AI := AI) n, map_pow, theta_pow]
    simpa using h3
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : PadicComplex l))
    GlobalTheory.RingBasics.norm_p_lt).comp (Filter.tendsto_add_atTop_nat 1)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' lim key))

theorem exists_t_eq (T : LocTied l P AI) (J : ThetaL P AI) :
    ∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
  obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t 1 _).1 J.t_μ
  obtain ⟨u, hu, hyu⟩ := exists_inv T y hy
  have hy0 : y ∈ (P.PD (botExt l)).Fil 0 := (P.PD (botExt l)).Fil_anti 0 hy
  have h1 := (P.PD (botExt l)).one_mem
  have hθu : J.θ u = 1 := by
    have := congrArg J.θ hyu
    rwa [J.θ_mul _ (add_mem h1 hy0) _ hu, J.θ_add _ h1 _ hy0, (J.θ_ker y hy0).2 hy, J.θ_one,
      add_zero, one_mul] at this
  have hπ : J.θ (P.ιB (AI.ιA AI.π₁)) = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
    rw [eq_sub_iff_add_eq, ← theta_teich J, ← J.θ_one, ← J.θ_add _ (AI.ainf_image_mem_filtration_zero _ _) _ h1]
    simp [LocAinf.π₁]
  refine ⟨P.ιB (AI.ιA AI.π₁) * u, mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) hu, ?_, ?_⟩
  · rw [AI.μ_eq, map_mul, map_mul] at e
    linear_combination (-u) * e - P.ιB P.tB * hyu
  · rw [J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ hu, hθu, mul_one, hπ]

theorem exists_t_pow (J : ThetaL P AI) (a : ℤ) (n : ℕ) (x : P.R.BdR)
    (hx : x ∈ (P.PD (botExt l)).Fil (a + n)) :
    ∃ y ∈ (P.PD (botExt l)).Fil a, x = P.ιB P.tB ^ n * y := by
  induction n generalizing x with
  | zero => exact ⟨x, by simpa using hx, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc] at hx
    obtain ⟨z, hz, rfl⟩ := (J.fil_succ_iff_mul_t _ _).1 hx
    obtain ⟨y, hy, rfl⟩ := ih z hz
    exact ⟨y, hy, by ring⟩

theorem mem_Fil_iff (T : LocTied l P AI) (J : ThetaL P AI) (n : ℕ) (a : Ainf l) :
    P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a := by
  have hξ : P.ιB (AI.ιA AI.ξ) ∈ (P.PD (botExt l)).Fil 1 :=
    (AI.ainf_image_mem_filtration_one_iff _ _).2 ⟨1, (mul_one _).symm⟩
  constructor
  · obtain ⟨w, hw, ht, -⟩ := exists_t_eq T J
    have hunit : IsUnit (P.ιB (AI.ιA AI.ξ)) := by
      have := (P.PD (botExt l)).t_unit.map P.ιB
      rw [P.period_datum_t_eq, ht] at this
      exact isUnit_of_mul_isUnit_left this
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      rw [Nat.cast_succ] at h
      obtain ⟨b, rfl⟩ := ih ((P.PD (botExt l)).Fil_anti _ h)
      rw [add_comm] at h
      obtain ⟨y, hy, e⟩ := exists_t_pow J 1 n _ h
      rw [map_mul, map_mul, map_pow, map_pow, ht, mul_pow, mul_assoc] at e
      have e' := (hunit.pow n).mul_left_cancel e
      have hb : P.ιB (AI.ιA b) ∈ (P.PD (botExt l)).Fil 1 := by
        rw [e']
        exact mul_mem_zero (by simpa using pow_mem_Fil hw n) hy
      obtain ⟨c, rfl⟩ := (AI.ainf_image_mem_filtration_one_iff _ _).1 hb
      exact ⟨c, by rw [pow_succ, mul_assoc]; rfl⟩
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, map_pow, map_pow, mul_comm]
    exact mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) (by simpa using pow_mem_Fil hξ n)

theorem fil_quotient : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (J : ThetaL P AI) (n : ℕ),
    (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l),
      (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧
    (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧
    (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1) :=
  fun _ _ _ _ T J n => ⟨exists_approx T n, mem_Fil_iff T J n, exists_t_eq T J⟩

end GlobalTheory.BdRQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinfStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_fil_quotient_xi_power_ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (J : ThetaL P AI) (n : ℕ), (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l), (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧ (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧ (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧ J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1)  := by
  first | exact @GlobalTheory.BdRQuot.fil_quotient | exact GlobalTheory.BdRQuot.fil_quotient | (intros; apply GlobalTheory.BdRQuot.fil_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem cyc_eq_binomialSeries (c : ℤ_[l]) : cyc l O c = PowerSeries.binomialSeries O c - 1 :=
  Series.cyc_eq l O c

theorem act_X (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := PowerSeries.substAlgHom_X _

theorem act_apply (c : ℤ_[l]) (a : PowerSeries O) :
    act l O c a = PowerSeries.subst (cyc l O c) a :=
  congrFun (PowerSeries.coe_substAlgHom _) a

theorem act_eq_gam (c : ℤ_[l]) : act l O c = GlobalTheory.Fon.gam O c :=
  Series.act_eq l O c

theorem act_act (c c' : ℤ_[l]) (a : PowerSeries O) :
    act l O c (act l O c' a) = act l O (c * c') a := by
  simp only [act_eq_gam, GlobalTheory.Fon.gam_mul]

theorem act_one (a : PowerSeries O) : act l O 1 a = a := by
  rw [act_eq_gam, GlobalTheory.Fon.gam_one]

theorem cyc_natCast (k : ℕ) : cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1 := by
  rw [cyc_eq_binomialSeries, PowerSeries.binomialSeries_nat]

theorem coeff_one_cyc (c : ℤ_[l]) : PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c := by
  rw [cyc_eq_binomialSeries, ← GlobalTheory.Fon.gam_X, GlobalTheory.Fon.coeff_one_gam_X]

theorem act_pow_sub_one (c : ℤ_[l]) (k : ℕ) :
    act l O c ((1 + PowerSeries.X) ^ k - 1) =
      PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) := by
  rw [← cyc_natCast l O k, ← act_apply, ← act_X l O c, ← act_X l O (k : ℤ_[l]), act_act, act_act,
    mul_comm]

theorem act_laws : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], (∀ c, act l O c PowerSeries.X = cyc l O c) ∧ (∀ c c' a, act l O c (act l O c' a) = act l O (c * c') a) ∧ (∀ a, act l O 1 a = a) ∧ (∀ k : ℕ, cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1) ∧ (∀ c, PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c) ∧ ∀ (c : ℤ_[l]) (k : ℕ), act l O c ((1 + PowerSeries.X) ^ k - 1) = PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) :=
  fun l _ O _ _ => ⟨act_X l O, act_act l O, act_one l O, cyc_natCast l O, coeff_one_cyc l O,
    act_pow_sub_one l O⟩

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], (∀ c, act l O c PowerSeries.X = cyc l O c) ∧ (∀ c c' a, act l O c (act l O c' a) = act l O (c * c') a) ∧ (∀ a, act l O 1 a = a) ∧ (∀ k : ℕ, cyc l O (k : ℤ_[l]) = (1 + PowerSeries.X) ^ k - 1) ∧ (∀ c, PowerSeries.coeff 1 (cyc l O c) = algebraMap ℤ_[l] O c) ∧ ∀ (c : ℤ_[l]) (k : ℕ), act l O c ((1 + PowerSeries.X) ^ k - 1) = PowerSeries.subst ((1 + PowerSeries.X) ^ k - 1 : PowerSeries O) (cyc l O c) := by
  first | exact @GlobalTheory.Cyc.act_laws | exact GlobalTheory.Cyc.act_laws | (intros; apply GlobalTheory.Cyc.act_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisExtra
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.LocIota

theorem ιB_algebraMap_Kur {l : ℕ} [Fact l.Prime] (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  have hint : IsIntegral ℚ_[l] (c : Om l) := Algebra.IsIntegral.isIntegral _
  obtain ⟨K, hc⟩ : ∃ K : FinExt l, (c : Om l) ∈ K0 K :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
      IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] (c : Om l), c.2⟩
  have h := (P.PD K).ι.commutes (⟨c, hc⟩ : ↥(K0 K))
  rw [P.PD_ι] at h
  exact h

end GlobalTheory.LocIota
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodParIffGoodSig
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.EigenProjector

theorem HG_of_mem_Zgood (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) :
    HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩

end GlobalTheory.EigenProjector
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Topology Filter

namespace GlobalTheory

private lemma mem_span_pow_smul_iff_exists_pow_smul {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] (n : ℕ) (x : M) :
    x ∈ (Ideal.span {a}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, x = a ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp [eq_comm]

theorem continuous_adicModule_iff {R : Type} [CommRing R] (a : R) {M : Type} [AddCommGroup M]
    [Module R M] {G : Type} [TopologicalSpace G] (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g : G) (n : ℕ), ∀ᶠ h in 𝓝 g, ∃ y : M, f h - f g = a ^ n • y := by
  let _ : TopologicalSpace R := (Ideal.span {a}).ringFilterBasis.topology
  let _ : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hB : ∀ y : M, (𝓝 y).HasBasis
      (fun V : Set M => ∃ n : ℕ, V = ↑((Ideal.span {a}) ^ n • (⊤ : Submodule R M)))
      (fun V => (fun z => y + z) '' V) := fun y =>
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M)).toAddGroupFilterBasis.nhds_hasBasis y
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g => ?_
  refine ((hB (f g)).tendsto_right_iff).trans ⟨fun H n => ?_, fun H V hV => ?_⟩
  · filter_upwards [H _ ⟨n, rfl⟩] with h hh
    obtain ⟨z, hz, hzh⟩ := hh
    obtain ⟨y, rfl⟩ := (mem_span_pow_smul_iff_exists_pow_smul a n z).1 hz
    beta_reduce at hzh
    exact ⟨y, by rw [← hzh, add_sub_cancel_left]⟩
  · obtain ⟨n, rfl⟩ := hV
    filter_upwards [H n] with h hh
    obtain ⟨y, hy⟩ := hh
    exact ⟨a ^ n • y, (mem_span_pow_smul_iff_exists_pow_smul a n _).2 ⟨y, rfl⟩, by
      show f g + a ^ n • y = f h
      rw [← hy]; abel⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExtEmbeddingSplitting
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem natCard_algHom_intermediateField_of_range_le {F E A : Type} [Field F] [Field E] [Field A]
    [Algebra F E] [Algebra F A] [FiniteDimensional F E] [Algebra.IsSeparable F E] [IsAlgClosed A]
    (M : IntermediateField F A) (h : ∀ (f : E →ₐ[F] A) (x : E), f x ∈ M) :
    Nat.card (E →ₐ[F] ↥M) = finrank F E := by

  have e : (E →ₐ[F] ↥M) ≃ (E →ₐ[F] A) :=
    { toFun := fun g => M.val.comp g
      invFun := fun f => f.codRestrict M.toSubalgebra (h f)
      left_inv := fun _ => AlgHom.ext fun _ => rfl
      right_inv := fun _ => AlgHom.ext fun _ => rfl }
  rw [Nat.card_congr e]
  exact AlgHom.natCard_of_splits F E A fun _ => IsAlgClosed.splits _

private theorem exists_fd_intermediateField_contains_embeddings (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ N : IntermediateField ℚ_[l] (Om l), FiniteDimensional ℚ_[l] ↥N ∧
      ∀ (f : E →ₐ[ℚ_[l]] Om l) (x : E), f x ∈ N := by
  have hfin : ∀ f : E →ₐ[ℚ_[l]] Om l, FiniteDimensional ℚ_[l] ↥f.fieldRange :=
    fun f => f.toLinearMap.finiteDimensional_range
  exact ⟨⨆ f : E →ₐ[ℚ_[l]] Om l, f.fieldRange,
    IntermediateField.finiteDimensional_iSup_of_finite,
    fun f x => (le_iSup (fun g : E →ₐ[ℚ_[l]] Om l => g.fieldRange) f) ⟨x, rfl⟩⟩

theorem exists_finExt_embedding_splitting (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ LL' : FinExt l, Nonempty (LL →ₐ[ℚ_[l]] ↥LL'.1) ∧
      Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥K.1 ∧
      Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥(K0 K) := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := Module.Finite.left ℚ_[l] ↥(K0 K) ↥K.1
  obtain ⟨N1, hN1, hK1⟩ := exists_fd_intermediateField_contains_embeddings l ↥K.1
  obtain ⟨N0, hN0, hK0⟩ := exists_fd_intermediateField_contains_embeddings l ↥(K0 K)

  let φ : LL →ₐ[ℚ_[l]] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have : FiniteDimensional ℚ_[l] ↥φ.fieldRange := φ.toLinearMap.finiteDimensional_range

  refine ⟨⟨φ.fieldRange ⊔ N1 ⊔ N0, inferInstance⟩,
    ⟨φ.codRestrict (φ.fieldRange ⊔ N1 ⊔ N0).toSubalgebra fun x => ?_⟩, ?_, ?_⟩
  · exact (le_sup_left.trans le_sup_left : φ.fieldRange ≤ _) ⟨x, rfl⟩
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right.trans le_sup_left : N1 ≤ _) (hK1 f x)
  · exact natCard_algHom_intermediateField_of_range_le _ fun f x =>
      (le_sup_right : N0 ≤ _) (hK0 f x)

end GlobalTheory
end
