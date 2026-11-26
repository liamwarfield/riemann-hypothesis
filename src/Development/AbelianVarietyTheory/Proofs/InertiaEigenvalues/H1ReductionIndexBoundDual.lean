module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeLevelPrimePow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerReductionH1Eq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerReductionH1Eq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.ReductionH1Kernel

section Gen
variable {G : Type} [Group G] [TopologicalSpace G]
    {LL : Type} [Field LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V}

theorem smul_H1Q_eq_zero (L : Lattice (O := O) ρ) (b : O)
    (hI : StableSub L (Ideal.span {b} • ⊤ : Submodule O ↥L.T)) (z : QuotientCohomology L _ hI) : b • z = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H w =>
    have hw : b • w = 0 := by
      apply Subtype.ext
      funext g
      show b • w.1 g = 0
      obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (w.1 g)
      rw [← ht, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, hw, Submodule.Quotient.mk_zero]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem cob_mem_Z1T (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) :
    (fun g => ρ g x - x) ∈ latticeCocycles L := by
  refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩
  · simp_rw [sub_eq_add_neg]
    exact (hρ x).add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel

theorem ker_red_gen (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (b : O)
    (hb : algebraMap O LL b ≠ 0) (hI : StableSub L (Ideal.span {b} • ⊤ : Submodule O ↥L.T))
    (hZ : ∀ d : ↥(latticeCocycles L), redT L _ d ∈ quotientCocycles L _ hI) :
    ∃ f : LatticeCohomology L →ₗ[O] QuotientCohomology L _ hI, LinearMap.ker f = (Ideal.span {b} • ⊤ : Submodule O (LatticeCohomology L)) ∧
      ∀ d : ↥(latticeCocycles L), ∃ h : redT L _ d ∈ quotientCocycles L _ hI,
        f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT L _ d, h⟩ := by
  let g0 : ↥(latticeCocycles L) →ₗ[O] ↥(quotientCocycles L _ hI) := (redT L _).codRestrict _ hZ
  have hB : (latticeCoboundaries L).comap (latticeCocycles L).subtype ≤
      ((BQ L _ hI).comap (quotientCocycles L _ hI).subtype).comap g0 := by
    intro d hd
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hd
    obtain ⟨x, hx, hxd⟩ := hd
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply]
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    funext g
    show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) - Submodule.Quotient.mk ⟨x, hx⟩ =
      Submodule.Quotient.mk (evT L g d)
    rw [show actQ L _ hI g (Submodule.Quotient.mk ⟨x, hx⟩) =
      Submodule.Quotient.mk (actT L g ⟨x, hx⟩) from rfl, ← Submodule.Quotient.mk_sub]
    congr 1
    apply Subtype.ext
    show ρ g x - x = (d : _ → V) g
    rw [← hxd]; rfl
  let f : LatticeCohomology L →ₗ[O] QuotientCohomology L _ hI := Submodule.mapQ _ _ g0 hB
  refine ⟨f, ?_, fun d => ⟨hZ d, rfl⟩⟩
  have hkill := smul_H1Q_eq_zero L b hI
  apply le_antisymm
  · intro z hz
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective ((latticeCoboundaries L).comap (latticeCocycles L).subtype) z
    rw [LinearMap.mem_ker] at hz
    change Submodule.Quotient.mk (g0 d) = (0 : QuotientCohomology L _ hI) at hz
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at hz
    obtain ⟨y, hy⟩ := hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (Ideal.span {b} • ⊤ : Submodule O ↥L.T) y
    have hg : ∀ g, ∃ t : ↥L.T, evT L g d - (actT L g x - x) = b • t := by
      intro g
      have h1 := congrFun hy g
      change actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x =
        Submodule.Quotient.mk (evT L g d) at h1
      rw [show actQ L _ hI g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (actT L g x) from rfl,
        ← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h1
      rw [← GlobalTheory.RedLocConst.mem_span_smul_top', ← neg_sub]
      exact neg_mem h1
    choose t ht using hg
    let cx : ↥(latticeCocycles L) := ⟨_, cob_mem_Z1T L hρ x⟩
    have h2 : ∀ g, (d : _ → V) g - (ρ g x - x) = algebraMap O LL b • ((t g : ↥L.T) : V) := by
      intro g
      rw [algebraMap_smul]
      exact congrArg Subtype.val (ht g)
    have hd'Z : (fun g => ((t g : ↥L.T) : V)) ∈ latticeCocycles L := by
      have hfun : (fun g => ((t g : ↥L.T) : V)) =
          (algebraMap O LL b)⁻¹ • ((d : _ → V) - (cx : _ → V)) := by
        funext g
        show _ = (algebraMap O LL b)⁻¹ • ((d : _ → V) g - (ρ g x - x))
        rw [h2, inv_smul_smul₀ hb]
      refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_pi.2 fun g _ => (t g).2⟩
      rw [hfun]
      exact (continuousCocycles ρ).smul_mem _ ((continuousCocycles ρ).sub_mem (Submodule.mem_inf.1 d.2).1 (Submodule.mem_inf.1 cx.2).1)
    have hdec : d = b • (⟨_, hd'Z⟩ : ↥(latticeCocycles L)) + cx := by
      apply Subtype.ext
      funext g
      show (d : _ → V) g = b • ((t g : ↥L.T) : V) + (ρ g x - x)
      rw [← algebraMap_smul LL b, ← h2, sub_add_cancel]
    have hcx : (Submodule.Quotient.mk cx : LatticeCohomology L) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      exact ⟨x, x.2, rfl⟩
    rw [hdec, Submodule.Quotient.mk_add, hcx, add_zero, Submodule.Quotient.mk_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self b) Submodule.mem_top
  · rw [Submodule.smul_le]
    intro a ha z _
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [LinearMap.mem_ker, map_smul, mul_smul, hkill, smul_zero]

end Gen

theorem redT_mem_Z1Q_of_ne (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ)
    (b : O) (hb : algebraMap O LL b ≠ 0)
    (hI : StableSub LA (Ideal.span {b} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)) :
    redT LA _ a ∈ quotientCocycles LA _ hI := by
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL b with hcdef
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hb).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = b • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [GlobalTheory.RedLocConst.mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = b • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {b} • ⊤ : Submodule O ↥LA.T) a) g) =
      Submodule.Quotient.mk (evT LA g a) := fun g => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g0
    refine ⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)),
      hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩
    · show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)
      rw [sub_self]; exact ⟨0, LA.T.zero_mem, smul_zero c⟩
    · intro g hg
      rw [hval, hval, Submodule.Quotient.eq, hmem]
      exact hg
  · intro g h
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {b} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

theorem ker_reduction_H1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), ∃ f : LatticeCohomology LA →ₗ[O] QuotientCohomology LA _ hI, LinearMap.ker f = (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA)) ∧ ∀ d : ↥(latticeCocycles LA), ∃ h : redT LA _ d ∈ quotientCocycles LA _ hI, f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT LA _ d, h⟩ := by
  intro l _ P K LL _ _ _ O _ _ hO A LA r hI
  have hb : algebraMap O LL (((l : ℕ) : O) ^ r) ≠ 0 := by
    rw [map_pow, map_natCast]
    refine pow_ne_zero _ ?_
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact ker_red_gen LA A.cont _ hb hI (redT_mem_Z1Q_of_ne l K LL O hO A LA _ hb hI)

end GlobalTheory.ReductionH1Kernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerReductionH1EqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_reduction_H1_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), ∃ f : LatticeCohomology LA →ₗ[O] QuotientCohomology LA _ hI, LinearMap.ker f = (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA)) ∧ ∀ d : ↥(latticeCocycles LA), ∃ h : redT LA _ d ∈ quotientCocycles LA _ hI, f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT LA _ d, h⟩ := by
  first | exact @GlobalTheory.ReductionH1Kernel.ker_reduction_H1 | exact GlobalTheory.ReductionH1Kernel.ker_reduction_H1 | (intros; apply GlobalTheory.ReductionH1Kernel.ker_reduction_H1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1Reduction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1Reduction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem finite_H1Q_lpow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA r hI
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hrest⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl : ((l : ℕ) : O) ≠ 0 := by
    intro h0
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h0, map_zero]
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] LL)] at h1
    have h2 : ((l : ℕ) : ℚ_[l]) = 0 := (algebraMap ℚ_[l] LL).injective (by rw [h1, map_zero])
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero r hl) hϖ
  have hspan : Ideal.span {((l : ℕ) : O) ^ r} = Ideal.span {ϖ ^ m} :=
    Ideal.span_singleton_eq_span_singleton.2 hm
  have key : ∀ (I : Submodule O ↥LA.T) (hI' : StableSub LA I),
      I = (Ideal.span {ϖ ^ m} • ⊤ : Submodule O ↥LA.T) → Finite (QuotientCohomology LA I hI') := by
    rintro I hI' rfl
    have hZ := finite_Z1Q hT l K LL O hO A LA ϖ hϖ m hI'
    have : Finite ↥(quotientCocycles LA _ hI') := hZ.to_subtype
    exact Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact key _ hI (by rw [hspan])

end GlobalTheory.CocycleModPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1ReductionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H1_reduction : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  first | exact @GlobalTheory.CocycleModPow.finite_H1Q_lpow | exact GlobalTheory.CocycleModPow.finite_H1Q_lpow | (intros; apply GlobalTheory.CocycleModPow.finite_H1Q_lpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CycIntegral

theorem cyc_mem (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (g : ↥(GK K)) :
    ∃ b : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL b := by
  obtain ⟨_, _, _, _, hopen⟩ := hO
  obtain ⟨a, ha, _⟩ := P.χQ_cyc (g : GQ l) 0 1 (one_pow _)
  have hn : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have h1 : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
    rw [h1]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · exact_mod_cast Padic.norm_int_le_one (a : ℤ)
  have hmem := GlobalTheory.GoodCoeff.padicInt_mem (algebraMap O LL).range
    (by rw [RingHom.coe_range]; exact hopen) (⟨_, hn⟩ : ℤ_[l])
  obtain ⟨b, hb⟩ := RingHom.mem_range.1 hmem
  refine ⟨b, ?_⟩
  rw [hb]
  simp [cycLL, LocPrime.PD_χ]

theorem cyc_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  intro l _ P K LL _ _ _ O _ _ hO
  obtain ⟨⟨hD, hV, hF⟩, _⟩ := id hO
  refine ⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := cyc_mem l P K LL O hO g
    refine ⟨b * x, ?_⟩
    show algebraMap O LL (b * x) = ((cycLL (P.PD K) LL g : LLˣ) : LL) • algebraMap O LL x
    rw [map_mul, hb, smul_eq_mul]
  · rw [← Submodule.map_top]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

end GlobalTheory.CycIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicIntegralLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_integral_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  first | exact @GlobalTheory.CycIntegral.cyc_lattice | exact GlobalTheory.CycIntegral.cyc_lattice | (intros; apply GlobalTheory.CycIntegral.cyc_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotient
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_finset_pow_torsion : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  intro l _ LL _ _ _ O _ _ hG k
  classical
  haveI hfin : Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ k}) :=
    (good_coeff_integers l LL O hG).2.2.1 k
  have hl : (l : LL) ≠ 0 := by
    have := (algebraMap ℚ_[l] LL).injective.ne
      (show (l : ℚ_[l]) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    simpa using this
  have hlk : (l : LL) ^ k ≠ 0 := pow_ne_zero _ hl
  let f : O ⧸ Ideal.span {((l : ℕ) : O) ^ k} → LL ⧸ LinearMap.range (Algebra.linearMap O LL) :=
    fun q => Submodule.Quotient.mk (((l : LL) ^ k)⁻¹ * algebraMap O LL q.out)
  refine ⟨(Set.finite_range f).toFinset, fun e he => ?_⟩
  rw [Set.Finite.mem_toFinset]
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ e
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at he
  obtain ⟨a, ha⟩ := he
  rw [Algebra.linearMap_apply, Algebra.smul_def, map_pow, map_natCast] at ha
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  have h1 : (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : O) ^ k}) a).out - a ∈
      Ideal.span {((l : ℕ) : O) ^ k} :=
    Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  have hc' := congrArg (algebraMap O LL) hc
  rw [map_mul, map_pow, map_natCast, RingHom.map_sub, ha] at hc'
  refine (Submodule.Quotient.eq _).2 ⟨c, ?_⟩
  rw [Algebra.linearMap_apply]
  field_simp
  linear_combination hc'

end GlobalTheory.GoodCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetPrimePowTorsionQuotientStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_primePow_torsion_quotient : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ k : ℕ, ∃ Es : Finset (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), ∀ e, ((l : ℕ) : O) ^ k • e = 0 → e ∈ Es := by
  first | exact @GlobalTheory.GoodCoeff.exists_finset_pow_torsion | exact GlobalTheory.GoodCoeff.exists_finset_pow_torsion | (intros; apply GlobalTheory.GoodCoeff.exists_finset_pow_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedFiniteCohomologyQuotients
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisMore
namespace GlobalTheory.NonzeroScalarLattice

theorem exists_ne_zero_smul_mem {G : Type} [Group G] {LL : Type} [Field LL] {O : Type}
    [CommRing O] [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [IsDomain O] [IsFractionRing O LL]
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (w : V) :
    ∃ (b : O), b ≠ (0 : O) ∧ b • w ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T L := by
  have hw : w ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.T.smul_mem _ hax
    · rw [mul_smul]; exact L.T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := O) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap O LL q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective O LL (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • ((algebraMap O LL p / algebraMap O LL q) • x) = p • x := by
      rw [← algebraMap_smul LL q, smul_smul, mul_div_cancel₀ _ hq1, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact L.T.smul_mem _ hax

end GlobalTheory.NonzeroScalarLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedFiniteCohomologyQuotients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.KerToDivisible

theorem torsion_finite_and_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : O) (hℓ0 : ℓ ≠ 0) (hℓ : ¬ IsUnit ℓ) (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n}))
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Finite ↥(Submodule.torsion O M) ∧ ∃ k : ℕ, ∀ x ∈ Submodule.torsion O M, ℓ ^ k • x = 0 := by
  have hdvd : ∀ y : O, y ≠ 0 → ∃ n : ℕ, y ∣ ℓ ^ n := by
    intro y hy
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ
    have he : e ≠ 0 := by
      rintro rfl; apply hℓ; rw [hv, pow_zero, mul_one]; exact v.isUnit
    refine ⟨n, ?_⟩
    rw [hu, hv, mul_pow, Units.mul_left_dvd]
    apply Dvd.dvd.mul_left
    rw [← pow_mul]
    exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he))
  haveI : Module.Finite O ↥(Submodule.torsion O M) :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  obtain ⟨y, hy, hy0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (Submodule.torsion_isTorsion (R := O) (M := M))
  obtain ⟨k, t, ht⟩ := hdvd y (nonZeroDivisors.ne_zero hy0)
  have hk : ∀ x : ↥(Submodule.torsion O M), ℓ ^ k • x = 0 := by
    intro x
    rw [ht, mul_comm, mul_smul, Submodule.mem_annihilator.1 hy x Submodule.mem_top, smul_zero]
  refine ⟨?_, k, fun x hx => congrArg Subtype.val (hk ⟨x, hx⟩)⟩
  have hT : Module.IsTorsionBy O ↥(Submodule.torsion O M) (ℓ ^ k) := fun x => hk x
  letI := hT.module
  haveI := hfin k
  haveI : IsScalarTower O (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff _).mpr hT)
  haveI : Module.Finite (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ Ideal.span {ℓ ^ k})

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
  [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  {ρ : Representation LL G V}

theorem redT_mem_BQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (a : ↥(latticeCocycles L)) (ha : (Submodule.Quotient.mk a : LatticeCohomology L) = 0) : redT L I a ∈ BQ L I hI := by
  rw [Submodule.Quotient.mk_eq_zero] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  refine ⟨I.mkQ ⟨x, hx⟩, ?_⟩
  funext g
  have h1 : evT L g a = actT L g ⟨x, hx⟩ - ⟨x, hx⟩ := Subtype.ext (congrFun hxa g).symm
  show actQ L I hI g (I.mkQ ⟨x, hx⟩) - I.mkQ ⟨x, hx⟩ = I.mkQ (evT L g a)
  rw [h1, map_sub]
  rfl


omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in
theorem exists_smul_mem [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) (w : V) :
    ∃ b : O, b ≠ 0 ∧ b • w ∈ L.T := by
  first
  | exact @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem ..)

theorem exists_torsion_lift [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ)
    (hρ : ∀ m, Continuous fun g => ρ g m) (s : O) (σ : LL) (hs : algebraMap O LL s = σ) (hσ : σ ≠ 0)
    (c : G → ↥L.T ⧸ (Ideal.span {s} • ⊤ : Submodule O ↥L.T))
    (hc : (fun g => (Submodule.Quotient.mk (σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) : V ⧸ L.T)) ∈ BD L) :
    ∃ a : ↥(latticeCocycles L), (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) ∧
      redT L _ a = c := by
  obtain ⟨vb, hvb⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ vb
  have h1 : ∀ g, (ρ g v - v) - σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∈ L.T := by
    intro g
    rw [← Submodule.Quotient.eq, ← congrFun hvb g, Submodule.Quotient.mk_sub]
    rfl
  have hspec : ∀ g, ∃ y : ↥L.T, (y : V) = Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∧
      Submodule.Quotient.mk y = c g := fun g =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (c g)).choose_spec⟩
  choose y hy hyc using hspec
  set w : V := σ • v with hw
  have h2 : ∀ g, ρ g w - w = (y g : V) + s • ((⟨_, h1 g⟩ : ↥L.T) : V) := by
    intro g
    rw [← algebraMap_smul LL s, hs, hy, hw, map_smul]
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hσ, one_smul]
    abel
  have h3 : ∀ g, ρ g w - w ∈ L.T := fun g => by
    rw [h2]; exact L.T.add_mem (y g).2 (L.T.smul_mem _ (h1 g))
  have hZ : (fun g => ρ g w - w) ∈ latticeCocycles L := by
    refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => h3 g⟩
    · simp_rw [sub_eq_add_neg]
      exact (hρ w).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
  refine ⟨⟨_, hZ⟩, ?_, ?_⟩
  · obtain ⟨b, hb, hbw⟩ := exists_smul_mem L w
    refine ⟨⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩, ?_⟩
    show b • (Submodule.Quotient.mk ⟨_, hZ⟩ : LatticeCohomology L) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨b • w, hbw, ?_⟩
    funext g
    show ρ g (b • w) - b • w = b • (ρ g w - w)
    rw [smul_sub, LinearMap.map_smul_of_tower]
  · funext g
    rw [← hyc g]
    show (Submodule.Quotient.mk (evT L g ⟨_, hZ⟩) : ↥L.T ⧸ _) = _
    rw [Submodule.Quotient.eq, GlobalTheory.TateOrth.mem_span_smul_top]
    refine ⟨⟨_, h1 g⟩, Subtype.ext ?_⟩
    show (ρ g w - w) - y g = _
    rw [h2, add_sub_cancel_left]
    rfl

theorem exists_finset_red (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    [Finite ↥(Submodule.torsion O (LatticeCohomology L))] :
    ∃ F : Finset (QuotientCohomology L I hI), F.card ≤ Nat.card ↥(Submodule.torsion O (LatticeCohomology L)) ∧
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)),
        (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) → redT L I a = c →
        (Submodule.Quotient.mk c : QuotientCohomology L I hI) ∈ F := by
  classical
  letI := Fintype.ofFinite ↥(Submodule.torsion O (LatticeCohomology L))
  have key : ∀ t : ↥(Submodule.torsion O (LatticeCohomology L)), ∃ x : QuotientCohomology L I hI,
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t →
        redT L I a = c → (Submodule.Quotient.mk c : QuotientCohomology L I hI) = x := by
    intro t
    by_cases h : ∃ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t ∧
        redT L I a = c
    · obtain ⟨c0, a0, h0, h0'⟩ := h
      refine ⟨Submodule.Quotient.mk c0, fun c a h1 h1' => ?_⟩
      rw [Submodule.Quotient.eq]
      have := redT_mem_BQ L I hI (a - a0) (by rw [Submodule.Quotient.mk_sub, h0, h1, sub_self])
      rw [map_sub, h0', h1'] at this
      exact this
    · exact ⟨0, fun c a h1 h1' => absurd ⟨c, a, h1, h1'⟩ h⟩
  choose ψ hψ using key
  refine ⟨Finset.univ.image ψ, ?_, fun c a ha hac => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  · exact Finset.mem_image.2 ⟨⟨_, ha⟩, Finset.mem_univ _, (hψ ⟨_, ha⟩ c a rfl hac).symm⟩

theorem ker_bounded_gen [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (hfg : Module.Finite O (LatticeCohomology L))
    (ℓ : O) (σ : LL) (hs : algebraMap O LL ℓ = σ) (hσ : σ ≠ 0) (hℓ : ¬ IsUnit ℓ)
    (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n})) :
    ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI : StableSub L (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)),
      ∃ F : Finset (QuotientCohomology L _ hI), F.card ≤ C0 ∧ ∀ c : ↥(quotientCocycles L _ hI),
        (fun g => (Submodule.Quotient.mk ((σ ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _
          ((c : G → ↥L.T ⧸ (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)) g)) : V ⧸ L.T)) ∈ BD L →
        (Submodule.Quotient.mk c : QuotientCohomology L _ hI) ∈ F ∧
          (ℓ ^ k0) • (Submodule.Quotient.mk c : QuotientCohomology L _ hI) = 0 := by
  have hℓ0 : ℓ ≠ 0 := fun h => hσ (by rw [← hs, h, map_zero])
  obtain ⟨hF, k, hk⟩ := torsion_finite_and_killed ℓ hℓ0 hℓ hfin (LatticeCohomology L)
  refine ⟨Nat.card ↥(Submodule.torsion O (LatticeCohomology L)), k, fun r hI => ?_⟩
  obtain ⟨F, hFc, hFm⟩ := exists_finset_red L _ hI
  refine ⟨F, hFc, fun c hc => ?_⟩
  obtain ⟨a, ha, hac⟩ := exists_torsion_lift L hρ (ℓ ^ r) (σ ^ r)
    (by rw [map_pow, hs]) (pow_ne_zero _ hσ) _ hc
  refine ⟨hFm c a ha hac, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have := redT_mem_BQ L _ hI (ℓ ^ k • a)
    (by rw [Submodule.Quotient.mk_smul]; exact hk _ ha)
  rw [map_smul, hac] at this
  exact this

end Gen

theorem ker_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ), ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ F : Finset (QuotientCohomology LA' _ hI'), F.card ≤ C0 ∧ ∀ c' : ↥(quotientCocycles LA' _ hI'), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ BD LA' → (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') ∈ F ∧ (((l : ℕ) : O) ^ k0) • (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hO A' LA'
  have hgc := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO
  have hfg : Module.Finite O (LatticeCohomology LA') := GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  letI hD : IsDomain O := hO.1.choose
  haveI : IsDiscreteValuationRing O := hO.1.choose_spec.1
  haveI : IsFractionRing O LL := hO.1.choose_spec.2
  have hlLL : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have hℓu : ¬ IsUnit ((l : ℕ) : O) :=
    GlobalTheory.DoubleAnnihilator.not_isUnit_of_adicComplete _ hgc.2.2.2
  exact ker_bounded_gen (G := ↥(GK K)) (LL := LL) (O := O) (V := A'.V) (ρ := A'.ρ) LA' A'.cont hfg
    ((l : ℕ) : O) ((l : ℕ) : LL) (map_natCast (algebraMap O LL) l) hlLL hℓu hgc.2.2.1

end GlobalTheory.KerToDivisible
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedFiniteCohomologyQuotientsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_finite_cohomology_quotients : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ), ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ F : Finset (QuotientCohomology LA' _ hI'), F.card ≤ C0 ∧ ∀ c' : ↥(quotientCocycles LA' _ hI'), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ BD LA' → (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') ∈ F ∧ (((l : ℕ) : O) ^ k0) • (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') = 0 := by
  first | exact @GlobalTheory.KerToDivisible.ker_bounded | exact GlobalTheory.KerToDivisible.ker_bounded | (intros; apply GlobalTheory.KerToDivisible.ker_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocycles
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DivLift

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mk_inv_smul_liftQ (L : Lattice (O := O) ρ) (a : O) (ha : algebraMap O LL a ≠ 0)
    (y : ↥L.T) :
    (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y)) : V ⧸ L.T) =
      Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • (y : V)) := by
  obtain ⟨y0, hy0, hs⟩ : ∃ y0 : ↥L.T, (y0 : V) = Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y) ∧
      (Submodule.Quotient.mk y0 : ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) =
        Submodule.Quotient.mk y :=
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk y)).choose_spec⟩
  rw [← hy0]
  have hmem := (Submodule.Quotient.eq _).1 hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨t, -, ht⟩ := hmem
  have ht' : a • (t : V) = (y0 : V) - (y : V) := congrArg Subtype.val ht
  rw [Submodule.Quotient.eq, ← smul_sub, ← ht', ← algebraMap_smul LL a, smul_smul,
    inv_mul_cancel₀ ha, one_smul]
  exact t.2

theorem inv_smul_liftQ_mem_Z1D [TopologicalSpace G] (L : Lattice (O := O) ρ) (a : O)
    (ha : algebraMap O LL a ≠ 0) (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T))
    (c : G → ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (hc : c ∈ quotientCocycles L _ hI) :
    (fun g => (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) :
      V ⧸ L.T)) ∈ divisibleCocycles L := by
  refine ⟨hc.1.comp (fun x => (Submodule.Quotient.mk
    ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ x) : V ⧸ L.T)), fun g h => ?_⟩
  have hgh := hc.2 g h
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (c g)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (c h)
  have h1 : c (g * h) = Submodule.Quotient.mk (x + actT L g y) := by
    rw [hgh, ← hx, ← hy]; rfl
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + actD L g (Submodule.Quotient.mk _)
  rw [h1, ← hx, ← hy, mk_inv_smul_liftQ L a ha, mk_inv_smul_liftQ L a ha,
    mk_inv_smul_liftQ L a ha]
  show _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk (ρ g ((algebraMap O LL a)⁻¹ • (y : V)))
  rw [← Submodule.Quotient.mk_add, map_smul, ← smul_add]
  rfl

end Gen

theorem pow_inv_smul_liftQ_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  intro l _ K LL _ _ _ O _ _ _ A' LA' r hI' c'
  have he : algebraMap O LL (((l : ℕ) : O) ^ r) = ((l : ℕ) : LL) ^ r := by
    rw [map_pow, map_natCast]
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have := inv_smul_liftQ_mem_Z1D LA' (((l : ℕ) : O) ^ r) (by rw [he]; exact pow_ne_zero _ hl)
    hI' c'.1 c'.2
  rwa [he] at this

end GlobalTheory.DivLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocyclesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  first | exact @GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | exact GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | (intros; apply GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfDoubleAnnihilatorPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfDoubleAnnihilatorPairing
namespace GlobalTheory

theorem card_le_of_double_annihilator (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X]
    [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X]
    (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O)
    (h1 : ∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S)
    (h2 : ∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0)
    (h3 : ∀ e : E, a • e = 0 → e ∈ Es) :
    Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  classical
  let L : X →ₗ[O] (F → E) :=
    LinearMap.pi fun y => if (∀ s ∈ S, β (y : Y) s = 0) then β y else 0
  have hL : ∀ x (y : F), L x y = if (∀ s ∈ S, β (y : Y) s = 0) then β y x else 0 := by
    intro x y
    simp only [L, LinearMap.pi_apply]
    split_ifs <;> rfl
  have hS : S ≤ LinearMap.ker L := by
    intro x hx
    rw [LinearMap.mem_ker]
    funext y
    rw [hL]
    split_ifs with h
    · exact h x hx
    · rfl
  have hker : LinearMap.ker L ≤ S := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply h1
    intro y hy
    have := congrFun hx ⟨y, (h2 y hy).1⟩
    rw [hL, if_pos hy] at this
    exact this
  have hmem : ∀ x (y : F), L x y ∈ Es := by
    intro x y
    apply h3
    rw [hL]
    split_ifs with h
    · rw [← LinearMap.smul_apply, ← map_smul, (h2 y h).2, map_zero, LinearMap.zero_apply]
    · exact smul_zero a
  let g : X ⧸ S → (F → Es) := fun q y =>
    ⟨S.liftQ L hS q y, by
      induction q using Submodule.Quotient.induction_on with
      | H x => simpa using hmem x y⟩
  have hinj : Function.Injective g := by
    intro q r hqr
    have h' : S.liftQ L hS q = S.liftQ L hS r := by
      funext y
      have := congrFun hqr y
      simpa [g] using congrArg Subtype.val this
    exact (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot S L hS hker)) h'
  have hq : Nat.card (X ⧸ S) ≤ Es.card ^ F.card := by
    have := Nat.card_le_card_of_injective g hinj
    rwa [Nat.card_fun, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard] at this
  rw [Submodule.card_eq_card_quotient_mul_card S, mul_comm]
  exact Nat.mul_le_mul_right _ hq

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfDoubleAnnihilatorPairingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_of_double_annihilator_pairing : ∀ (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X] (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O), (∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S) → (∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0) → (∀ e : E, a • e = 0 → e ∈ Es) → Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  first | exact @GlobalTheory.card_le_of_double_annihilator | exact GlobalTheory.card_le_of_double_annihilator | (intros; apply GlobalTheory.card_le_of_double_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDual
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BoundedIndex


set_option maxHeartbeats 1000000 in
theorem h1_reduction_index_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' LA LA' m hm
  obtain ⟨L1, hL1⟩ := GlobalTheory.T.exists_cyclotomic_integral_lattice l P K LL O hO
  obtain ⟨C0, k0, hF⟩ := GlobalTheory.T.bounded_finite_cohomology_quotients hT l P K LL O hO A' LA'
  obtain ⟨Es, hEs⟩ := GlobalTheory.T.exists_finset_primePow_torsion_quotient l LL O hO k0
  have hEs1 : 1 ≤ Es.card := Finset.card_pos.2 ⟨0, hEs 0 (smul_zero _)⟩
  refine ⟨Es.card ^ C0, pow_pos hEs1 _, fun r hI => ?_⟩
  have hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) :=
    GlobalTheory.TateOrth.stable_span_smul_top LA' _
  haveI hX := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A LA r hI
  haveI hY := GlobalTheory.T.finite_H1_reduction hT l K LL O hO A' LA' r hI'
  haveI : Module.Finite O (QuotientCohomology LA' _ hI') := Module.Finite.of_finite
  obtain ⟨f, hker, hf⟩ := GlobalTheory.T.ker_reduction_H1_eq l P K LL O hO A LA r hI
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.T.tate_pairing_lattice_level_primePow hT l P K LL O hO L1 hL1 A A' LA LA' m hm r hI hI'
  obtain ⟨F, hFc, hFm⟩ := hF r hI'
  have hcardS : Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) =
      Nat.card (LinearMap.range f) := by
    have key : ∀ N : Submodule O (LatticeCohomology LA), LinearMap.ker f = N → Nat.card (LatticeCohomology LA ⧸ N) = Nat.card (LinearMap.range f) := by
      rintro N rfl
      exact Nat.card_congr f.quotKerEquivRange.toEquiv
    exact key _ hker
  rw [hcardS]
  refine ⟨Nat.card_le_card_of_injective _ Subtype.val_injective, ?_⟩
  have hdd : ∀ c, (∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → β y c = 0) → c ∈ LinearMap.range f :=
    GlobalTheory.mem_of_forall_annihilator_annihilator l LL O hO _ _ β (LinearMap.range f)
      (fun c hc => by rw [hβ1 c hc]; exact Submodule.zero_mem _)
  have hA : ∀ y, (∀ s ∈ LinearMap.range f, β y s = 0) → y ∈ F ∧ ((l : ℕ) : O) ^ k0 • y = 0 := by
    intro y hy
    obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hFm c'
    refine GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m hm _
      (GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles l K LL O hO A' LA' r hI' c') fun d hd => ?_
    obtain ⟨h, hfd⟩ := hf ⟨d, hd⟩
    have h0 : β (Submodule.Quotient.mk c') (f (Submodule.Quotient.mk ⟨d, hd⟩)) = 0 := hy _ ⟨_, rfl⟩
    exact hβ2 ⟨d, hd⟩ h c' ((congrArg (β (Submodule.Quotient.mk c')) hfd).symm.trans h0)
  calc Nat.card (QuotientCohomology LA _ hI) ≤ Es.card ^ F.card * Nat.card (LinearMap.range f) :=
        GlobalTheory.T.card_le_of_double_annihilator_pairing O _ _ _ β (LinearMap.range f) F Es _ hdd hA hEs
    _ ≤ Es.card ^ C0 * Nat.card (LinearMap.range f) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hEs1 hFc)

end GlobalTheory.BoundedIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDualStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_reduction_index_bound_of_tateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  first | exact @GlobalTheory.BoundedIndex.h1_reduction_index_bounded | exact GlobalTheory.BoundedIndex.h1_reduction_index_bounded | (intros; apply GlobalTheory.BoundedIndex.h1_reduction_index_bounded <;> assumption)
end
