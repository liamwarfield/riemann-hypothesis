module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDual
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDual
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.BlochKatoDuality.Br

namespace GlobalTheory.TatePair

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)

theorem cup_coboundary_right (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) (hc : (c : G → A'.V ⧸ LA'.T) ∈ BD LA') :
    cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hcg : ∀ h, (c : G → A'.V ⧸ LA'.T) h =
      repD LA' h (Submodule.Quotient.mk v) - Submodule.Quotient.mk v := fun h =>
    (congrFun hw h).symm
  have hT : IsOpen (L1.T : Set LL) := integers_isOpen PD L1 hL1 hopen
  have hcont : Continuous fun g : G => P ((d : G → A.V) g) (A'.ρ g v) :=
    (IsModuleTopology.continuous_bilinear_of_finite_left P).comp
      (d.2.1.1.prodMk (A'.cont v))
  have hlc : IsLocallyConstant fun g : G =>
      -(Submodule.Quotient.mk (P ((d : G → A.V) g) (A'.ρ g v)) : LL ⧸ L1.T) :=
    (locConst_mk L1.T hT _ hcont).neg
  refine ⟨fun g => -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d),
    ⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  show repD L1 g (-torsionPairing PD hd L1 hL1 (repD LA' h (Submodule.Quotient.mk v)) (evT LA h d))
      - -torsionPairing PD hd L1 hL1 (repD LA' (g * h) (Submodule.Quotient.mk v)) (evT LA (g * h) d)
      + -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d) =
    cupModuloIntegers PD hd L1 hL1 c d (g, h)
  rw [cup_apply_alt]
  simp only [hcg, map_neg, ← torsionPairing_equivariant, lattice_cocycle_mul, map_mul, Module.End.mul_apply, map_add (f := _),
    map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end Gen

theorem integral_pairing : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type)
    [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
      (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m →
    ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T),
      (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧
      (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' m hd
  obtain ⟨e⟩ := GlobalTheory.T.tate_H2_period_datum hT l P K LL O hG L1 hL1
  obtain ⟨⟨hO, hDVR, hFr⟩, -, -, htr, hopen⟩ := hG
  haveI := hO
  haveI := hDVR
  haveI := hFr
  haveI := htr
  obtain ⟨pr, hpr⟩ := exists_pr (P.PD K) hopen hd L1 hL1
  refine ⟨(pr.compr₂ e.toLinearMap).flip ∘ₗ Submodule.mkQ _, ?_, ?_, ?_⟩
  · intro d c
    show e (pr c (Submodule.Quotient.mk d)) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact hpr c d
  · intro d c hdB
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_mem_coboundaries (P.PD K) hd L1 hL1 c d hdB
  · intro d c hc
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_coboundary_right (P.PD K) hd L1 hL1 hopen c d hc

end GlobalTheory.TatePair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDualStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tate_pairing_lattice_dual : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T), (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧ (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  first | exact @GlobalTheory.TatePair.integral_pairing | exact GlobalTheory.TatePair.integral_pairing | (intros; apply GlobalTheory.TatePair.integral_pairing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModIntegerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (M N : Type) [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O M] (β : M →ₗ[O] N →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL))) (S : Submodule O N), (∀ c, (∀ d, β d c = 0) → c ∈ S) → ∀ c, (∀ d, (∀ s ∈ S, β d s = 0) → β d c = 0) → c ∈ S := by
  first | exact @GlobalTheory.mem_of_forall_annihilator_annihilator | exact GlobalTheory.mem_of_forall_annihilator_annihilator | (intros; apply GlobalTheory.mem_of_forall_annihilator_annihilator <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tate_double_annihilator : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdual S hBS hSZ c hc hann
  obtain ⟨β, hβ0, hβB, -⟩ := GlobalTheory.T.integral_tate_pairing_lattice_dual hT l P K LL O hO L1 hL1 A A' LA LA' m hdual
  haveI : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hT l P K LL O hO A LA
  let e : (LL ⧸ L1.T) ≃ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    Submodule.quotEquivOfEq _ _ hL1
  let β₁ : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    β.compr₂ e.toLinearMap
  have hβ₁ : ∀ d c, β₁ d c = 0 ↔ β d c = 0 := fun d c => by
    simp only [β₁, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
    exact e.map_eq_zero_iff
  have hker : (latticeCoboundaries LA).comap (latticeCocycles LA).subtype ≤ LinearMap.ker β₁ := by
    intro d hd
    rw [LinearMap.mem_ker]
    ext c
    exact (hβ₁ d c).2 (hβB d c hd)
  let β₂ : LatticeCohomology LA →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype).liftQ β₁ hker
  have hβ₂ : ∀ d c, β₂ (Submodule.Quotient.mk d) c = β₁ d c := fun d c => rfl
  have key := GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers l LL O hO (LatticeCohomology LA) ↥(divisibleCocycles LA') β₂ (S.comap (divisibleCocycles LA').subtype) ?_
    ⟨c, hc⟩ ?_
  · exact key
  · intro c' hc'
    show c'.1 ∈ S
    apply hBS
    apply GlobalTheory.T.lattice_dual_pairing_cyclotomic hT l P K LL O hO L1 hL1 A A' LA LA' m hdual c'.1 c'.2
    intro d hd
    have h := hc' (Submodule.Quotient.mk ⟨d, hd⟩)
    rw [hβ₂, hβ₁] at h
    exact (hβ0 ⟨d, hd⟩ c').1 h
  · intro d hd
    induction d using Submodule.Quotient.induction_on with
    | _ d0 =>
    rw [hβ₂, hβ₁]
    apply (hβ0 d0 ⟨c, hc⟩).2
    apply hann d0.1 d0.2
    intro s hs
    have h := hd ⟨s, hSZ hs⟩ hs
    rw [hβ₂, hβ₁] at h
    exact (hβ0 d0 ⟨s, hSZ hs⟩).1 h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomicStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_dual_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  first | exact @GlobalTheory.tate_double_annihilator | exact GlobalTheory.tate_double_annihilator | (intros; apply GlobalTheory.tate_double_annihilator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSpan
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TwistDR

theorem exists_unit_of_span {k F R : Type} [Field k] [Infinite k] [Field F] [CommRing R] [Algebra F R]
    [Module k R] [Module.Finite F R] (hk : ∀ (c : k) (x : R), ∃ r : R, c • x = r * x)
    (U : Submodule k R) (hU : Submodule.span F (U : Set R) = ⊤) : ∃ d ∈ U, IsUnit d := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite F R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let S : MaximalSpectrum R → Submodule k U := fun m =>
    { carrier := {x | (x : R) ∈ m.asIdeal}
      add_mem' := fun ha hb => m.asIdeal.add_mem ha hb
      zero_mem' := m.asIdeal.zero_mem
      smul_mem' := fun c x hx => by
        obtain ⟨r, hr⟩ := hk c x
        change c • (x : R) ∈ m.asIdeal
        rw [hr]
        exact m.asIdeal.mul_mem_left r hx }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : Submodule.span F (U : Set R) ≤ m.asIdeal.restrictScalars F :=
      Submodule.span_le.2 fun x hx => (hm ▸ Submodule.mem_top : (⟨x, hx⟩ : U) ∈ S m)
    exact h1 (hU ▸ Submodule.mem_top)
  have h2 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 h2
  refine ⟨x, x.2, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hx
  exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR (ρ : Representation LL G V) (x : V ⊗[Qp] BdR) :
    x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, sub_eq_zero]

def tw (χ : G → LL) (g : G) : BdR ⊗[Qp] LL →ₗ[Qp] BdR ⊗[Qp] LL :=
  TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) (LinearMap.mulLeft Qp (χ g))

theorem tw_tmul (χ : G → LL) (g : G) (b : BdR) (c : LL) :
    tw PD χ g (b ⊗ₜ[Qp] c) = PD.actdR g b ⊗ₜ[Qp] (χ g * c) := rfl

theorem tw_smul (χ : G → LL) (g : G) (b : BdR) (w : BdR ⊗[Qp] LL) :
    tw PD χ g (b • w) = PD.actdR g b • tw PD χ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [tw_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

def twInv (χ : G → LL) : Submodule K (BdR ⊗[Qp] LL) where
  carrier := {x | ∀ g, tw PD χ g x = x}
  add_mem' ha hb g := by rw [map_add (f := _), ha g, hb g]
  zero_mem' g := map_zero _
  smul_mem' c x hx g := by
    rw [← algebraMap_smul BdR c x, tw_smul, AlgEquiv.commutes, hx g]

theorem finrank_twInv [FiniteDimensional Qp LL] (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank K ↥(twInv PD χ) = finrank Qp LL := by
  haveI := PD.finK
  let e : (Fin 1 → LL) ⊗[Qp] BdR ≃ₗ[Qp] BdR ⊗[Qp] LL :=
    ((LinearEquiv.funUnique (Fin 1) Qp LL).rTensor BdR).trans (TensorProduct.comm Qp LL BdR)
  have he : ∀ g x, e (actVdR PD ν g x) = tw PD χ g (e x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [e, actVdR, tw_tmul, hν]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hm : ((DdR PD ν).restrictScalars Qp).map (e : _ →ₗ[Qp] _) = (twInv PD χ).restrictScalars Qp := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.restrictScalars_mem, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [← he, e.injective.eq_iff]
  have h1 : finrank Qp ↥(twInv PD χ) = finrank Qp ↥(DdR PD ν) := by
    have := LinearEquiv.finrank_map_eq e ((DdR PD ν).restrictScalars Qp)
    rw [hm] at this
    exact this
  haveI : Module.Free LL ↥(DdR PD ν) := Module.Free.of_divisionRing LL ↥(DdR PD ν)
  rw [← Module.finrank_mul_finrank Qp K ↥(twInv PD χ), ← Module.finrank_mul_finrank Qp LL ↥(DdR PD ν), h,
    finrank_fintype_fun_eq_card, Fintype.card_fin, mul_one, mul_comm (finrank Qp LL)] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem exists_unit [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR) (χ : G → LL)
    (h : finrank K ↥(twInv PD χ) = finrank Qp LL) : ∃ d ∈ twInv PD χ, IsUnit d := by
  letI : Field BdR := hB.toField
  haveI : Infinite K := Infinite.of_injective _ (algebraMap Qp K).injective
  have hpos : 0 < finrank Qp LL := finrank_pos
  haveI : Module.Finite K ↥(twInv PD χ) := Module.finite_of_finrank_pos (h ▸ hpos)
  refine exists_unit_of_span (F := BdR) (fun c x => ⟨algebraMap K _ c, Algebra.smul_def c x⟩) _ ?_
  let v := Module.finBasisOfFinrankEq K _ h
  have h1 : LinearIndependent K fun i => (v i : BdR ⊗[Qp] LL) :=
    v.linearIndependent.map' (twInv PD χ).subtype (twInv PD χ).ker_subtype
  have h2 : LinearIndependent BdR fun i => (v i : BdR ⊗[Qp] LL) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    refine GlobalTheory.RegularRing.linearIndepOn_of_invariant (fun g b => PD.actdR g b)
      (fun g => (tw PD χ g).toAddMonoidHom) (tw_smul PD χ) ?_ _ (fun g i => (v i).2 g) s
      (h1.linearIndepOn _)
    intro b b' hb hg
    obtain ⟨c, hc⟩ := PD.invdR (b' / b) fun g => by
      have h3 : PD.actdR g b ≠ 0 := (map_ne_zero _).2 hb
      rw [map_div₀, div_eq_div_iff h3 hb]
      linear_combination hg g
    exact ⟨c, by rw [hc, div_mul_cancel₀ _ hb]⟩
  haveI : Nonempty (Fin (finrank Qp LL)) := ⟨⟨0, hpos⟩⟩
  rw [eq_top_iff, ← h2.span_eq_top_of_card_eq_finrank (by simp)]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact (v i).2


variable (V) in
def mulR : BdR ⊗[Qp] LL →ₗ[Qp] (V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR) :=
  TensorProduct.lift (LinearMap.mk₂ Qp
    (fun b c => c • AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b))
    (fun b b' c => by ext; simp [add_mul, tmul_add])
    (fun q b c => by ext; simp [smul_comm q c])
    (fun b c c' => add_smul _ _ _)
    (fun q b c => smul_assoc _ _ _))

theorem mulR_tmul (b : BdR) (c : LL) (v : V) (b' : BdR) :
    mulR V (b ⊗ₜ[Qp] c) (v ⊗ₜ[Qp] b') = (c • v) ⊗ₜ[Qp] (b * b') := by
  simp [mulR, smul_tmul']

theorem mulR_one (x : V ⊗[Qp] BdR) : mulR V (1 : BdR ⊗[Qp] LL) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [Algebra.TensorProduct.one_def, mulR_tmul, one_smul, one_mul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mulR_mul (d d' : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    mulR V (d * d') x = mulR V d (mulR V d' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ =>
      induction d' using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add (f := _), LinearMap.add_apply, hx, hy]
      | tmul b₂ c₂ => simp only [Algebra.TensorProduct.tmul_mul_tmul, mulR_tmul, mul_smul, mul_assoc]

theorem act_mulR (ρ ρ' : Representation LL G V) (χ : G → LL) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (g : G) (d : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ' g (mulR V d x) = mulR V (tw PD χ g d) (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ => simp [mulR_tmul, tw_tmul, actVdR, hρ, mul_smul]

theorem finrank_DdR_twist [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank LL ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) := by
  obtain ⟨_, hd, d, rfl⟩ := exists_unit PD hB χ (finrank_twInv PD ν χ hν h)
  let e : V ⊗[Qp] BdR ≃ₗ[LL] V ⊗[Qp] BdR := LinearEquiv.ofLinear (mulR V d.1) (mulR V d⁻¹.1)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.mul_inv, mulR_one, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.inv_mul, mulR_one, LinearMap.id_apply])
  have he : ∀ g x, actVdR PD ρ' g (e x) = e (actVdR PD ρ g x) := fun g x => by
    change actVdR PD ρ' g (mulR V d.1 x) = mulR V d.1 _
    rw [act_mulR PD ρ ρ' χ hρ, hd g]
  have hm : (DdR PD ρ).map (e : _ →ₗ[LL] _) = DdR PD ρ' := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_DdR, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [he, e.injective.eq_iff]
  rw [← hm, LinearEquiv.finrank_map_eq]

end Generic

theorem isDR_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsDR (P.PD K) ν → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ') := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ h
  haveI := LL.2
  unfold IsDR
  rw [finrank_DdR_twist (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ ρ' ν χ hν hρ h]

end GlobalTheory.TwistDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL Module

noncomputable section

namespace GlobalTheory.HWL.SandProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA} {Zl : Type} [CommRing Zl] {zl : PowerSeries Zl →+* LetA O n}

theorem jD_smulA (E : WEt I) (T : LocLat G Qp LL O) (a : LetA O n) (y : E.DD T) :
    E.jD T (a • y) = inclR (I.io a) • E.jD T y := by
  rw [← algebraMap_smul R.EE a y, E.jD_smul, I.ioE_ext]

theorem φD_smulA (E : WEt I) (T : LocLat G Qp LL O) (a : LetA O n) (y : E.DD T) :
    E.φD T (a • y) = letφ R.φ₀ a • E.φD T y := by
  rw [← algebraMap_smul R.EE a y, E.φD_smul, R.φE_ext, algebraMap_smul]

theorem φA_π (R : WSer Γ) : letφ (n := n) R.φ₀ letπ = letπ * (fun _ => R.q₀) := by
  funext i
  exact R.φ₀_X

theorem φA_one_add_π (R : WSer Γ) : letφ (n := n) R.φ₀ (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add (f := _), map_one, φA_π]
  funext i
  have := R.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.one_apply, letπ]
  rw [this]; ring

theorem φA_pow_one_add_π (R : WSer Γ) (k : ℕ) :
    (letφ (n := n) R.φ₀ ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, map_pow, φA_one_add_π, ← pow_mul, pow_succ']

theorem frobenius_inclusion_X_eq_mul_Q (I : WIo R RA RW inclR φR gR πA)
    (hu : φR (inclR (1 + πA)) = inclR (1 + πA) ^ PD.p) :
    φR (inclR ((1 + πA) ^ (PD.p ^ (s - 1)) - 1)) =
      inclR ((1 + πA) ^ (PD.p ^ (s - 1)) - 1) * inclR (I.io R.Q) := by
  have hX : (letφ (n := n) R.φ₀ ^ (s - 1)) letπ = (1 + letπ) ^ (PD.p ^ (s - 1)) - 1 := by
    rw [← φA_pow_one_add_π R, map_add (f := _), map_one]; ring
  have hXQ : (letφ (n := n) R.φ₀ ^ (s - 1)) letπ * R.Q =
      ((1 + letπ) ^ PD.p) ^ (PD.p ^ (s - 1)) - 1 := by
    rw [WSer.Q, ← map_mul, ← φA_π, ← pow_mul, mul_comm PD.p, pow_mul,
      ← φA_pow_one_add_π R, ← map_pow, ← φA_one_add_π R, map_add, map_one, map_add, map_one]
    ring
  have hπ : I.io (1 + letπ) = 1 + πA := by rw [map_add (f := _), map_one, I.io_π]
  have h1 : (1 + πA) ^ (PD.p ^ (s - 1)) - 1 = I.io ((letφ (n := n) R.φ₀ ^ (s - 1)) letπ) := by
    rw [hX, map_sub, map_pow, map_one, hπ]
  conv_rhs => rw [h1, ← map_mul, ← map_mul, hXQ]
  simp only [map_sub, map_pow, map_one, hπ, hu]

theorem uniform {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (q : A)
    (S : Submodule A M) (w : ι → M) (h : ∀ i, ∃ k : ℕ, q ^ k • w i ∈ S) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i, q ^ k • w i ∈ S := by
  choose k hk using h
  refine ⟨Finset.univ.sup k, fun m hm i => ?_⟩
  have : k i ≤ m := (Finset.le_sup (Finset.mem_univ i)).trans hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le this
  rw [add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk i)

theorem sand_of {E : WEt I} (Mo : WN E zl)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (P : Matrix p p RA)
      (P' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = P.map inclR * Z * P'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (x : RA) (hx : φR (inclR x) = inclR x * inclR (I.io R.Q)) [Nontrivial O]
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(Mo.N T)) :
    ∃ m : ℕ, Sand Mo T (x ^ m) := by
  classical
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  let tb := Module.finBasis O ↥T.L.T
  have hexp : ∀ y ∈ Mo.N T, ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
      y = ∑ j, c j • (b j : E.DD T) := by
    intro y hy
    refine ⟨fun j => b.repr ⟨y, hy⟩ j, ?_⟩
    have := congrArg (Mo.N T).subtype (b.sum_repr ⟨y, hy⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this.symm
  have hj : ∀ (c : Fin (Module.finrank O ↥T.L.T) → LetA O n)
      (w : Fin (Module.finrank O ↥T.L.T) → E.DD T),
      E.jD T (∑ j, c j • w j) = ∑ j, inclR (I.io (c j)) • E.jD T (w j) := by
    intro c w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => jD_smulA E T _ _
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (b i : E.DD T)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine (Mo.N_base T hT).inductionOn y ?_ ?_ ?_
    · intro z
      obtain ⟨c, hc⟩ := hexp z.1 z.2
      change E.jD T z.1 ∈ _
      rw [hc, hj]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro e z hz
      rw [E.jD_smul]
      exact Submodule.smul_mem _ _ hz
    · intro z z' hz hz'
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hz hz'
  have hli : LinearIndependent RW fun i => E.jD T (b i : E.DD T) := by
    have hs := hsp
    rw [← Finsupp.range_linearCombination, top_le_iff, LinearMap.range_eq_top] at hs
    exact OrzechProperty.injective_of_surjective_of_injective _ _
      (Algebra.TensorProduct.basis RW tb).linearIndependent hs
  obtain ⟨k₁, h1⟩ := uniform R.Q (Mo.N T) (fun i => E.φD T (b i : E.DD T))
    (fun i => Mo.N_φ T _ (b i).2)
  obtain ⟨k₂, h2⟩ := uniform R.Q (Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))))
    (fun i => (b i : E.DD T)) (fun i => Mo.N_φinv T _ (b i).2)
  replace h1 := h1 (max k₁ k₂) (le_max_left _ _)
  replace h2 := h2 (max k₁ k₂) (le_max_right _ _)
  refine ⟨max k₁ k₂, ?_⟩
  generalize max k₁ k₂ = m at h1 h2
  unfold Sand
  rw [map_pow]
  constructor
  · choose P hP using fun i => hexp _ (h1 i)
    have hup := GlobalTheory.Sandwich.upper tb inclR φR hA _ _ hx m (fun i => E.jD T (b i : E.DD T))
      (Matrix.of fun i j => I.io (P i j)) (by
        intro i
        have := congrArg (E.jD T) (hP i)
        rw [hj, jD_smulA, E.jD_φ, map_pow, map_pow] at this
        exact this)
    intro y hy
    obtain ⟨c, rfl⟩ := hexp y hy
    change _ ∈ LinearMap.range (TWincl inclR T)
    rw [hj, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_comm]
    exact GlobalTheory.Sandwich.incl_smul_mem inclR _ _ (hup j)
  · have hexp2 : ∀ y ∈ Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))),
        ∃ c : Fin (Module.finrank O ↥T.L.T) → LetA O n,
        y = ∑ j, c j • E.φD T (b j : E.DD T) := by
      intro y hy
      have : Submodule.span (LetA O n) (E.φD T '' (Mo.N T : Set (E.DD T))) ≤ Submodule.span (LetA O n)
          (Set.range fun j => E.φD T (b j : E.DD T)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨c, rfl⟩ := hexp z hz
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [φD_smulA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (this hy)
      exact ⟨c, hc.symm⟩
    choose U hU using fun i => hexp2 _ (h2 i)
    let nb : Basis (Fin (Module.finrank O ↥T.L.T)) RW (TW RW T) := Basis.mk hli hsp
    have hnb : ∀ i, nb i = E.jD T (b i : E.DD T) := fun i => Basis.mk_apply _ _ i
    have hlow := GlobalTheory.Sandwich.lower tb inclR φR hA _ _ hx m nb
      (Matrix.of fun i j => I.io (U i j)) (by
        intro i
        have := congrArg (E.jD T) (hU i)
        rw [hj, jD_smulA, map_pow, map_pow] at this
        simp only [E.jD_φ] at this
        simp only [hnb]
        exact this)
    intro t
    rw [← tb.sum_repr t, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [TensorProduct.tmul_smul, smul_comm]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc⟩ := hlow k
    rw [hc]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨c j, b j, (b j).2, ?_⟩
    rw [hnb]

end Generic

theorem εroot_pow_pred {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) :
    AI.εroot (k + 1) ^ l ^ k = AI.ε1 := by
  induction k with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ k ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem x_eq {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ)
    (hs : 1 ≤ s) :
    ((1 : RA LL) + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ (l ^ (s - 1)) - 1 =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hs
  have h : (1 : RA LL) + (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot (k + 1)) - 1) =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot (k + 1)) : Ainf l) := by
    rw [TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]; abel
  rw [h, Algebra.TensorProduct.tmul_pow, one_pow, ← map_pow, Nat.add_sub_cancel, εroot_pow_pred,
    LocAinf.π₁, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def]


set_option maxHeartbeats 1600000 in
theorem sandwich : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) := by
  intro l _ P AI K s LL hg Γ R I hI E Mo T hT
  obtain ⟨b⟩ := GlobalTheory.T.wach_lattice_free_of_crystalline l P AI K s LL hg Γ R I hI E Mo T hT
  have hp : (P.PD K).p = l := P.PD_p K
  have hx := frobenius_inclusion_X_eq_mul_Q I (by rw [hp]; exact GlobalTheory.Sandwich.φRW_teichmuller LL _)
  rw [hp, x_eq AI LL s Γ.s_pos] at hx
  obtain ⟨m, hm⟩ := sand_of Mo (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) _ hx T hT b
  refine ⟨m, ?_⟩
  have e : ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) = ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.π₁ : RA LL) ^ m := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow]
  rw [e]
  exact hm

end GlobalTheory.HWL.SandProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPiStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) := by
  first | exact @GlobalTheory.HWL.SandProof.sandwich | exact GlobalTheory.HWL.SandProof.sandwich | (intros; apply GlobalTheory.HWL.SandProof.sandwich <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptySubquotEquiv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocEulerScalars

theorem nonempty_subquot_equiv {R R' X : Type*} [Ring R] [Ring R'] [AddCommGroup X] [Module R X]
    [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    Nonempty ((Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype)) := by
  refine ⟨Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => ?_⟩
  change (B.comap Z.subtype).quotientRel a b ↔
    (B'.comap Z'.subtype).quotientRel (Equiv.subtypeEquivRight hZ a) (Equiv.subtypeEquivRight hZ b)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap]
  exact hB _

theorem localEulerChar_above : LocalFiniteness → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation Λ (Dec (F := F) A) M), (∀ m : M, l • m = 0) → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ ReciprocityTheory.Gal.locDeg v := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ A v ρ hl hA hv hc

  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule fun m => by rw [pow_one]; exact hl m
  let ρ' : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M := zmodRep (l ^ 1) ρ
  have hc' : ContAction ρ' := hc

  have hd : ∀ c : Dec (F := F) A → M, d1 ρ c = d1 ρ' c := fun c => by
    funext p
    obtain ⟨g, h⟩ := p
    rw [d1_apply, d1_apply]
    rfl
  have hZ1 : ∀ f, f ∈ Z1 ρ ↔ f ∈ Z1 ρ' := fun f => by
    rw [mem_Z1_iff_cocycle, mem_Z1_iff_cocycle]
    exact Iff.rfl
  have hB1 : ∀ f, f ∈ B1 ρ ↔ f ∈ B1 ρ' := fun f => by
    rw [mem_coboundaries1, mem_coboundaries1]
    exact Iff.rfl
  have hZ2 : ∀ f, f ∈ Z2 ρ ↔ f ∈ Z2 ρ' := fun f => by
    rw [mem_cocycles2, mem_cocycles2]
    exact Iff.rfl
  have hB2 : ∀ f, f ∈ B2 ρ ↔ f ∈ B2 ρ' := fun f => by
    rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
    simp only [hd]
  obtain ⟨e1⟩ := nonempty_subquot_equiv (Z1 ρ) (B1 ρ) (Z1 ρ') (B1 ρ') hZ1 hB1
  obtain ⟨e2⟩ := nonempty_subquot_equiv (Z2 ρ) (B2 ρ) (Z2 ρ') (B2 ρ') hZ2 hB2
  have c1 : Nat.card (H1 ρ) = Nat.card (H1 ρ') := Nat.card_congr e1
  have c2 : Nat.card (H2 ρ) = Nat.card (H2 ρ') := Nat.card_congr e2

  obtain ⟨-, h1, h2, -⟩ := hF F Ω l 1 M A ρ' v Nat.one_pos hA hc'
  have hχ := (hE F Ω l 1 M A ρ' v Nat.one_pos hA hc').1 hv
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [c1, c2]
  convert hχ using 3

  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end GlobalTheory.LocEulerScalars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftExactFunctorRepresentableTorsionModules
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftExactFunctorRepresentableTorsionModules
open CategoryTheory GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Level

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ]

def IsMin (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (A : ModuleCat.{0} Λ) (x : F.obj A) : Prop :=
  ∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : A ⟶ B, (F.map φ).hom x = 0 → φ = 0

def LeftEx (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) : Prop :=
  ∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom

theorem map_map (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) {A B C : ModuleCat.{0} Λ} (f : A ⟶ B) (g : B ⟶ C)
    (x : F.obj A) : (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by
  rw [F.map_comp]; rfl

theorem exists_min (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (hF : LeftEx F) (A : ModuleCat.{0} Λ) [Finite A]
    (hA : Tors Λ A) (x : F.obj A) :
    ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧ (F.map f).hom z = x ∧
      IsMin F C z := by
  classical
  have hex : ∃ m : ℕ, ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧
      (F.map f).hom z = x ∧ Nat.card C = m :=
    ⟨_, A, 𝟙 A, x, Function.injective_id, by rw [F.map_id]; rfl, rfl⟩
  obtain ⟨C, f, z, hf, hz, hm⟩ := Nat.find_spec hex
  refine ⟨C, f, z, hf, hz, fun B hB φ hφ => ?_⟩
  haveI : Finite C := Finite.of_injective _ hf
  have hC : Tors Λ C := fun c => by
    obtain ⟨n, hn⟩ := hA (f.hom c)
    exact ⟨n, fun r hr => hf (by rw [map_smul, hn r hr, map_zero])⟩
  obtain ⟨-, h2⟩ := hF (ModuleCat.of Λ (LinearMap.ker φ.hom)) C B hC hB
    (ModuleCat.ofHom (LinearMap.ker φ.hom).subtype) φ Subtype.val_injective
    (LinearMap.exact_subtype_ker_map φ.hom)
  obtain ⟨w, hw⟩ := (h2 z).1 hφ
  have hle : Nat.find hex ≤ Nat.card (LinearMap.ker φ.hom) :=
    Nat.find_min' hex ⟨ModuleCat.of Λ (LinearMap.ker φ.hom),
      ModuleCat.ofHom (LinearMap.ker φ.hom).subtype ≫ f, w, hf.comp Subtype.val_injective,
      by rw [← map_map, hw, hz], rfl⟩
  rw [← hm] at hle
  have hbij : Function.Bijective (LinearMap.ker φ.hom).subtype :=
    Function.Injective.bijective_of_nat_card_le Subtype.val_injective hle
  ext c
  obtain ⟨k, rfl⟩ := hbij.2 c
  exact k.2

theorem card_le_of_min [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive]
    (hfin : Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)))) (n : ℕ) :
    ∃ N : ℕ, ∀ (A : ModuleCat.{0} Λ) (x : F.obj A), Finite A →
      (∀ r ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, r • y = 0) → IsMin F A x → Nat.card A ≤ N := by
  set c := Nat.card (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) with hc
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) := ‹Finite (IsLocalRing.ResidueField Λ)›
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  refine ⟨Nat.card (Fin c → Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n), fun A x hA hn hmin => ?_⟩
  have hk : Tors Λ (IsLocalRing.ResidueField Λ) := fun b => ⟨1, fun r hr => by
    rw [pow_one] at hr
    rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff r).2 hr, zero_mul]⟩
  have hinj : Function.Injective (fun φ : A →ₗ[Λ] IsLocalRing.ResidueField Λ =>
      (F.map (ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ))).hom x) := by
    intro φ ψ h
    have := hmin (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) hk
      ((ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) - ModuleCat.ofHom ψ) (by
        rw [F.map_sub]
        exact sub_eq_zero.2 h)
    have h2 := sub_eq_zero.1 this
    exact congrArg ModuleCat.Hom.hom h2
  have h1 : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ c := Nat.card_le_card_of_injective _ hinj
  have h2 : c ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ c :=
    (Nat.lt_pow_self Finite.one_lt_card).le
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_generators_of_card_hom_residueField_le Λ A c (h1.trans h2)
  let p : Fin c → (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) →ₗ[Λ] A := fun i =>
    (IsLocalRing.maximalIdeal Λ ^ n).liftQ (LinearMap.toSpanSingleton Λ A (v i)) (fun r hr => hn r hr _)
  refine Nat.card_le_card_of_surjective (fun t => ∑ i, p i (t i)) (fun a => ?_)
  have ha : a ∈ Submodule.span Λ (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 ha
  exact ⟨fun i => Submodule.Quotient.mk (t i), rfl⟩

theorem level : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
  (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
  (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
  Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) → ∀ n : ℕ,
  ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧ (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M ⟶ B, (F.map φ).hom ξ = 0 → φ = 0) ∧
    ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M ⟶ B, (F.map φ).hom ξ = η := by
  classical
  intro Λ _ _ _ _ F _ _ hF hfin n
  obtain ⟨N, hN⟩ := card_le_of_min F hfin n
  let P : ℕ → Prop := fun m => ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧
    (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧ IsMin F M ξ ∧ Nat.card M = m
  have h0 : P (Nat.card (ModuleCat.of Λ PUnit)) :=
    ⟨ModuleCat.of Λ PUnit, 0, inferInstanceAs (Finite PUnit), fun _ _ _ => rfl, fun B _ φ _ => by
      ext c
      exact map_zero φ.hom, rfl⟩
  have hle : ∀ m, P m → m ≤ N := by
    rintro m ⟨M, ξ, h1, h2, h3, rfl⟩
    exact hN M ξ h1 h2 h3
  obtain ⟨M, ξ, hM, hMn, hmin, hcard⟩ : P (Nat.findGreatest P N) := Nat.findGreatest_spec (hle _ h0) h0
  refine ⟨M, ξ, hM, hMn, hmin, fun B hB hBn η => ?_⟩
  let A : ModuleCat.{0} Λ := ModuleCat.of Λ (M × B)
  haveI : Finite A := inferInstanceAs (Finite (M × B))
  have hAn : ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, x • y = 0 := fun r hr y =>
    Prod.ext (hMn r hr y.1) (hBn r hr y.2)
  let i1 : M ⟶ A := ModuleCat.ofHom (LinearMap.inl Λ M B)
  let i2 : B ⟶ A := ModuleCat.ofHom (LinearMap.inr Λ M B)
  let q1 : A ⟶ M := ModuleCat.ofHom (LinearMap.fst Λ M B)
  let q2 : A ⟶ B := ModuleCat.ofHom (LinearMap.snd Λ M B)
  have e11 : i1 ≫ q1 = 𝟙 M := rfl
  have e22 : i2 ≫ q2 = 𝟙 B := rfl
  have e12 : i1 ≫ q2 = 0 := rfl
  have e21 : i2 ≫ q1 = 0 := rfl
  obtain ⟨C, f, z, hf, hz, hC⟩ := exists_min F hF A (fun a => ⟨n, fun r hr => hAn r hr a⟩)
    ((F.map i1).hom ξ + (F.map i2).hom η)
  have hz1 : (F.map (f ≫ q1)).hom z = ξ := by
    rw [← map_map, hz, map_add (f := _), map_map, map_map, e11, e21, F.map_id, F.map_zero]
    exact add_zero _
  have hz2 : (F.map (f ≫ q2)).hom z = η := by
    rw [← map_map, hz, map_add (f := _), map_map, map_map, e12, e22, F.map_id, F.map_zero]
    exact zero_add _
  haveI hCf : Finite C := Finite.of_injective _ hf
  set g := f ≫ q1 with hg
  have hsurj : Function.Surjective g.hom := by
    have := hmin (ModuleCat.of Λ (M ⧸ LinearMap.range g.hom)) (fun b => ⟨n, fun r hr => by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [← Submodule.Quotient.mk_smul, hMn r hr, Submodule.Quotient.mk_zero]⟩)
      (ModuleCat.ofHom (LinearMap.range g.hom).mkQ) (by
        have e : g ≫ ModuleCat.ofHom (LinearMap.range g.hom).mkQ = 0 := by
          ext c
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨c, rfl⟩
        rw [← hz1, map_map, e, F.map_zero]
        rfl)
    intro m
    have h3 : (LinearMap.range g.hom).mkQ m = 0 :=
      congrArg (fun φ : M ⟶ ModuleCat.of Λ (M ⧸ LinearMap.range g.hom) => φ.hom m) this
    exact (Submodule.Quotient.mk_eq_zero _).1 h3
  have hPC : P (Nat.card C) := ⟨C, z, hCf, fun r hr y => hf (by rw [map_smul, hAn r hr, map_zero]), hC, rfl⟩
  have hcle : Nat.card C ≤ Nat.card M := hcard ▸ Nat.le_findGreatest (hle _ hPC) hPC
  have hbij : Function.Bijective g.hom := hsurj.bijective_of_nat_card_le hcle
  let e := LinearEquiv.ofBijective g.hom hbij
  refine ⟨(ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) ≫ f ≫ q2, ?_⟩
  have e3 : g ≫ (ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) = 𝟙 C := by
    ext c
    exact e.symm_apply_apply c
  rw [← hz1, map_map, ← Category.assoc, e3, Category.id_comp, hz2]

end GlobalTheory.SelFun.Level
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftExactFunctorRepresentableTorsionModulesStatement
open CategoryTheory GlobalTheory.SelFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftExact_functor_representable_torsion_modules : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
  (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
  (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
  Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) → ∀ n : ℕ,
  ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧ (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M ⟶ B, (F.map φ).hom ξ = 0 → φ = 0) ∧
    ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M ⟶ B, (F.map φ).hom ξ = η := by
  first | exact @GlobalTheory.SelFun.Level.level | exact GlobalTheory.SelFun.Level.level | (intros; apply GlobalTheory.SelFun.Level.level <;> assumption)
end
end
