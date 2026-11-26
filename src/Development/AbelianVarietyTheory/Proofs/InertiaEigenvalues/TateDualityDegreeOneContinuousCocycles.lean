module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemCoboundariesOfTateOrthogonal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalTatePairingBilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanQ
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtension
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem span_cocycles_ext {G F E : Type} [Group G] [TopologicalSpace G] [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] [Field E] [Algebra F E] [TopologicalSpace E]
    [FiniteDimensional F E] [IsModuleTopology F E] [IsTopologicalRing E] (χ : G → F)
    (H : ∃ z0 : G × G → F, (Continuous z0 ∧ ∀ g h k,
        χ g * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → F, Continuous z →
        (∀ g h k, χ g * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : F, ∃ f : G → F, Continuous f ∧
          ∀ g h, χ g * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h)) :
    ∃ z0 : G × G → E, (Continuous z0 ∧ ∀ g h k,
        algebraMap F E (χ g) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧
      ∀ z : G × G → E, Continuous z →
        (∀ g h k, algebraMap F E (χ g) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) →
        ∃ x : E, ∃ f : G → E, Continuous f ∧
          ∀ g h, algebraMap F E (χ g) * f h - f (g * h) + f g = z (g, h) - x * z0 (g, h) := by
  obtain ⟨z0, ⟨hc0, hz0⟩, H⟩ := H
  haveI : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E
  have hA : Continuous (algebraMap F E) := by
    have : (algebraMap F E : F → E) = fun a => a • (1 : E) := by
      funext a; rw [Algebra.algebraMap_eq_smul_one]
    rw [this]; fun_prop
  refine ⟨fun p => algebraMap F E (z0 p), ⟨hA.comp hc0, fun g h k => ?_⟩, fun z hc hz => ?_⟩
  · have := congrArg (algebraMap F E) (hz0 g h k)
    simpa using this
  · let b := Module.finBasis F E
    have hb : ∀ i, Continuous (b.coord i) := fun i =>
      IsModuleTopology.continuous_of_linearMap (b.coord i)
    have key : ∀ i, ∃ x : F, ∃ f : G → F, Continuous f ∧
        ∀ g h, χ g * f h - f (g * h) + f g = b.coord i (z (g, h)) - x * z0 (g, h) := by
      intro i
      refine H (fun p => b.coord i (z p)) ((hb i).comp hc) (fun g h k => ?_)
      have := congrArg (b.coord i) (hz g h k)
      rw [← Algebra.smul_def, map_sub, map_add (f := _), map_sub, map_smul, map_zero, smul_eq_mul] at this
      exact this
    choose x f hf hxf using key
    refine ⟨∑ i, x i • b i, fun g => ∑ i, f i g • b i, ?_, fun g h => ?_⟩
    · exact continuous_finsetSum _ (fun i _ => (hf i).smul continuous_const)
    · have hs : z (g, h) = ∑ i, b.coord i (z (g, h)) • b i := by
        simp [b.sum_repr]
      rw [hs, ← Algebra.smul_def, mul_comm, ← Algebra.smul_def, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, smul_smul, ← sub_smul, ← add_smul, ← sub_smul, hxf i g h, mul_comm (x i)]

theorem span_cocycles_cyc_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  intro l _ P K LL _ _ _ O _ _ hO H
  obtain ⟨-, hfd, hmt, htr, -⟩ := hO
  obtain ⟨z0, hz0, H⟩ := H
  have := span_cocycles_ext (F := ℚ_[l]) (E := LL)
    (fun g : ↥(GK K) => ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])) ⟨z0, hz0, fun z hc hz => by
      obtain ⟨x, f, hf, hd⟩ := H z hc hz
      refine ⟨x, f, hf, fun g h => ?_⟩
      have := congrFun hd (g, h)
      simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using this⟩
  have e : ∀ g : ↥(GK K), algebraMap ℚ_[l] LL ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])
      = ((cycLL (P.PD K) LL g : LLˣ) : LL) := fun g => by simp [cycLL]
  simp only [e] at this
  obtain ⟨w0, hw0, H'⟩ := this
  refine ⟨w0, hw0, fun z hc hz => ?_⟩
  obtain ⟨x, f, hf, hd⟩ := H' z hc hz
  refine ⟨x, f, hf, ?_⟩
  funext ⟨g, h⟩
  simpa [ReciprocityTheory.Def.d1, Formalism.WeaklyAdmissibleFiltrations.charRep] using hd g h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanCyclotomicTwoCocyclesFiniteExtensionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  first | exact @GlobalTheory.span_cocycles_cyc_ext | exact GlobalTheory.span_cocycles_cyc_ext | (intros; apply GlobalTheory.span_cocycles_cyc_ext <;> assumption)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.InvLine

theorem spanQ : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0) := by
  intro hT l _ P K
  obtain ⟨hcpt, χ, c, hχc, hχ, hgen, hfin⟩ := GlobalTheory.T.exists_fundamentalTwoCocycle_of_localTateDuality hT l P K
  obtain ⟨⟨hcc, hcoc⟩, hsp⟩ := GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental l ↥(GK K) χ c hχc hgen hfin
  have hcyc : ∀ g, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) = ((χ g : ℤ_[l]) : ℚ_[l]) := fun g => by
    rw [hχ]; rfl
  refine ⟨fun p => (c p : ℚ_[l]), ⟨hcc, fun g h k => by rw [hcyc]; exact hcoc g h k⟩, fun z hz hzc => ?_⟩
  obtain ⟨x, f, hf, hfd⟩ := hsp z hz (fun g h k => by rw [← hcyc]; exact hzc g h k)
  refine ⟨x, f, hf, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have e := hfd g h
  rw [← hcyc] at e
  simp only [ReciprocityTheory.Def.d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← e]
  simp [charRep]

theorem exists_inv : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ (Z : Submodule LL (↥(GK K) × ↥(GK K) → LL)) (inv : ↥Z →ₗ[LL] LL), (∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) ∧ ∀ z : ↥Z, inv z = 0 ↔ CobL (P.PD K) z.1 := by
  intro hT l _ P K LL _ _ _ O _ _ hO
  obtain ⟨z0, ⟨hz0c, hz0⟩, hspan⟩ := GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension l P K LL O hO (spanQ hT l P K)
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let Z : Submodule LL (↥(GK K) × ↥(GK K) → LL) :=
    { carrier := {z | Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g h k => by
        have e1 := ha.2 g h k
        have e2 := hb.2 g h k
        simp only [Pi.add_apply]
        linear_combination e1 + e2⟩
      zero_mem' := ⟨continuous_const, fun g h k => by simp⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun g h k => by
        have e1 := ha.2 g h k
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination c * e1⟩ }
  have hZ : ∀ z, z ∈ Z ↔ Continuous z ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0 := fun z => Iff.rfl
  let B : Submodule LL ↥Z :=
    { carrier := {z | CobL (P.PD K) z.1}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨f1, hf1, e1⟩ := ha
        obtain ⟨f2, hf2, e2⟩ := hb
        exact ⟨f1 + f2, hf1.add hf2, by rw [map_add (f := _), e1, e2]; rfl⟩
      zero_mem' := ⟨0, continuous_const, by rw [map_zero]; rfl⟩
      smul_mem' := fun c a ha => by
        obtain ⟨f1, hf1, e1⟩ := ha
        exact ⟨c • f1, hf1.const_smul c, by rw [map_smul, e1]; rfl⟩ }
  have hB : ∀ z : ↥Z, z ∈ B ↔ CobL (P.PD K) z.1 := fun z => Iff.rfl
  let z0' : ↥Z := ⟨z0, hz0c, hz0⟩
  have hQ : ∀ z : ↥Z, ∃ x : LL, B.mkQ z = x • B.mkQ z0' := by
    intro z
    obtain ⟨x, hx⟩ := hspan z.1 z.2.1 z.2.2
    refine ⟨x, ?_⟩
    rw [← map_smul, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨Z, ?_⟩
  by_cases h0 : B.mkQ z0' = 0
  · refine ⟨0, hZ, fun z => ?_⟩
    obtain ⟨x, hx⟩ := hQ z
    rw [h0, smul_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    simp only [LinearMap.zero_apply, true_iff]
    exact hx
  · have htop : Submodule.span LL {B.mkQ z0'} = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨z, rfl⟩ := B.mkQ_surjective q
      obtain ⟨x, hx⟩ := hQ z
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    let φ := LinearEquiv.toSpanNonzeroSingleton LL _ _ h0
    let inv : ↥Z →ₗ[LL] LL :=
      (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap).comp B.mkQ
    have hinj : Function.Injective (φ.symm.toLinearMap.comp (LinearEquiv.ofTop _ htop).symm.toLinearMap) :=
      φ.symm.injective.comp (LinearEquiv.ofTop _ htop).symm.injective
    refine ⟨inv, hZ, fun z => ?_⟩
    have e1 : inv z = 0 ↔ B.mkQ z = 0 :=
      (injective_iff_map_eq_zero' _).1 hinj (B.mkQ z)
    rw [e1, ← hB, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end GlobalTheory.InvLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalTatePairingBilinear
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.PairLine

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]

theorem cont_form {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (f : V →ₗ[LL] LL) : Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

theorem cont_act {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (ρ : Representation LL G V)
    (hρ : ∀ x, Continuous fun g => ρ g x) : Continuous fun p : G × V => ρ p.1 p.2 := by
  haveI : ContinuousSMul LL V := IsModuleTopology.toContinuousSMul LL V
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let b := Module.finBasis LL V
  have h : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.repr p.2 i • ρ p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_snd).smul
    ((hρ (b i)).comp continuous_fst)

theorem cont_bil {V V' : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] [AddCommGroup V'] [Module LL V']
    [FiniteDimensional LL V'] [TopologicalSpace V'] [IsModuleTopology LL V']
    (m : V →ₗ[LL] V' →ₗ[LL] LL) : Continuous fun q : V × V' => m q.1 q.2 := by
  let b := Module.finBasis LL V
  have h : (fun q : V × V' => m q.1 q.2) = fun q => ∑ i, b.repr q.1 i * m (b i) q.2 := by
    funext q
    conv_lhs => rw [← b.sum_repr q.1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_fst).mul
    ((cont_form (m (b i))).comp continuous_snd)

end Cont

theorem exists_pair : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, ∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨Z, inv, hZ, hinv⟩ := GlobalTheory.InvLine.exists_inv hT l P K LL O hO
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hmem : ∀ (a : ↥(continuousCocycles A.ρ)) (b : ↥(continuousCocycles A'.ρ)), cupL A'.ρ m a.1 b.1 ∈ Z := by
    intro a b
    obtain ⟨ha, ha'⟩ : Continuous a.1 ∧ ∀ g h, a.1 (g * h) = a.1 g + A.ρ g (a.1 h) := a.2
    obtain ⟨hb, hb'⟩ : Continuous b.1 ∧ ∀ g h, b.1 (g * h) = b.1 g + A'.ρ g (b.1 h) := b.2
    rw [hZ]
    refine ⟨?_, fun g h k => ?_⟩
    · have h1 : Continuous fun p : ↥(GK K) × ↥(GK K) => A'.ρ p.1 (b.1 p.2) :=
        (cont_act A'.ρ A'.cont).comp (continuous_fst.prodMk (hb.comp continuous_snd))
      exact (cont_bil m).comp ((ha.comp continuous_fst).prodMk h1)
    · simp only [cupL]
      rw [← hm.1 g (a.1 h) (A'.ρ h (b.1 k)), ha', hb', map_mul, Module.End.mul_apply]
      simp only [map_add (f := _), LinearMap.add_apply]
      ring
  refine ⟨LinearMap.mk₂ LL (fun a b => inv ⟨cupL A'.ρ m a.1 b.1, hmem a b⟩) ?_ ?_ ?_ ?_,
    fun a b => ?_⟩
  · intro a a' b
    rw [← map_add (f := _)]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro a b b'
    rw [← map_add (f := _)]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · rw [LinearMap.mk₂_apply]
    exact hinv _

end GlobalTheory.PairLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalTatePairingBilinearStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_tatePairing_bilinear : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, ∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1) := by
  first | exact @GlobalTheory.PairLine.exists_pair | exact GlobalTheory.PairLine.exists_pair | (intros; apply GlobalTheory.PairLine.exists_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleMemCoboundariesOfTateOrthogonalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL (P.PD K) (cupL A'.ρ m a b)) → b ∈ B1 A'.ρ := by
  first | exact @GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' | exact GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' | (intros; apply GlobalTheory.TateOrthV.cocycle_mem_coboundaries_of_tate_orthogonal' <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundary
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

section General

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]
  {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [TopologicalSpace V'] [ContinuousAdd V']
  [ContinuousConstSMul LL V']

theorem cupAnti_cob_of_flip (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ continuousCocycles ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ')
    (h : ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ m.flip b a) :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨f, hf, hfe⟩ := h
  obtain ⟨hac, ha⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => -(m (a g) (b g)) - f g, ((hm.comp (hac.prodMk hbc)).neg).sub hf, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  have h1 := congrFun hfe (g, h)
  have h2 := hχ g (a h) (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    ha, hb, map_add, LinearMap.add_apply] at h1 ⊢
  linear_combination -h1 + h2

theorem cupAnti_cob_of_left (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ Formalism.WeaklyAdmissibleFiltrations.B1 ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ') :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => m x (b g), hm.comp (continuous_const.prodMk hbc), ?_⟩
  funext y
  obtain ⟨g, h⟩ := y
  have h2 := hχ g x (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, cob, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, LinearMap.pi_apply,
    hb, map_add, map_sub, LinearMap.sub_apply]
  linear_combination -h2

end General

theorem cupL_anticomm_cobL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m hm a ha b hb
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hc : Continuous fun p : A.V × A'.V => m p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m
  have hc' : Continuous fun p : A'.V × A.V => m.flip p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m.flip
  have hχ := hm.1
  have hχ' : ∀ g x y, m.flip (A'.ρ g x) (A.ρ g y) =
      ((cycLL (P.PD K) LL g : LLˣ) : LL) * m.flip x y := fun g x y => hχ g y x
  refine ⟨⟨fun h => cupAnti_cob_of_flip _ A'.ρ A.ρ m.flip hc' hχ' hb ha h,
    fun h => cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb h⟩, ?_⟩
  rintro (h | h)
  · exact cupAnti_cob_of_left _ A.ρ A'.ρ m hc hχ h hb
  · exact cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb
      (cupAnti_cob_of_left _ A'.ρ A.ρ m.flip hc' hχ' h ha)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundaryStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  first | exact @GlobalTheory.cupL_anticomm_cobL | exact GlobalTheory.cupL_anticomm_cobL | (intros; apply GlobalTheory.cupL_anticomm_cobL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocycles
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tateDuality_degreeOne_cocycles : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 A.ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_rational_tatePairing_bilinear hT l P K LL O hO A A' m hm
  have hflip : IsDual1 (P.PD K) A'.ρ A.ρ m.flip :=
    ⟨fun g x y => hm.1 g y x, hm.2.2.1, hm.2.1, hm.2.2.2.symm⟩
  have hanti := GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary l P K LL O hO A A' m hm
  refine ⟨β, hβ, fun a => ⟨fun h => ?_, fun ha b => ?_⟩, fun b => ⟨fun h => ?_, fun hb a => ?_⟩⟩
  · refine GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A' A m.flip hflip a.1 a.2 (fun b hb => ?_)
    exact ((hanti a.1 a.2 b hb).1).1 ((hβ a ⟨b, hb⟩).1 (h ⟨b, hb⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inl ha))
  · exact GlobalTheory.T.cocycle_mem_coboundaries_of_tate_orthogonal hT l P K LL O hO A A' m hm b.1 b.2
      (fun a ha => (hβ ⟨a, ha⟩ b).1 (h ⟨a, ha⟩))
  · exact (hβ a b).2 ((hanti a.1 a.2 b.1 b.2).2 (Or.inr hb))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocyclesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 A.ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 A'.ρ := by
  first | exact @GlobalTheory.tateDuality_degreeOne_cocycles | exact GlobalTheory.tateDuality_degreeOne_cocycles | (intros; apply GlobalTheory.tateDuality_degreeOne_cocycles <;> assumption)
end
