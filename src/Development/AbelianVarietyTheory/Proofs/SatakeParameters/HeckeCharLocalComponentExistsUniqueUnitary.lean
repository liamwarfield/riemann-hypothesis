module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
public import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeComp

theorem smooth_loc {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := by
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ w
  have hu := unif_spec w
  set c : w.adicCompletion E := ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ (n + 1) with hc
  have hv : Valued.v c = WithZero.exp (-((n : ℤ) + 1)) := by
    unfold IsUnifAt at hu
    rw [hc, map_pow, hu, ← WithZero.exp_nsmul]; congr 1; simp
  have ho : IsOpen {x : (w.adicCompletion E)ˣ | ((x : w.adicCompletion E) - 1) * c⁻¹ ∈ w.adicCompletionIntegers E} :=
    (Valued.isOpen_valuationSubring _).preimage ((Units.continuous_val.sub continuous_const).mul continuous_const)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  have h1 : Valued.v (((x : w.adicCompletion E) - 1) * c⁻¹) ≤ 1 := hx
  rw [map_mul, map_inv₀, hv, mul_inv_le_iff₀ WithZero.exp_pos, one_mul] at h1
  have h2 : Valued.v ((x : w.adicCompletion E) - 1) < 1 :=
    h1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  refine hn x ?_ (h1.trans (WithZero.exp_le_exp.2 (by omega)))
  have := Valuation.map_one_add_of_lt _ h2
  rwa [add_sub_cancel] at this

theorem eq_of_isComp {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {ξ ξ' : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : IsComp χ w ξ) (hξ' : IsComp χ w ξ') : ξ' = ξ := by
  have hs := hξ'.1.mul hξ.1.inv
  have hc := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 (MonoidHom.ext fun y => ?_)
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hc.isOpen_compl
  have hyU : (y : w.adicCompletion E) ∈ U := by
    have : y ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨y, hyU, y.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  show ξ' _ * (ξ _)⁻¹ = 1
  rw [hξ.2, hξ'.2]
  exact mul_inv_cancel _

theorem main : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  intro E _ _ χ w
  have hc : IsComp χ w (χ.loc w) := ⟨smooth_loc χ w, fun _ => rfl⟩
  exact ⟨χ.loc w, hc, fun ξ' h' => eq_of_isComp hc h', fun hu x => hu _⟩

end GlobalTheory.HeckeComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  first | exact @GlobalTheory.HeckeComp.main | exact GlobalTheory.HeckeComp.main | (intros; apply GlobalTheory.HeckeComp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.L2.Host GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver Dec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GalFirstClause

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem finextRep : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (a : ℕ) (r : G E Ω →* GL (Fin a) (Om l)), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) →
    ∃ (K : FinExt l) (ρ : G E Ω →* GL (Fin a) ↥K.1), Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥K.1)) ∧
      mapRep (algebraMap ↥K.1 (Om l)) ρ = r := by
  intro l _ E Ω _ _ _ _ _ a r hr
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a r hr (GlobalTheory.Pst.adjExt 0)
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : G E Ω → Matrix (Fin a) (Fin a) ↥L.1 := fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : G E Ω →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  refine ⟨L, ρ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_induced_rng.2 ((continuous_apply j).comp ((continuous_apply i).comp hr))
  · exact MonoidHom.ext fun g => Units.ext (hM g)

end GlobalTheory.GalFirstClause

open GlobalTheory

open scoped TensorProduct

namespace GlobalTheory.GalFirstClause.Emb

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

def tensLift (φ : E →+* Om l) : ℚ_[l] ⊗[ℚ] E →ₐ[ℚ_[l]] Om l :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (Om l)) φ.toRatAlgHom (fun _ _ => Commute.all _ _)

theorem tensLift_tmul (φ : E →+* Om l) (a : ℚ_[l]) (y : E) :
    tensLift φ (a ⊗ₜ y) = algebraMap ℚ_[l] (Om l) a * φ y := by
  simp [tensLift]

theorem exists_approx (φ ψ : E →+* Om l) (t : ℚ_[l] ⊗[ℚ] E) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖tensLift φ t - φ x‖ < ε ∧ ‖tensLift ψ t - ψ x‖ < ε := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    intro ε hε
    have hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1 := by positivity
    obtain ⟨q, hq⟩ := Padic.rat_dense l a (div_pos hε hM)
    refine ⟨(q : E) * y, ?_, ?_⟩
    · rw [tensLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖φ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (ψ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
    · rw [tensLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖ψ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (φ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
  | add t₁ t₂ h₁ h₂ =>
    intro ε hε
    obtain ⟨x₁, a₁, b₁⟩ := h₁ (ε / 2) (half_pos hε)
    obtain ⟨x₂, a₂, b₂⟩ := h₂ (ε / 2) (half_pos hε)
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · have e : tensLift φ (t₁ + t₂) - φ (x₁ + x₂) = (tensLift φ t₁ - φ x₁) + (tensLift φ t₂ - φ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (tensLift φ t₁ - φ x₁) (tensLift φ t₂ - φ x₂)]
    · have e : tensLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (tensLift ψ t₁ - ψ x₁) + (tensLift ψ t₂ - ψ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (tensLift ψ t₁ - ψ x₁) (tensLift ψ t₂ - ψ x₂)]

theorem norm_tensLift_le (φ ψ : E →+* Om l) (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (t : ℚ_[l] ⊗[ℚ] E) :
    ‖tensLift ψ t‖ ≤ ‖tensLift φ t‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, h₁, h₂⟩ := exists_approx φ ψ t (ε / 2) (half_pos hε)
  have e1 : ‖tensLift ψ t‖ ≤ ‖tensLift ψ t - ψ x‖ + ‖ψ x‖ := by
    simpa using norm_add_le (tensLift ψ t - ψ x) (ψ x)
  have e2 : ‖φ x‖ ≤ ‖φ x - tensLift φ t‖ + ‖tensLift φ t‖ := by
    simpa using norm_add_le (φ x - tensLift φ t) (tensLift φ t)
  rw [norm_sub_rev] at e2
  rw [← h x] at e1
  linarith

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause.Emb

open scoped TensorProduct

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

theorem norm_eq_of_samePlace (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ = ‖φ x‖ := by
  have e1 := PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)
  have e2 := PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (e1.symm.trans e2)
  have hl := congrFun hce ((l : ℕ) : E)
  simp only [PI.CompDegEF.normAbv_apply, map_natCast] at hl
  have hpos := PI.CompDegEF.norm_natCast_pos l
  have hlt := PI.CompDegEF.norm_natCast_lt_one l
  have hL : Real.log ‖((l : ℕ) : Om l)‖ ≠ 0 := (Real.log_neg hpos hlt).ne
  have hc1 : c = 1 := by
    have := congrArg Real.log hl
    rw [Real.log_rpow hpos] at this
    exact (mul_eq_right₀ hL).1 this
  have hx := congrFun hce x
  simp only [PI.CompDegEF.normAbv_apply, hc1, Real.rpow_one] at hx
  exact hx

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause.Emb

open scoped TensorProduct

theorem exists_isInduced : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (τ : E →+* Om l), ∃ w ∈ placesOver E l, ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
        Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  intro l _ E Ω _ _ _ _ _ τ
  refine ⟨PI.CompDegEF.plOf τ, PI.CompDegEF.natCast_mem_plIdeal τ, ?_⟩
  intro A hA O _ _ _ Bw hj
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hw := hj.mem_placesOver hA
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ (PI.CompDegEF.plOf τ).asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := norm_eq_of_samePlace τ jE _ hw (fun x => Iff.rfl) hjE
  have hker : ∀ t ∈ RingHom.ker (tensLift jE), tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change tensLift jE (a ⊗ₜ y) ∈ _
      rw [tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((tensLift jE).range : Set (Om l)) :=
    Submodule.isClosed_of_finiteDimensional (Subalgebra.toSubmodule (tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by change tensLift jE (1 ⊗ₜ x) = jE x; rw [tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (tensLift jE)) (tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = tensLift jE (1 ⊗ₜ x)
    rw [tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (tensLift τ) hker ((Ideal.quotientKerEquivRange (tensLift jE)).symm
    (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = tensLift τ (1 ⊗ₜ x)
  rw [tensLift_tmul, map_one, one_mul]

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst

theorem existsIsInduced : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (τ : E →+* Om l), ∃ w ∈ placesOver E l, ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
        Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' :=
  Emb.exists_isInduced

end GlobalTheory.GalFirstClause
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ProdFiniteLength

open GlobalTheory.SmGL

theorem piTensor_mulSingle_eq_map {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (a : α)
    (g : Γ a) :
    piTensor ρ (Pi.mulSingle a g) =
      PiTensorProduct.map (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) a (ρ a g)) := by
  apply PiTensorProduct.ext
  ext x
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, PiTensorProduct.map_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

theorem exists_mem_adjoin_eq {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible)
    (hS : ∀ φ : V →ₗ[ℂ] V, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id)
    (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ T ∈ Algebra.adjoin ℂ (Set.range π), ∀ x ∈ s, T x = f x := by
  classical
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range π)
  have hmem : ∀ g, π g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  haveI : IsSimpleOrder (Subrepresentation π) := hirr
  haveI : IsSimpleModule A V := by
    rw [isSimpleModule_iff]
    refine { exists_pair_ne := ?_, eq_bot_or_eq_top := fun U => ?_ }
    · obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by
        by_contra h
        push_neg at h
        apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
        ext v
        simp [h v]
      refine ⟨⊥, ⊤, fun h => hx ?_⟩
      have : x ∈ (⊤ : Submodule A V) := trivial
      rw [← h] at this
      exact (Submodule.mem_bot A).1 this
    · let W : Subrepresentation π :=
        { toSubmodule := U.restrictScalars ℂ
          apply_mem_toSubmodule := fun g v hv => U.smul_mem (⟨π g, hmem g⟩ : A) hv }
      rcases IsSimpleOrder.eq_bot_or_eq_top W with h | h
      · left
        ext v
        constructor
        · intro hv
          have : v ∈ W.toSubmodule := hv
          rw [h] at this
          exact (Submodule.mem_bot A).2 this
        · intro hv
          rw [(Submodule.mem_bot A).1 hv]
          exact U.zero_mem
      · right
        refine eq_top_iff.2 fun v _ => ?_
        have : v ∈ (⊤ : Subrepresentation π).toSubmodule := trivial
        rw [← h] at this
        exact this
  have hscal : ∀ φ : Module.End A V, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := hS (φ.restrictScalars ℂ) fun g x => φ.map_smul (⟨π g, hmem g⟩ : A) x
    exact ⟨c, fun m => by simpa using LinearMap.congr_fun hc m⟩
  let F : Module.End (Module.End A V) V :=
    { toFun := fun m => f m
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun x hx => (hr x hx).symm⟩

theorem piTensor_isIrreducible_of_schur {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hirr : ∀ a, (ρ a).IsIrreducible)
    (hS : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id) :
    (piTensor ρ).IsIrreducible := by
  classical
  cases nonempty_fintype α
  have hnt : ∀ a, Nontrivial (X a) := fun a => by
    haveI : IsSimpleOrder (Subrepresentation (ρ a)) := hirr a
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
    ext v
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim v 0⟩
  haveI : ∀ a, Nontrivial (X a) := hnt
  haveI : Nontrivial (PiTensorProduct ℂ fun a => X a) := GlobalTheory.ProdSupport.nontrivial_piTensor X hnt
  have hcomp : ∀ (f g : ∀ a, X a →ₗ[ℂ] X a) (x : PiTensorProduct ℂ fun a => X a),
      PiTensorProduct.map (fun a => f a ∘ₗ g a) x =
        PiTensorProduct.map f (PiTensorProduct.map g x) := by
    intro f g x
    rw [PiTensorProduct.map_comp]; rfl
  show IsSimpleOrder (Subrepresentation (piTensor ρ))
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · obtain ⟨x, hx⟩ := exists_ne (0 : PiTensorProduct ℂ fun a => X a)
    have : x ∈ (⊤ : Subrepresentation (piTensor ρ)).toSubmodule := trivial
    rw [← h] at this
    exact hx this
  by_cases hU : ∀ x ∈ U.toSubmodule, x = 0
  · left
    ext v
    refine ⟨hU v, fun h => ?_⟩
    rw [show v = 0 from h]
    exact U.toSubmodule.zero_mem
  push_neg at hU
  obtain ⟨x, hxU, hx0⟩ := hU
  right
  let Asub : ∀ a, Subalgebra ℂ (Module.End ℂ (X a)) := fun i =>
    { carrier := {T | ∀ x ∈ U.toSubmodule,
        PiTensorProduct.map (Function.update (fun b => (LinearMap.id : X b →ₗ[ℂ] X b)) i T) x ∈ U.toSubmodule}
      mul_mem' := fun {a b} ha hb x hx => by
        have := ha _ (hb x hx)
        rw [← hcomp] at this
        convert this using 3
        funext ρ
        by_cases hρ : ρ = i
        · subst hρ; simp [Module.End.mul_eq_comp]
        · simp [Function.update_of_ne hρ]
      add_mem' := fun {a b} ha hb x hx => by
        rw [PiTensorProduct.map_update_add]
        exact U.toSubmodule.add_mem (ha x hx) (hb x hx)
      algebraMap_mem' := fun c x hx => by
        rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul]
        have : Function.update (fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ)) i (1 : Module.End ℂ (X i)) =
            fun ρ => (LinearMap.id : X ρ →ₗ[ℂ] X ρ) := Function.update_eq_self i _
        rw [this, PiTensorProduct.map_id]
        exact U.toSubmodule.smul_mem c hx }
  have hA : ∀ a, Algebra.adjoin ℂ (Set.range (ρ a)) ≤ Asub a := fun a =>
    Algebra.adjoin_le (by
      rintro _ ⟨g, rfl⟩ y hy
      rw [← piTensor_mulSingle_eq_map]
      exact U.apply_mem_toSubmodule _ hy)
  have h3 : ∀ T : ∀ a, Module.End ℂ (X a), (∀ a, T a ∈ Asub a) →
      ∀ y ∈ U.toSubmodule, PiTensorProduct.map T y ∈ U.toSubmodule := by
    intro T hT
    have h2 : ∀ s : Finset α, ∀ y ∈ U.toSubmodule,
        PiTensorProduct.map (fun a => if a ∈ s then T a else LinearMap.id) y ∈ U.toSubmodule := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro y hy; simpa using hy
      | insert j s hj ih =>
        intro y hy
        have := hT j _ (ih y hy)
        rw [← hcomp] at this
        convert this using 3
        funext b
        by_cases hb : b = j
        · subst hb; simp [hj]
        · simp [hb]
    intro y hy
    simpa using h2 Finset.univ y hy
  have htop : U.toSubmodule = ⊤ := by
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    let b := fun a => Module.Free.chooseBasis ℂ (X a)
    let B := Basis.piTensorProduct b
    obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
    let f : ∀ a, Module.End ℂ (X a) := fun a => ((b a).coord (p a)).smulRight (v a)
    have hT : ∀ a, ∃ T ∈ Asub a, ∀ y ∈ (B.repr x).support.image (fun q => b a (q a)), T y = f a y :=
      fun a => by
        obtain ⟨T, hT1, hT2⟩ := exists_mem_adjoin_eq (ρ a) (hirr a) (hS a) (f a)
          ((B.repr x).support.image (fun q => b a (q a)))
        exact ⟨T, hA a hT1, hT2⟩
    choose T hTA hTf using hT
    have e : PiTensorProduct.map f = (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext w
      simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
        Module.Basis.coord_apply, B, f, Basis.piTensorProduct_repr_tprod_apply]
      exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
    have hmap : PiTensorProduct.map T x = PiTensorProduct.map f x := by
      rw [← B.linearCombination_repr x, Finsupp.linearCombination_apply, map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr fun q hq => ?_
      rw [map_smul, map_smul, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod]
      congr 2
      funext a
      exact hTf a _ (Finset.mem_image_of_mem _ hq)
    have h4 := h3 T hTA x hxU
    rw [hmap, e] at h4
    exact (U.toSubmodule.smul_mem_iff hp).1 h4
  ext y
  exact ⟨fun _ => trivial, fun _ => by rw [htop]; trivial⟩

theorem multiProd_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ)
    (σ : ∀ a, Irr k (d a)) (e : (Σ a, Fin (d a)) ≃ Fin n),
    HasFiniteLength (multiProd e fun a => (σ a).π) := by
  intro hBZ k _ _ _ _ s n d σ e
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    piTensor_isIrreducible_of_schur (fun a => (σ a).π) (fun a => (σ a).irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible (GL (Fin (d a)) k) (KO k (Fin (d a))) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (σ a).V (σ a).π (σ a).irr
        (hAdm (Fin (d a)) (σ a).V (σ a).π (σ a).smooth (σ a).irr) φ hφ
  exact hInd (Fin s) (Fin n) (fun a => Fin (d a)) e _ _ (isSmooth_piTensor fun a => (σ a).smooth)
    (hasFiniteLength_of_isIrreducible hirr)

end GlobalTheory.ProdFiniteLength
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLengthStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionTensorProduct_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (e : (Σ a, Fin (d a)) ≃ Fin n), HasFiniteLength (multiProd e fun a => (σ a).π) := by
  first | exact @GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength | exact GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength | (intros; apply GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCGal

open Formalism.MainNotions.SumRepresentations.At GlobalTheory.TwistLG

section Rep

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a b : ℕ}

theorem sumRep_val (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] [IsTopologicalRing k]
    (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k)
    (c : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (c' : Continuous fun g => ((ρ' g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  simp only [sumRep_val]
  exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _

theorem ss_sumRep (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (h : IsSSRep ρ) (h' : IsSSRep ρ') :
    IsSSRep (sumRep ρ ρ') := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h h'
  rw [sumRep_val]
  ext i <;>
    simp [Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft]
  all_goals rfl

theorem ss_zero (ρ : Γ →* GL (Fin 0) k) : IsSSRep ρ := fun W _ =>
  ⟨⊥, fun g v hv => by simp [Subsingleton.elim v 0], by rw [Subsingleton.elim W ⊤]; exact isCompl_top_bot⟩

end Rep

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eq_lpZero {w : PlE H} (x : A.LP w) (hu : A.unr x) (hd : A.lpDim x = 0) : x = A.lpZero w := by
  have h1 : A.frobEig x = 0 := Multiset.card_eq_zero.1 (by rw [A.frobEig_card _ hu, hd])
  have h2 := A.unr_eq_lpUnr _ (A.lpZero_unr w)
  rw [A.frobEig_zero] at h2
  rw [A.unr_eq_lpUnr _ hu, h1, h2]

theorem lpTw_lpZero (w : PlE H) (c : ℝ) : A.lpTw (A.lpZero w) c = A.lpZero w :=
  eq_lpZero N A _ ((A.unr_tw _ _).2 (A.lpZero_unr w)) (by rw [A.lpDim_tw, A.lpDim_zero])

theorem param_int (hLP : TieLP N A) {a : ℕ} (π : A.CG a) (w : PlE H) (u t : ℝ) :
    A.lpChar (A.lpChar (A.lpTw (A.locG π w) u) (A.lpTw (A.locG A.etaT w) (1 / 2)))
      (A.lpTw (A.locG A.etaTinv w) (t - 1 / 2)) = A.lpTw (A.locG π w) (u + t) := by
  have d1 : A.lpDim (A.locG A.etaT w) = 1 := A.locG_dim _ w
  have d2 : A.lpDim (A.locG A.etaTinv w) = 1 := A.locG_dim _ w
  set X := A.lpTw (A.locG π w) u
  have c3a := (hLP w (A.lpChar X (A.lpTw (A.locG A.etaT w) (1 / 2))) (A.lpZero w) (A.locG A.etaTinv w)
    (A.locG A.etaTinv w) (t - 1 / 2) d2 d2).2.2.1
  have c3b := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaT w) (1 / 2) d1 d1).2.2.1
  have c2 := (hLP w (A.lpChar X (A.locG A.etaT w)) (A.lpZero w) (A.locG A.etaTinv w) (A.locG A.etaTinv w)
    (1 / 2) d2 d2).2.1
  have c4 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.1
  have c5 := (hLP w X (A.lpZero w) (A.locG A.etaT w) (A.locG A.etaTinv w) 0 d1 d2).2.2.2.2.1
  rw [c3a, c3b, c2, c4, etaT_char_etaTinv N A w, c5, A.lpTw_add, A.lpTw_add]
  congr 1
  ring

end Glob

section Piece

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem eta_alg (hAut : TieAut N A) (m : ℤ) (τ : H.E →+* ℂ) :
    (∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) ∧
    (∀ z ∈ A.infG A.etaTinv τ, ∃ k : ℤ, z + (((m : ℝ) + 1 / 2 : ℝ) : ℂ) = (k : ℂ)) := by
  obtain ⟨h1, h2⟩ := hAut.2.1 τ
  rw [h2]
  rcases h1 with h1 | h1 <;> rw [h1] <;> refine ⟨fun z hz => ?_, fun z hz => ?_⟩ <;>
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz <;> subst hz
  · exact ⟨m + 1, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m, by push_cast; ring⟩
  · exact ⟨m + 1, by push_cast; ring⟩

end Piece

section List

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end List

end GlobalTheory.BCGal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.DeRhamRead
open Formalism.BasicNotions.Loc

theorem exists_model_of_mem {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ}
    (r : Γ →* GL (Fin a) (Om l)) (hr : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l)))) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  refine ⟨ρ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_induced_rng.2 ((continuous_apply j).comp ((continuous_apply i).comp hr))
  · exact MonoidHom.ext fun g => Units.ext (hM g)

theorem isdRW_iff_isdRAt : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  intro D T W l _ ι w hw O _ _ _ B hj a r hr
  obtain ⟨LL', hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G D.host.E D.nd.Om) a r hr B.LL
  obtain ⟨r₁, c₁, rfl⟩ := exists_model_of_mem r hr LL' hmem
  obtain ⟨-, H⟩ := W.loc l ι w hw _ B hj ((algebraMap ↥B.LL.1 (Om l)).comp B.toLL) (fun _ => rfl)
  have hm : GlobalTheory.Pst.IsModel B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) LL'
      (r₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL, rfl⟩
  exact (H LL' hL a r₁ c₁).2.1.trans (hm.isdRAt_iff (D.loc l)).symm

end GlobalTheory.DeRhamRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_galoisSide_iff_deRham_at_localEmbedding : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → (W.IsdRW l ι r w ↔ GlobalTheory.Pst.IsdRAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 r w)) := by
  first | exact @GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | exact GlobalTheory.DeRhamRead.isdRW_iff_isdRAt | (intros; apply GlobalTheory.DeRhamRead.isdRW_iff_isdRAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceOver

theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem eq_or_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v →
    s.w = w ∨ IsConjPl D.host w s.w := by
  intro D s w hov
  let cO := IsCMField.ringOfIntegersComplexConj D.host.E
  have cc (x : 𝓞 D.host.E) : cO (cO x) = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
    exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)
  let Q : PlE D.host := {
    asIdeal := s.w.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
    isPrime := Ideal.comap_isPrime _ _
    ne_bot := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.w.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
      · show (cO : 𝓞 D.host.E →+* 𝓞 D.host.E) (cO y) ∈ s.w.asIdeal
        rw [RingHom.coe_coe, cc]; exact hy
      · intro h0
        apply hy0
        rw [← cc y, h0, map_zero] }
  have hQ (x : 𝓞 D.host.E) : x ∈ Q.asIdeal ↔ cO x ∈ s.w.asIdeal := Iff.rfl
  have he : w = s.w ∨ w = Q := by
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2⟩ := hne
    have nle : ∀ P : PlE D.host, w ≠ P → ¬ w.asIdeal ≤ P.asIdeal := fun P h hle =>
      h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top hle))
    obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle s.w h1)
    obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q h2)
    have key : ∃ x ∈ w.asIdeal, x ∉ s.w.asIdeal ∧ x ∉ Q.asIdeal := by
      by_cases haQ : a ∈ Q.asIdeal
      · by_cases hbP : b ∈ s.w.asIdeal
        · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
          · simpa using s.w.asIdeal.sub_mem h hbP
          · simpa using Q.asIdeal.sub_mem h haQ
        · exact ⟨b, hb, hbP, hbQ⟩
      · exact ⟨a, ha, haP, haQ⟩
    obtain ⟨x, hx, hxP, hxQ⟩ := key
    rw [hQ] at hxQ
    have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, cc, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
    rw [hov.trans s.w_under.symm, Ideal.mem_comap, hy] at hyw
    rcases s.w.isPrime.mem_or_mem hyw with h | h
    · exact hxP h
    · exact hxQ h
  rcases he with e | e
  · exact Or.inl e.symm
  · right
    intro x y hxy
    have hy : y = cO x := by
      apply RingOfIntegers.ext
      rw [hxy, IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
    rw [e, hQ, hy]

end GlobalTheory.SplitPlaceOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v → s.w = w ∨ IsConjPl D.host w s.w := by
  first | exact @GlobalTheory.SplitPlaceOver.eq_or_isConjPl | exact GlobalTheory.SplitPlaceOver.eq_or_isConjPl | (intros; apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwistBridgeDR

open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.TwistAbove

theorem twGL_eq {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (r : Γ →* GL (Fin a) K) (μ : Γ →* Kˣ) :
    Formalism.MainNotions.SumRepresentations.At.twGL r μ = GlobalTheory.TwistAbove.twGL μ r := by
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, GlobalTheory.TwistAbove.twGL, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

theorem characterAsRankOneRep_det_comp {Γ K : Type} [Group Γ] [CommRing K] (c : Γ →* GL (Fin 1) K) :
    GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c) = c := by
  ext g i j
  fin_cases i; fin_cases j
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem repE_twGL' {L : FinExt l} (χ : ↥Gw →* (↥L.1)ˣ) (s : ↥Gw →* GL (Fin a) ↥L.1)
    (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (GlobalTheory.TwistAbove.twGL χ s) g x = ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L s g x := by
  change Matrix.toLin' ((GlobalTheory.TwistAbove.twGL χ s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((χ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((s (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [GlobalTheory.TwistAbove.twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem isModel_untwist {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)}
    {t : ↥Gw →* GL (Fin a) ↥L.1} {cc : ↥Gw →* GL (Fin 1) ↥L.1}
    (mt : IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L t)
    (mc : IsModel Bw c L cc) : IsModel Bw r L (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) := by
  refine ⟨mt.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) mt.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) mc.2
  rw [twGL_eq] at e1
  simp only [mapRep] at e1 e2 ⊢
  simp [Matrix.det_unique] at e1 e2 ⊢
  have hne : ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det (c g)).ne_zero
    simpa [Matrix.det_unique] using this
  rw [e1, e2, inv_mul_cancel_left₀ hne]

theorem isdRAt_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₂, c₂, m₂, d₂⟩ := hc
  constructor
  · rintro ⟨L₁, t₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mt := m₁.enlarge l₁
    have mc := m₂.enlarge l₂
    have dt := (local_ext P Bw l₁ t₁).2.1.2 d₁
    have dc := (local_ext P Bw l₂ c₂).2.1.2 d₂
    set t := mapRep (IntermediateField.inclusion l₁).toRingHom t₁
    set cc := mapRep (IntermediateField.inclusion l₂).toRingHom c₂
    refine ⟨_, _, isModel_untwist Bw mt mc, ?_⟩
    have hν := repE_rank_one Bw cc
    have hρ : ∀ g x, Bw.repE (supExt L₁ L₂) t g x =
        ((chr cc (Bw.e.symm g) : (↥(supExt L₁ L₂).1)ˣ) : ↥(supExt L₁ L₂).1) •
          Bw.repE (supExt L₁ L₂) (GlobalTheory.TwistAbove.twGL (chr cc)⁻¹ t) g x := by
      intro g x
      rw [repE_twGL', smul_smul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_smul]
    rw [← isDR_iff] at dt dc ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw (supExt L₁ L₂) (Fin a → ↥(supExt L₁ L₂).1)
      _ _ _ _ hν hρ dc).2 dt
  · rintro ⟨L₁, r₁, m₁, d₁⟩
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have mc : IsModel Bw (GlobalTheory.TripleGal.rk1 (Matrix.GeneralLinearGroup.det.comp c)) (supExt L₁ L₂)
        (mapRep (IntermediateField.inclusion l₂).toRingHom c₂) := by
      rw [characterAsRankOneRep_det_comp]; exact m₂.enlarge l₂
    refine ⟨_, _, isModel_twGL Bw (r' := Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c))
      (μ := Matrix.GeneralLinearGroup.det.comp c) (fun g => by rw [twGL_eq]; exact GlobalTheory.TwistAbove.twGL_val _ _ _)
      (m₁.enlarge l₁) mc, (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁)
        ((local_ext P Bw l₂ c₂).2.1.2 d₂)⟩

end GlobalTheory.TwistBridgeDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_characterTwist_iff_localEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Loc.Om l)) (c : ↥Gw →* GL (Fin 1) (Loc.Om l)), Continuous (fun g => ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → Continuous (fun g => ((c g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l))) → GlobalTheory.Pst.IsdRAt P Bw c → (GlobalTheory.Pst.IsdRAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) ↔ GlobalTheory.Pst.IsdRAt P Bw r) := by
  first | exact @GlobalTheory.TwistBridgeDR.isdRAt_twist_iff | exact GlobalTheory.TwistBridgeDR.isdRAt_twist_iff | (intros; apply GlobalTheory.TwistBridgeDR.isdRAt_twist_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
open NumberField IsDedekindDomain ReciprocityTheory.Aut

namespace GlobalTheory.TypeTame

noncomputable abbrev conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) : SplitPlace L :=
  ⟨s.v, s.i.comp (IsCMField.complexConj L).toAlgHom⟩

theorem conjSP_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (x : L) :
    (conjSP s).i x = s.i (IsCMField.complexConj L x) := rfl

end GlobalTheory.TypeTame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntInertOfComplexMultiplicationCondition
namespace GlobalTheory

theorem intInert_of_complexMultiplication_condition : Formalism.L2.Th1.CM.CM2 → Formalism.L2.KerInert.IntInert :=
  fun h => by
    haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
    exact Formalism.L2.KerInert.kernels_integral_inert

end GlobalTheory
end
