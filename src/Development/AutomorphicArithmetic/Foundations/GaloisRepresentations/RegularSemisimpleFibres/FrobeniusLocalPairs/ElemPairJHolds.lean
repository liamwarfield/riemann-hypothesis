module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPair
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchOfSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField

@[expose] public section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree Module.Free.of_divisionRing

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflTrace
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.GlobOf
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private lemma galOf_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (a b : E ≃ₐ[F] E) (y : B) :
    PositivityTheory.Rg.Tf.Geo.galOf e (a * b) y = PositivityTheory.Rg.Tf.Geo.galOf e a (PositivityTheory.Rg.Tf.Geo.galOf e b y) := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((a * b : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z =
        Algebra.TensorProduct.map (a : E →ₐ[F] E) (AlgHom.id F A)
          (Algebra.TensorProduct.map (b : E →ₐ[F] E) (AlgHom.id F A) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add (f := _), hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (y : B) : PositivityTheory.Rg.Tf.Geo.galOf e (1 : E ≃ₐ[F] E) y = y := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add (f := _), hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galFin_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a b : E ≃ₐ[F] E) (v : Pl F) (y : CompletionsOver E v) :
    galFin (a * b) v y = galFin a v (galFin b v y) := galOf_mul' _ a b y

private lemma galFin_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) (y : CompletionsOver E v) : galFin (1 : E ≃ₐ[F] E) v y = y := galOf_one' _ y

theorem globOf : GlobOf := by
  intro F E _ _ _ _ _ _ hp v w hw
  have hs := sum_finrank_eq E v
  rw [Fintype.sum_eq_single w (fun w' h => (h (hw w')).elim)] at hs
  intro alg hcomp
  have hdeg : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1)
      = Module.finrank F E := by
    convert hs using 2
    congr 1
    first
    | exact Algebra.algebra_ext _ _ (fun x => (hcomp x).symm)
    | exact Algebra.algebra_ext _ _ (fun x => hcomp x)
  have hp2 := hp.two_le
  haveI : FiniteDimensional (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) :=
    Module.finite_of_finrank_pos (by omega)
  let ψ : CompletionsOver E v ≃+* HeightOneSpectrum.adicCompletion E w.1 :=
    RingEquiv.ofBijective (Pi.evalRingHom (fun w' : PlacesOver E v => HeightOneSpectrum.adicCompletion E w'.1) w)
      ⟨fun y₁ y₂ h => funext fun w' => by
          obtain rfl := hw w'
          exact h,
        fun z => ⟨fun w' => by
          rw [hw w']
          exact z, rfl⟩⟩
  have hx : ∀ (σ : Gal(E/F)) (x : E),
      galFin σ v (algebraMap E (CompletionsOver E v) x) = algebraMap E (CompletionsOver E v) (σ x) := by
    intro σ x
    have e1 : ∀ z : E, algebraMap E (CompletionsOver E v) z =
        tensorEquiv' E v (z ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v)) := by
      intro z
      rw [tensorEquiv'_tmul, map_one, mul_one]
    rw [e1, e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v (x ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v))))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have halg : ∀ (σ : Gal(E/F)) (r : HeightOneSpectrum.adicCompletion F v),
      galFin σ v (algebraMap _ (CompletionsOver E v) r) = algebraMap _ (CompletionsOver E v) r := by
    intro σ r
    have e1 : algebraMap _ (CompletionsOver E v) r = tensorEquiv' E v ((1 : E) ⊗ₜ[F] r) := by
      rw [tensorEquiv'_tmul, map_one, one_mul]
    rw [e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 : E) ⊗ₜ[F] r)))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hψalg : ∀ r : HeightOneSpectrum.adicCompletion F v,
      ψ.symm (algebraMap _ (HeightOneSpectrum.adicCompletion E w.1) r) = algebraMap _ (CompletionsOver E v) r := by
    intro r
    apply ψ.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hcomp r).symm
  let φ : Gal(E/F) →* Gal(HeightOneSpectrum.adicCompletion E w.1/HeightOneSpectrum.adicCompletion F v) :=
    { toFun := fun σ =>
        { toFun := fun z => ψ (galFin σ v (ψ.symm z))
          invFun := fun z => ψ (galFin σ⁻¹ v (ψ.symm z))
          left_inv := fun z => by
            show ψ (galFin σ⁻¹ v (ψ.symm (ψ (galFin σ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', inv_mul_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          right_inv := fun z => by
            show ψ (galFin σ v (ψ.symm (ψ (galFin σ⁻¹ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', mul_inv_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          map_mul' := fun a b => by simp only [map_mul]
          map_add' := fun a b => by simp only [map_add (f := _)]
          commutes' := fun r => by
            show ψ (galFin σ v (ψ.symm (algebraMap _ _ r))) = _
            rw [hψalg, halg]
            exact hcomp r }
      map_one' := by
        apply AlgEquiv.ext
        intro z
        show ψ (galFin 1 v (ψ.symm z)) = z
        rw [galFin_one', RingEquiv.apply_symm_apply]
      map_mul' := by
        intro a b
        apply AlgEquiv.ext
        intro z
        show ψ (galFin (a * b) v (ψ.symm z)) = ψ (galFin a v (ψ.symm (ψ (galFin b v (ψ.symm z)))))
        rw [RingEquiv.symm_apply_apply, galFin_mul'] }
  haveI : Nontrivial (CompletionsOver E v) := ψ.toEquiv.nontrivial
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply AlgEquiv.ext
    intro x
    have h1 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) x) := by
      rw [hσ]
      rfl
    have h2 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) (σ x)) := by
      show ψ (galFin σ v (ψ.symm (ψ _))) = _
      rw [RingEquiv.symm_apply_apply, hx]
    exact (algebraMap E (CompletionsOver E v)).injective (ψ.injective (h2.symm.trans h1))
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) ?_⟩
    have c1 := AlgEquiv.card_le (F := HeightOneSpectrum.adicCompletion F v)
      (K := HeightOneSpectrum.adicCompletion E w.1)
    have c2 := IsGalois.card_aut_eq_finrank F E
    simp only [Fintype.card_eq_nat_card] at c1 c2 ⊢
    omega
  refine ⟨?_, hdeg, ?_⟩
  · intro hsplit
    have h1 : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) = 1 := by
      rw [finrank_eq_one_iff_of_nonzero' (1 : HeightOneSpectrum.adicCompletion E w.1) one_ne_zero]
      intro z
      obtain ⟨c, hc⟩ := hsplit w z
      exact ⟨c, by rw [Algebra.smul_def, mul_one, ← hcomp, hc]⟩
    omega
  · intro s hs
    obtain ⟨σ, hσ⟩ := hbij.2 s
    refine ⟨σ, ?_, ?_⟩
    · intro τ
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hs (φ τ))
      refine Subgroup.mem_zpowers_iff.2 ⟨n, hinj ?_⟩
      rw [map_zpow, hσ, hn]
    · intro y
      rw [← hσ]
      show _ = ψ (galFin σ v (ψ.symm (ψ y)))
      rw [RingEquiv.symm_apply_apply]
      rfl

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TraceRangeEq
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem trace_range_eq {V : Type} [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] V)
    (F : Submodule ℂ V) [FiniteDimensional ℂ F] (h : ∀ x, T x ∈ F) :
    LinearMap.trace ℂ (LinearMap.range T)
      (T.restrict (p := LinearMap.range T) (q := LinearMap.range T)
        fun v _ => LinearMap.mem_range_self T v) =
      LinearMap.trace ℂ F (T.restrict (p := F) (q := F) fun v _ => h v) := by
  have hRF : LinearMap.range T ≤ F := by
    rintro _ ⟨x, rfl⟩
    exact h x
  haveI : FiniteDimensional ℂ (LinearMap.range T) :=
    FiniteDimensional.of_injective (Submodule.inclusion hRF) (Submodule.inclusion_injective hRF)
  let ι : LinearMap.range T →ₗ[ℂ] F := Submodule.inclusion hRF
  let π : F →ₗ[ℂ] LinearMap.range T := T.rangeRestrict ∘ₗ F.subtype
  have e1 : (T.restrict (p := LinearMap.range T) (q := LinearMap.range T)
      fun v _ => LinearMap.mem_range_self T v) = π ∘ₗ ι := by
    ext x
    rfl
  have e2 : (T.restrict (p := F) (q := F) fun v _ => h v) = ι ∘ₗ π := by
    ext x
    rfl
  rw [e1, e2]
  exact LinearMap.trace_comp_comm' ι π

private theorem op_mem_fixed {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup V] [Module ℂ V] (μ : Measure G)
    [μ.IsMulLeftInvariant] (ρ : Representation ℂ G V) (U : Subgroup G) (f : G → ℂ)
    (hf : ∀ k ∈ U, ∀ x, f (k * x) = f x) (B : V →ₗ[ℂ] V) (hB : IsIntegralOp μ ρ f B) (v : V) :
    B v ∈ fixed ρ U := by
  rw [GlobalTheory.TwTrLevel.mem_fixed_iff]
  intro u hu
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  have h1 := (hB v (l ∘ₗ ρ u)).2
  have h2 := (hB v l).2
  rw [LinearMap.comp_apply] at h1
  rw [h1, h2]
  rw [← integral_mul_left_eq_self (μ := μ) (fun g => f g * l (ρ g v)) u]
  congr 1
  funext g
  rw [hf u hu g, map_mul, Module.End.mul_apply, LinearMap.comp_apply]

private theorem op_eq_sum {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup V] [Module ℂ V] (μ : Measure G)
    [μ.IsMulLeftInvariant] (K U : Subgroup G) (hKc : IsCompact (K : Set G)) (hK1 : μ K = 1)
    (hUo : IsOpen (U : Set G)) (hUK : U ≤ K) (ρ : Representation ℂ G V) (f : G → ℂ)
    (hf : GlobalTheory.BCT.IsHecke U f) (B : V →ₗ[ℂ] V) (hB : IsIntegralOp μ ρ f B) (w : V)
    (hw : w ∈ fixed ρ U) :
    B w = ((U.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ U, f q.out • ρ q.out w := by
  have hfs := GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1
  have hUfin : μ (U : Set G) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := μ (K : Set G))
    · rw [hK1]
      exact ENNReal.one_ne_top
    · exact measure_mono hUK
  obtain ⟨hvol, hne⟩ := GlobalTheory.HaarSum.vol_mul_relIndex μ K U hUK hKc hUo
  have hKr : μ.real (K : Set G) = 1 := by
    rw [Measure.real_def, hK1]
    rfl
  rw [hKr] at hvol
  have hUr : (μ.real (U : Set G) : ℂ) = ((U.relIndex K : ℕ) : ℂ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    exact_mod_cast hvol
  have hsupp : Function.support (fun q : G ⧸ U => f q.out • ρ q.out w) ⊆ ↑hfs.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset]
    intro h0
    apply hq
    simp only [h0, zero_smul]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero, (hB w l).2, finsum_eq_sum_of_support_subset _ hsupp]
  rw [GlobalTheory.HaarSum.integral_eq_sum_cosets μ U hUo hUfin (fun g => f g * l (ρ g w)) ?_ hfs.toFinset ?_]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hUr, map_smul, map_sum, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    rw [map_smul, smul_eq_mul]
  · intro x s hs
    have hw' := (GlobalTheory.TwTrLevel.mem_fixed_iff ρ U w).1 hw s hs
    rw [(hf.2 s hs x).2, map_mul, Module.End.mul_apply, hw']
  · intro q hq
    have : f q.out = 0 := by
      by_contra h0
      exact hq (hfs.mem_toFinset.2 h0)
    simp only [this, zero_mul]

theorem trSum : TrSum := by
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 V _ _ ρ hρ U hUo hUK f hf A hAf hAk B c hB hT hfd
  have hleft : ∀ k ∈ U, ∀ x, f (k * x) = f x := fun k hk x => (hf.2 k hk x).1
  have hTF : ∀ x, (B ∘ₗ A) x ∈ fixed ρ U := fun x => op_mem_fixed μ ρ U f hleft B hB (A x)
  have hs := GlobalTheory.TwTrLevel.finite_supp U hUo f hf.1
  have hEq : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ K U f A v = (B ∘ₗ A) v := by
    intro v hv
    rw [GlobalTheory.TwTrLevel.levOp_apply ρ K U f A v hs, LinearMap.comp_apply,
      op_eq_sum μ K U hKc hK1 hUo hUK ρ f hf B hB (A v) (hAf v hv)]
  have hmem : ∀ v ∈ fixed ρ U, GlobalTheory.BCT.levOp ρ K U f A v ∈ fixed ρ U := fun v hv => by
    rw [hEq v hv]
    exact hTF v
  obtain ⟨-, rfl⟩ := hT
  unfold GlobalTheory.BCT.twTr
  rw [dite_eq_left hmem]
  haveI := hfd
  rw [trace_range_eq (B ∘ₗ A) (fixed ρ U) hTF]
  congr 1
  ext v
  simp only [LinearMap.restrict_coe_apply]
  exact (hEq v v.2).symm

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TwScale
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

private theorem exists_eq_smul_id_of_irreducible {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin n) E) X) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (φ : X →ₗ[ℂ] X) (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  haveI : ρ.IsIrreducible := hi
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth
      (show GroundTheory.Automorphic.IsSmooth ρ from hs)).2
    (⟨φ, fun g => LinearMap.ext fun x => hφ g x⟩ : Representation.IntertwiningMap ρ ρ)
  exact ⟨c, LinearMap.ext fun x =>
    (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm⟩

set_option maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.L.twScale :
    UpperTheory.Gal.InertialTypesAlt.L.TwScale := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n V _ _ ρ hs hi I hI
  haveI := hi
  set m := Module.finrank k E with hm
  have hmpos : 0 < m := Module.finrank_pos
  have hiter : ∀ j : ℕ, ∀ g x, ((I : V →ₗ[ℂ] V) ^ j) (ρ g x) =
      ρ (GlobalTheory.LBC.galAct (σ ^ j) n g) (((I : V →ₗ[ℂ] V) ^ j) x) := by
    intro j
    induction j with
    | zero =>
      intro g x
      rw [pow_zero, pow_zero, GlobalTheory.LBC.galAct_one]
      rfl
    | succ j ih =>
      intro g x
      rw [pow_succ', pow_succ', GlobalTheory.LBC.galAct_mul, Module.End.mul_apply, Module.End.mul_apply, ih]
      exact hI _ _
  have hσm : σ ^ m = 1 := by
    rw [hm, ← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  obtain ⟨c, hc⟩ := exists_eq_smul_id_of_irreducible ρ hs hi ((I : V →ₗ[ℂ] V) ^ m) (by
    intro g x
    rw [hiter m g x, hσm, GlobalTheory.LBC.galAct_one]
    rfl)
  have hinj : Function.Injective ((I : V →ₗ[ℂ] V) ^ m) := by
    rw [Module.End.coe_pow]
    exact I.injective.iterate m
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GroundTheory.Automorphic.exists_ne_zero_of_isIrreducible (ρ := ρ)
    apply hv
    apply hinj
    rw [hc, zero_smul, map_zero]
    rfl
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ hmpos
  refine ⟨a, ?_, ?_, hmpos, ?_⟩
  · rintro rfl
    rw [zero_pow hmpos.ne'] at ha
    exact inv_ne_zero hc0 ha.symm
  · intro g
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, LinearEquiv.coe_coe]
    rw [hI]
  · rw [smul_pow, hc, ha, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rfl
end
end

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin mapGL)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

private theorem exists_trace {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (m : Measure (GL (Fin n) k)) [m.IsHaarMeasure]
    (τ : SmIrr (GL (Fin n) k)) (φ : GL (Fin n) k → ℂ) (hφ : Test φ) : ∃ z, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace m τ.ρ φ z := by
  obtain ⟨l1, -, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of k n
  have hA := (GlobalTheory.CompanionTheory.AdmDict.isAdmissible_iff τ.ρ).1 (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred)
  obtain ⟨A, hA1, hA2⟩ := PositivityTheory.TfC.OccursIff.exists_integralOp_of_admissible m τ.ρ hA φ hφ.1 hφ.2
  exact ⟨_, A, hA1, hA2, rfl⟩

private theorem fin_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (U : Subgroup (GL (Fin n) k)) (ho : IsOpen (U : Set (GL (Fin n) k)))
    (hc : IsCompact (U : Set (GL (Fin n) k))) : FiniteDimensional ℂ (fixed τ.ρ U) :=
  (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred).2 U ho hc

private theorem twKer_keep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Subgroup G)
    (θ : G → G) (hθ : ∀ u ∈ U, θ u ∈ U) (I : V →ₗ[ℂ] V) (hI : ∀ g x, I (ρ g x) = ρ (θ g) (I x)) :
    ∀ x ∈ twKer ρ U 1, I x ∈ twKer ρ U 1 := by
  have h : twKer ρ U 1 ≤ (twKer ρ U 1).comap I := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, x, rfl⟩
    refine Submodule.subset_span ⟨⟨θ u, hθ u u.2⟩, I x, ?_⟩
    simp [hI]
  exact fun x hx => h hx

private theorem cmp_onto {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) (g : Gw n w.1) :
    ∃ y : GL (Fin n) (CompletionsOver E v), GM.cmp w y = g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let e := RingEquiv.piUnique (fun w : PlacesOver E v => w.1.adicCompletion E)
  refine ⟨mapGL n (e.symm : _ →+* _) g, ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact e.apply_symm_apply (g i j)

end UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

open UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

theorem UpperTheory.Gal.InertialTypesAlt.L.inflTrace :
    GlobalTheory.DZA.InflMatching → UpperTheory.Gal.InertialTypesAlt.G.VarEx → UpperTheory.Gal.InertialTypesAlt.G.VarTrace → UpperTheory.Gal.InertialTypesAlt.G.NormInt → UpperTheory.Gal.InertialTypesAlt.L.InflTrace := by
  intro hIM hVE hVT hNI F E _ _ _ _ _ _ _ _ hp n hn π P hconj hweak v w hw hunr _ _ _ _ hcm F₀ F₁ _ _ _ _ _ rk rK s sb hres τ τ' hτ hτ'
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨hgen, hfr⟩ := UpperTheory.Gal.InertialTypesAlt.L.frobFacts _ _ F₀ F₁ rk rK s sb hres
  obtain ⟨hns, hdeg, hglob⟩ := UpperTheory.Gal.InertialTypesAlt.L.globOf F E hp v w hw hcm
  obtain ⟨σ, hσg, hσs⟩ := hglob s hgen
  obtain ⟨s', hs', hI⟩ := hVE F E σ hσg hp n hn P hconj v w hns
  obtain ⟨I₀, hI₀⟩ := hI τ' hτ'

  have hsg : ∀ g : Gw n w.1, s' g = GlobalTheory.LBC.galAct s n g := by
    intro g
    obtain ⟨y, rfl⟩ := cmp_onto w hw g
    have e := hs' y
    change (s' : Gw n w.1 →* Gw n w.1) (GM.cmp w y) = _
    rw [← e]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hσs (y i j)

  obtain ⟨a, ha, hTw⟩ := UpperTheory.Gal.InertialTypesAlt.L.twScale _ _ s hgen n τ'.V τ'.ρ τ'.smooth τ'.irred I₀
    (fun g x => by rw [hI₀, hsg])
  let I₂ : τ'.V ≃ₗ[ℂ] τ'.V := I₀.trans (LinearEquiv.smulOfNeZero ℂ τ'.V a ha)
  have hI₂c : (I₂ : τ'.V →ₗ[ℂ] τ'.V) = a • (I₀ : τ'.V →ₗ[ℂ] τ'.V) := rfl
  have hI₂ : ∀ g x, I₂ (τ'.ρ g x) = τ'.ρ (s' g) (I₂ x) := fun g x => by
    change a • I₀ (τ'.ρ g x) = τ'.ρ (s' g) (a • I₀ x)
    rw [hI₀, map_smul]

  obtain ⟨i1, i2, i3, i4, mE, mF, hE, hF, h1, h2⟩ := (UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).1
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨hH, hP⟩ := @UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E _ _ _ _ _ _ σ hσg v w hw _ _ _ _ s hgen hdeg hcm hσs n _ _ _ _ mE mF hE hF _ _
  have hUS := UpperTheory.V.Z.Tf.Orb.unitSB_holds
  have hPI := UpperTheory.V.Z.Tf.Orb.placeInt_holds
  have hcmp : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have hE1 : (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)))
      (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.1.adicCompletion E) : Set (GL (Fin n) (w.1.adicCompletion E))) = 1 := by
    rw [Measure.map_apply hcmp.measurable (hUS _ n).1.measurableSet, ← hPI.2 F E v w hw n, h1]
  have hF1 : mF (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) = 1 := by
    rw [hPI.1 F v n, h2]
  obtain ⟨c, hc, hcT⟩ := hVT F E σ hσg hp n hn π P hconj hweak v w hns mF _ hF hH τ τ' hτ hτ' (s' : Gw n w.1 →* Gw n w.1) I₂ hs' hI₂
  refine ⟨(I₂ : τ'.V →ₗ[ℂ] τ'.V), c, by rw [hI₂c]; exact hTw, hc, fun fb hfb => ?_⟩
  obtain ⟨hKk, hUko, hUkc, hUkle, -, hfk⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₀ rk hres.onto₀ n
  obtain ⟨hKK, hUKo, hUKc, hUKle, -, hfK⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₁ rK hres.onto₁ n
  obtain ⟨hHk, hTk, hSk⟩ := hfk fb
  obtain ⟨hHK, hTK, -⟩ := hfK (normLift sb fb)
  obtain ⟨hst1, -, -⟩ := hfr n
  have hstab : ∀ u ∈ K1 rK n, GlobalTheory.LBC.galAct s n u ∈ K1 rK n := fun u hu => by
    have : GlobalTheory.LBC.galAct s n u ∈ (K1 rK n).map (GlobalTheory.LBC.galAct s n) := Subgroup.mem_map_of_mem _ hu
    rwa [hst1] at this
  obtain ⟨hm1, hm2⟩ := hIM _ _ (UpperTheory.V.Z.Tf.Orb.extCont_of _ _).1 inferInstance F₀ F₁ hres.deg rk rK hres.onto₀ hres.onto₁
    hres.inc s sb hres.gal hres.frob n fb hfb
  rw [hKk, hKK] at hm1
  rw [hKk] at hm2
  have hM := UpperTheory.Gal.InertialTypesAlt.L.matchOfSum _ _ s hgen n _ mF hH hF hE1 hF1 (K1 rK n) (K1 rk n) _ _
    ⟨hUKo, hKK ▸ hUKle, hstab⟩ ⟨hUko, hKk ▸ hUkle, fun _ h => h⟩ hHK hHk hm1 hm2
  have hMA : GM.MatchAt σ v 1 (fun g => infl rK (normLift sb fb) (GM.cmp w g)) (infl rk fb) :=
    @(UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).2 i1 i2 i3 i4 mE mF hE hF h1 h2 _ _ _ (hP _ hTK _ hTk hM)
  have hsupp : ∀ g, infl rk fb g ≠ 0 → g ∈ UpperTheory.Gal.InertialTypesAlt.G.normSet E n v := fun g hg =>
    hNI F E σ hσg hp n hn v hunr g (by
      have h3 : g ∈ (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) := by
        have := hSk g hg
        rwa [hKk] at this
      rw [hPI.1 F v n] at h3
      exact h3)
  obtain ⟨z, hz⟩ := exists_trace mF τ _ hTk
  obtain ⟨B, hB, hBt⟩ := hcT _ _ 1 z hTK hTk hMA hsupp hz
  obtain ⟨A, hA, hAt⟩ := hz
  obtain ⟨l1, s1, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (v.adicCompletion F) n
  obtain ⟨l2, s2, t2, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (w.1.adicCompletion E) n
  have e1 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hH (KO _ n) (by rw [hKK]; exact (hUS _ n).1) (by rw [hKK]; exact (hUS _ n).2.1)
    (by rw [hKK]; exact hE1) _ τ'.ρ τ'.smooth (K1 rK n) hUKo hUKle _ hHK (I₂ : τ'.V →ₗ[ℂ] τ'.V)
    (fun x hx => by rw [hI₂c]; exact hTw.mem_fixed hst1 hx)
    (twKer_keep _ _ (GlobalTheory.LBC.galAct s n) hstab _ (fun g x => (hI₂ g x).trans (congrArg (fun h => τ'.ρ h (I₂ x)) (hsg g))))
    B _ hB hBt (fin_fixed τ' _ hUKo hUKc)
  have e2 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hF (KO _ n) (by rw [hKk]; exact (hUS _ n).1) (by rw [hKk]; exact (hUS _ n).2.1)
    (by rw [hKk]; exact hF1) _ τ.ρ τ.smooth (K1 rk n) hUko hUkle _ hHk LinearMap.id (fun _ h => h) (fun _ h => h)
    A z hA hAt (fin_fixed τ _ hUko hUkc)
  rw [← e1, ← e2, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinTrace
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem finsum_smul_comp {G W : Type} [Finite G] [AddCommGroup W] [Module ℂ W] (a : G → ℂ) (L : G → W →ₗ[ℂ] W)
    (R : W →ₗ[ℂ] W) : ∑ᶠ g, a g • (L g ∘ₗ R) = (∑ᶠ g, a g • L g) ∘ₗ R := by
  letI := Fintype.ofFinite G
  simp only [finsum_eq_sum_of_fintype]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply]

private theorem trace_finsum_smul {G W : Type} [Finite G] [AddCommGroup W] [Module ℂ W] (a : G → ℂ) (L : G → W →ₗ[ℂ] W) :
    LinearMap.trace ℂ W (∑ᶠ g, a g • L g) = ∑ᶠ g, a g * LinearMap.trace ℂ W (L g) := by
  letI := Fintype.ofFinite G
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, smul_eq_mul]

private theorem trace_step {G G' W W' : Type} [Finite G] [Finite G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (a : G' → ℂ) (L : G' → W' →ₗ[ℂ] W') (R : W' →ₗ[ℂ] W') (b : G → ℂ) (M : G → W →ₗ[ℂ] W) (R' : W →ₗ[ℂ] W) (hR' : R' = LinearMap.id)
    (c d d' : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (e : d' * LinearMap.trace ℂ W' (∑ᶠ g, a g • (L g ∘ₗ R)) = c * (d * LinearMap.trace ℂ W (∑ᶠ g, b g • (M g ∘ₗ R'))))
    (hne : ∑ᶠ g, b g * LinearMap.trace ℂ W (M g) ≠ 0) : ∑ᶠ g, a g • L g ≠ 0 := by
  subst hR'
  simp only [LinearMap.comp_id] at e
  rw [finsum_smul_comp, trace_finsum_smul] at e
  intro h0
  rw [h0, LinearMap.zero_comp, map_zero, mul_zero] at e
  exact mul_ne_zero hc (mul_ne_zero hd hne) e.symm

open scoped Classical in
private theorem normLift_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ} (f : GL (Fin n) F → ℂ) :
    normLift s f = GlobalTheory.Shin.shLift s f := by
  have e : ∀ δ : GL (Fin n) F', GlobalTheory.LBC.norm F s δ = GlobalTheory.Shin.nrm s δ := by
    intro δ
    unfold GlobalTheory.LBC.norm GlobalTheory.Shin.nrm GlobalTheory.Shin.nrmG
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      ext a b
      rfl
  funext δ
  have e2 : IsFinNorm s δ = GlobalTheory.Shin.IsNorm s δ := by
    funext γ
    unfold IsFinNorm GlobalTheory.Shin.IsNorm
    rw [e]
    rfl
  have aux : ∀ P Q : GL (Fin n) F → Prop, P = Q →
      (if h : ∃ γ, P γ then f h.choose else 0) = (if h : ∃ γ, Q γ then f h.choose else 0) := by
    rintro P _ rfl; rfl
  exact aux _ _ e2

private theorem twTr_level (hAct : FinAct) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (fb : GL (Fin n) 𝓀[k] → ℂ) (A : V →ₗ[ℂ] V)
    (hA : ∀ x ∈ fixed ρ (GlobalTheory.SplitWeil.KOne k (Fin n)), A x ∈ fixed ρ (GlobalTheory.SplitWeil.KOne k (Fin n))) :
    GlobalTheory.BCT.twTr ρ (KO k n) (K1 (IsLocalRing.residue 𝒪[k]) n) (infl (IsLocalRing.residue 𝒪[k]) fb) A =
      (Nat.card (GL (Fin n) 𝓀[k]) : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (GlobalTheory.LocGL.levelZero ρ g ∘ₗ A.restrict hA)) := by
  letI := Fintype.ofFinite 𝓀[k]
  obtain ⟨hl, r, hr, hT⟩ := hAct k 𝓀[k] (IsLocalRing.residue 𝒪[k]) IsLocalRing.residue_surjective n V ρ
  have er : r = GlobalTheory.LocGL.levelZero ρ := by
    ext g x
    obtain ⟨y, rfl⟩ := hl g
    have e1 := hr y x
    have e2 := GlobalTheory.LocGL.levelZero_apply ρ ((GlobalTheory.LocGL.toKO k (Fin n)) y) x
    have e3 : GlobalTheory.LocGL.redK k (Fin n) ((GlobalTheory.LocGL.toKO k (Fin n)) y) = GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) y := by
      simp [GlobalTheory.LocGL.redK]
    rw [e3] at e2
    exact e1.trans e2.symm
  subst er
  exact hT fb A hA

set_option synthInstance.maxHeartbeats 200000 in
private theorem exists_isRes (hRes : ResEx) {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K] (hu : PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k K)
    [Algebra 𝓀[k] 𝓀[K]] [Fintype 𝓀[k]]
    (hinc : ∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x →
      IsLocalRing.residue _ y = algebraMap 𝓀[k] 𝓀[K] (IsLocalRing.residue _ x))
    (s : 𝓀[K] ≃ₐ[𝓀[k]] 𝓀[K]) (hs : ∀ z, s z = z ^ Nat.card 𝓀[k]) :
    ∃ t : K ≃ₐ[k] K, IsRes (IsLocalRing.residue 𝒪[k]) (IsLocalRing.residue 𝒪[K]) t s := by
  obtain ⟨F₀, F₁, _, _, _, _, _, rk, rK, t, sb, h⟩ := hRes k K hu

  have kk : ∀ x : 𝒪[k], rk x = 0 ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
    intro x
    have hm : RingHom.ker rk = IsLocalRing.maximalIdeal 𝒪[k] :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective rk h.onto₀)
    rw [IsLocalRing.residue_eq_zero_iff, ← hm, RingHom.mem_ker]
  have kK : ∀ x : 𝒪[K], rK x = 0 ↔ IsLocalRing.residue 𝒪[K] x = 0 := by
    intro x
    have hm : RingHom.ker rK = IsLocalRing.maximalIdeal 𝒪[K] :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective rK h.onto₁)
    rw [IsLocalRing.residue_eq_zero_iff, ← hm, RingHom.mem_ker]
  let φ₀ : 𝓀[k] →+* F₀ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[k]) rk
    fun a ha => (kk a).2 ((IsLocalRing.residue_eq_zero_iff a).2 ha)
  let φ₁ : 𝓀[K] →+* F₁ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[K]) rK
    fun a ha => (kK a).2 ((IsLocalRing.residue_eq_zero_iff a).2 ha)
  have hφ₀ : ∀ x, φ₀ (IsLocalRing.residue _ x) = rk x := fun x => rfl
  have hφ₁ : ∀ x, φ₁ (IsLocalRing.residue _ x) = rK x := fun x => rfl
  have b₀ : Function.Bijective φ₀ := ⟨φ₀.injective, fun z => by
    obtain ⟨x, rfl⟩ := h.onto₀ z
    exact ⟨_, hφ₀ x⟩⟩
  have b₁ : Function.Bijective φ₁ := ⟨φ₁.injective, fun z => by
    obtain ⟨x, rfl⟩ := h.onto₁ z
    exact ⟨_, hφ₁ x⟩⟩
  let e₀ : 𝓀[k] ≃+* F₀ := RingEquiv.ofBijective φ₀ b₀
  let e₁ : 𝓀[K] ≃+* F₁ := RingEquiv.ofBijective φ₁ b₁
  have hint : ∀ x : 𝒪[k], ∃ y : 𝒪[K], (y : K) = algebraMap k K x := by
    intro x
    have h1 : (x : k) ≤ᵥ 1 := (Valuation.Compatible.vle_iff_le (v := valuation k) _ _).2 (by rw [map_one]; exact (Valuation.mem_integer_iff _ _).1 x.2)
    have h2 : algebraMap k K x ≤ᵥ algebraMap k K 1 := ValuativeExtension.vle_iff_vle.2 h1
    rw [map_one] at h2
    exact ⟨⟨algebraMap k K x, (Valuation.mem_integer_iff _ _).2 (by simpa using (Valuation.Compatible.vle_iff_le (v := valuation K) _ _).1 h2)⟩, rfl⟩
  have hc : (algebraMap F₀ F₁).comp e₀.toRingHom = e₁.toRingHom.comp (algebraMap 𝓀[k] 𝓀[K]) := by
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨y, hy⟩ := hint x
    show algebraMap F₀ F₁ (φ₀ _) = φ₁ (algebraMap 𝓀[k] 𝓀[K] _)
    rw [← hinc x y hy, hφ₀, hφ₁, h.inc x y hy]
  have hq : Fintype.card F₀ = Nat.card 𝓀[k] := by
    rw [← Nat.card_eq_fintype_card]; exact (Nat.card_congr e₀.toEquiv).symm
  refine ⟨t, ?_, IsLocalRing.residue_surjective, IsLocalRing.residue_surjective, hinc, ?_, ?_⟩
  · rw [← h.deg]
    exact Algebra.finrank_eq_of_equiv_equiv e₀ e₁ hc
  · intro x y hy
    have h1 : rK y = rK x ^ Nat.card 𝓀[k] := by rw [h.gal x y hy, h.frob, hq]
    have h2 : rK (y - x ^ Nat.card 𝓀[k]) = 0 := by rw [map_sub, map_pow, h1, sub_self]
    have h3 := (kK _).1 h2
    rw [map_sub, map_pow, sub_eq_zero] at h3
    rw [h3, hs]
  · intro z
    rw [hs, Nat.card_eq_fintype_card]

theorem finTrace :
    ResEx → FinAct → InflFacts → FrobFacts → InflTrace → UpperTheory.Gal.InertialTypesAlt.FinTrace := by
  intro hRes hAct hInfl hFrob hIT F E _ _ _ _ _ _ _ _ hp n hn π P hcj hbc v w hsp hu τ τ' hτ hτ' _ hinc s hs f hf hne
  obtain ⟨w', hw'⟩ := UpperTheory.V.Z.Tf.Orb.placeUniq_holds F E hp v hsp
  have hw : ∀ x : PlacesOver E v, x = w := fun x => (hw' x).trans (hw' w).symm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hp.pos
  haveI : Fact (Module.finrank F E).Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := by
    apply isCyclic_of_prime_card (p := Module.finrank F E)
    exact IsGalois.card_aut_eq_finrank F E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  obtain ⟨i1, i2, i3, i4, s0, hs0, hr, h1, h2, h3⟩ := UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  letI := Fintype.ofFinite 𝓀[v.adicCompletion F]
  letI := Fintype.ofFinite 𝓀[w.1.adicCompletion E]
  have hcm : ∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x := h1
  obtain ⟨t, ht⟩ := exists_isRes hRes (h3 (hu w))
    (fun x y hy => hinc x y (hy.trans (hcm x).symm)) s hs
  obtain ⟨I, c, hI, hc, H⟩ := hIT F E hp n hn π P hcj hbc v w hw hu hcm _ _ _ _ t s ht τ τ' hτ hτ'
  have hst := ((hFrob _ _ _ _ _ _ t s ht).2 n).1
  have hA : ∀ x ∈ fixed τ'.ρ (GlobalTheory.SplitWeil.KOne (w.1.adicCompletion E) (Fin n)),
      I x ∈ fixed τ'.ρ (GlobalTheory.SplitWeil.KOne (w.1.adicCompletion E) (Fin n)) :=
    fun x hx => hI.mem_fixed hst hx
  have hB : ∀ x ∈ fixed τ.ρ (GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n)),
      (LinearMap.id : τ.V →ₗ[ℂ] τ.V) x ∈ fixed τ.ρ (GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n)) :=
    fun x hx => hx
  have e := H f hf
  rw [normLift_eq, twTr_level hAct n τ'.ρ _ I hA, twTr_level hAct n τ.ρ f _ hB] at e
  have hid : (LinearMap.id : τ.V →ₗ[ℂ] τ.V).restrict hB = LinearMap.id := by
    ext x
    rfl
  have hcard : (Nat.card (GL (Fin n) 𝓀[v.adicCompletion F]) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  exact trace_step _ _ _ _ _ _ hid _ _ _ hc hcard e hne

end UpperTheory.Gal.InertialTypesAlt.L
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.RamOne
open ValuativeRel PositivityTheory.Rg.Tf.Loc

private theorem ramOne (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] (h : IsUnramifiedLoc k K) :
    (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation k))) = 1 := by
  obtain ⟨π, hπ, hmin⟩ := h
  have hv := Valuation.integer.integers (valuation K)
  rw [← GroundTheory.LocalField.isUnramified_iff, ← GroundTheory.LocalField.map_maximalIdeal_eq_iff]
  have hπk : π ∈ 𝒪[k] := (GroundTheory.LocalField.algebraMap_mem_integer_iff k K π).1 (le_of_lt hπ)
  let p : 𝒪[k] := ⟨π, hπk⟩
  have hpK : ((algebraMap 𝒪[k] 𝒪[K] p : 𝒪[K]) : K) = algebraMap k K π := rfl
  have hp : p ∈ 𝓂[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hv.one_of_isUnit (hu.map (algebraMap 𝒪[k] 𝒪[K]))
    change valuation K ((algebraMap 𝒪[k] 𝒪[K] p : 𝒪[K]) : K) = 1 at h1
    rw [hpK] at h1
    exact (ne_of_lt hπ) h1
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.2 (fun x hx => by
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact ((IsLocalRing.mem_maximalIdeal x).1 hx) (isUnit_of_map_unit _ _ hu))
  · intro x hx
    have hxlt : valuation K (x : K) < 1 := by
      by_contra hge
      have heq : valuation K (x : K) = 1 := le_antisymm x.2 (not_lt.1 hge)
      exact ((IsLocalRing.mem_maximalIdeal x).1 hx) (hv.isUnit_of_one' heq)
    have hle := hmin (x : K) hxlt
    rw [← hpK] at hle
    obtain ⟨z, hz⟩ := hv.dvd_of_le (x := x) (y := algebraMap 𝒪[k] 𝒪[K] p) hle
    rw [hz]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp)

theorem UpperTheory.Gal.InertialTypesAlt.L.resEx :
    UpperTheory.Gal.InertialTypesAlt.L.ResEx := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ hu
  have h1 := ramOne k K hu
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  refine ⟨𝓀[k], 𝓀[K], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsLocalRing.residue _, IsLocalRing.residue _, GroundTheory.LocalField.frobenius k K h1,
    GroundTheory.LocalField.residueAlgEquiv k K (GroundTheory.LocalField.frobenius k K h1), ?_⟩
  refine ⟨?_, IsLocalRing.residue_surjective, IsLocalRing.residue_surjective, ?_, ?_, ?_⟩
  · rw [← GroundTheory.LocalField.residueDegree_eq_finrank,
      GroundTheory.LocalField.residueDegree_eq_finrank_of_unramified k K h1]
  · intro x y h
    have e : y = algebraMap 𝒪[k] 𝒪[K] x := Subtype.ext h
    rw [e]
    rfl
  · intro x y h
    have e : y = GroundTheory.LocalField.integerAlgEquiv k K (GroundTheory.LocalField.frobenius k K h1) x :=
      Subtype.ext h
    rw [e, GroundTheory.LocalField.residueAlgEquiv_residue]
  · intro z
    rw [GroundTheory.LocalField.residueAlgEquiv_frobenius_apply, Fintype.card_eq_nat_card]
end

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem elemPairJ_holds : UpperTheory.Gal.Join.ElemPairJ := elemPairJ elemPair

theorem finTrace_holds (h : GlobalTheory.DZA.InflMatching) (h₁ : G.VarEx) (h₂ : G.VarTrace) (h₃ : G.NormInt) : FinTrace :=
  finTrace resEx finAct inflFacts frobFacts (inflTrace h h₁ h₂ h₃)

end UpperTheory.Gal.InertialTypesAlt.L
