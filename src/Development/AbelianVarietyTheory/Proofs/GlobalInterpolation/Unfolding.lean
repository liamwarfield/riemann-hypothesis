module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure MeasureTheory

namespace GlobalTheory.RationalStabiliserDomains

theorem isDiscreteWithDomains_inf_subgroupOf {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ S : Subgroup G) [Countable Γ] [DiscreteTopology Γ] :
    IsDiscreteWithDomains ((Γ ⊓ S).subgroupOf S) := by
  let f : (Γ ⊓ S).subgroupOf S → Γ := fun g => ⟨g.1.1, g.2.1⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have : Countable ((Γ ⊓ S).subgroupOf S) := hf.countable
  have : DiscreteTopology ((Γ ⊓ S).subgroupOf S) := DiscreteTopology.of_continuous_injective hc hf
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set G)
  exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_of_discrete _

theorem isDiscreteWithDomains_HstabFin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  intro F E _ _ _ _ _ σ _ M J _ x _
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have h := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ M J
  have := h.1
  have := h.2.1
  exact isDiscreteWithDomains_inf_subgroupOf (ratPts (AF F) σ J) (Hstab (AF F) σ J x)

end GlobalTheory.RationalStabiliserDomains
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVectorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  first | exact @GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | exact GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | (intros; apply GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodular
open MeasureTheory NumberField IsDedekindDomain Matrix Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicUnimod
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
open Formalism.UG (UJ cT intAd)
open scoped TensorProduct NNReal ENNReal Pointwise RestrictedProduct

noncomputable section

namespace GlobalTheory.FiniteAdelicUnimod

open GlobalTheory.AdelicPointsUnimod (exists_sum_tmul exists_compact_subring congSub isCompact_congSub
  modular_of_mem_compact isCompact_intAd)

section Adeles

variable {F : Type} [Field F] [NumberField F]

theorem exists_split_finiteAdele {κ : Type} [Finite κ] (a : κ → Af F) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (p : Af F →ₐ[F] R) (e : Af F),
    IsArtinianRing R ∧ Function.Surjective p ∧ p e = 1 ∧ (∀ x, p x = 0 → e * x = 0) ∧
      ∀ k, (1 - e) * a k ∈ intAd F := by
  classical
  let S := ⋃ k, {v : HeightOneSpectrum (𝓞 F) | a k v ∉ v.adicCompletionIntegers F}
  have hS : S.Finite := Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (a k).2
  haveI : Finite S := hS.to_subtype
  let p : Af F →ₐ[F] (∀ v : S, v.1.adicCompletion F) :=
    { toFun := fun x v => x v.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let s : (∀ v : S, v.1.adicCompletion F) → Af F := fun y =>
    ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by
      filter_upwards [hS.compl_mem_cofinite] with v hv
      rw [dite_eq_right hv]
      exact zero_mem _⟩
  have hs : ∀ y, p (s y) = y := fun y => funext fun v => dif_pos v.2
  have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by
    show dite _ _ _ = _
    split_ifs <;> rfl
  refine ⟨_, inferInstance, inferInstance, p, s 1, inferInstance, fun y => ⟨_, hs y⟩, hs 1, fun x hx => ?_,
    fun k v => ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show s 1 v * x v = 0
    rw [hs1]
    split_ifs with h
    · rw [one_mul]
      exact congrFun hx ⟨v, h⟩
    · exact zero_mul _
  · show (1 - s 1 v) * a k v ∈ _
    rw [hs1]
    split_ifs with h
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul]
      exact not_not.1 fun h' => h (Set.mem_iUnion.2 ⟨k, h'⟩)

end Adeles

section Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_split_tensor (σ : E →ₐ[F] E) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {κ : Type} [Finite κ]
    (C : NonUnitalSubring (Af F ⊗[F] E)) (hC : ∀ r ∈ intAd F, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C)
    (x : κ → Af F ⊗[F] E) : ∃ (B : Type) (_ : CommRing B) (σ' : B →+* B) (π : Af F ⊗[F] E →+* B)
      (e : Af F ⊗[F] E), (∀ x, π (sigR (Af F) σ x) = σ' (π x)) ∧ Function.Surjective π ∧ π e = 1 ∧
      (∀ x, π x = 0 → e * x = 0) ∧ sigR (Af F) σ e = e ∧ Generic σ' ∧ ∀ k, (1 - e) * x k ∈ C := by
  classical
  choose a ha using fun k => exists_sum_tmul (x k)
  obtain ⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩ :=
    exists_split_finiteAdele (κ := κ × _) fun q => a q.1 q.2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  letI : Algebra ℚ (R ⊗[F] E) := ((inclR (F := F) R).comp (algebraMap ℚ E)).toAlgebra
  refine ⟨R ⊗[F] E, inferInstance, sigR R σ, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom,
    e ⊗ₜ 1, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ hp Function.surjective_id, ?_, fun y hy => ?_, ?_,
    generic_of_semilocal (δ := inclR R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · simp [hpe, Algebra.TensorProduct.one_def]
  · have hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map p (AlgHom.id F E)) := hy
    rw [Algebra.TensorProduct.rTensor_ker _ hp] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simp [hker z hz]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  · simp [sigR]
  · simp [sigR, inclR, hσδ, TensorProduct.tmul_neg]
  · rw [ha k, Finset.mul_sum, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact hC _ (hint (k, i)) _

theorem isUnimodularLC_finiteAdele (σ : E →ₐ[F] E) (hss : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0)
    (hσδ : σ δ = -δ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) :
    IsUnimodularLC (HA (Af F) σ J) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨h⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : T2Space (Af F ⊗[F] E) := h.isEmbedding.t2Space
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_HA (Af F) σ n J
  haveI : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨Measure.haar, inferInstance⟩, fun μ _ => ?_⟩
  have hσ := GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ
  obtain ⟨C, hCc, hC⟩ := exists_compact_subring (F := F) (E := E) (intAd F).toNonUnitalSubring
    (isCompact_intAd F)
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hss (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (Af F) σ) (JR (Af F) J) (M.map (inclR (Af F))) :=
    hM.map fun x => by simp [sigR, inclR]
  have hss' := GlobalTheory.AdelicPointsUnimod.sigR_sigR (R := Af F) hss
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution hσ hss' hF
  refine ⟨fun g => ?_⟩
  obtain ⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩ := exists_split_tensor σ hδ hσδ
    (κ := Bool × Fin n × Fin n) C hC fun p =>
      (mat (σ := sigR (Af F) σ) (J := JR (Af F) J) (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2
  let χ : HA (Af F) σ J →* ℝ≥0 := Measure.modularCharacter
  have hχ := modular_involution (G := HA (Af F) σ J) T hTc hT
  obtain ⟨k, hk, hk', hkg⟩ := exists_char_eq h1 h2 h3 h4 h5 hss' hF h6 χ
    (fun x x' h => by
      rw [hT' x x' h]
      exact hχ x) g
  have hkK : k ∈ congSub (sigR (Af F) σ) (JR (Af F) J) C :=
    ⟨fun i j => by rw [hk]; exact h7 (true, i, j), fun i j => by rw [hk']; exact h7 (false, i, j)⟩
  let K : Subgroup (HA (Af F) σ J) := congSub (sigR (Af F) σ) (JR (Af F) J) C
  have hKc : IsCompact (K : Set (HA (Af F) σ J)) := isCompact_congSub hσ _ C hCc
  have h8 := modular_of_mem_compact K hKc (k := k) hkK
  rw [map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]

end Tensor

theorem unimodularOver_finiteAdele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      UnimodularOver (Af F) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hss := GlobalTheory.HermLineZeros.conj_invol hσ
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne hσ
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_forall (Af F) hss
    (fun _ _ h => isUnimodularLC_finiteAdele σ hss (sub_ne_zero.2 hd) (by rw [map_sub, hss, neg_sub]) h) hJ

end GlobalTheory.FiniteAdelicUnimod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodularStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (Af F) σ J := by
  first | exact @GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele | exact GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele | (intros; apply GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
namespace GlobalTheory

theorem adelicUnitaryHaar_holds : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  exact ⟨GlobalTheory.T.adelic_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ, GlobalTheory.T.archimedean_unitaryGroup_stabilisers_unimodular F E σ hσ M J hJ,
    GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular F E σ hσ M J hJ, GlobalTheory.T.localUnitaryGroup_stabilizers_unimodular_finitePlace F E σ hσ M J hJ,
    GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm F E σ hσ M J hJ, GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer F E σ hσ M J hJ⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  first | exact @GlobalTheory.adelicUnitaryHaar_holds | exact GlobalTheory.adelicUnitaryHaar_holds | (intros; apply GlobalTheory.adelicUnitaryHaar_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualStabilizer
noncomputable section

namespace GlobalTheory.Proof.SelfDualStabilizer

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

theorem unramifiedAtFinite_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.UnramifiedAtFinite F E ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.UnramifiedAtFinite F E := by
  constructor
  · intro h P hP hne
    exact h ⟨P, hP, hne⟩
  · intro h P
    exact @h P.asIdeal P.isPrime P.ne_bot

section Clauses

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)


omit [NumberField F] [NumberField E] in
theorem isSelfDualLattice_iff (L : Submodule (𝓞 E) (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.IsSelfDualLat σ J L := Iff.rfl


omit [NumberField F] [NumberField E] in
theorem perpPart_eq (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.perpPart σ J (L : Set (Fin M → E)) x = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.perpIn σ J L x := rfl


omit [NumberField E] in
theorem stabHat_eq (S : Set (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.stabHat σ J S = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.stabLat (Af F) σ J (latHat F E S) :=
  Subgroup.ext fun _ => Iff.rfl


omit [NumberField E] in
theorem orbitClaims_iff (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims σ J (L : Set (Fin M → E)) x β ↔
      GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl F E σ J L x β := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl
  rw [stabHat_eq, stabHat_eq, perpPart_eq]
  exact Iff.rfl

end Clauses

theorem stabTransitive_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun σ => imp_congr_right fun _ => ?_
  refine imp_congr (unramifiedAtFinite_iff F E) ?_
  refine forall_congr' fun M => forall_congr' fun J => imp_congr_right fun _ =>
    forall_congr' fun L => imp_congr (isSelfDualLattice_iff σ J L) ?_
  exact forall_congr' fun β => imp_congr_right fun _ => forall_congr' fun x =>
    imp_congr_right fun _ => imp_congr_right fun _ => orbitClaims_iff σ J L x β

end GlobalTheory.Proof.SelfDualStabilizer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
namespace GlobalTheory.StabOrbit

theorem stabTransitive : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive :=
  GlobalTheory.Proof.SelfDualStabilizer.stabTransitive_iff.1 (stabTransitive_of_lemmas GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis)

end GlobalTheory.StabOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLengthStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  first | exact @GlobalTheory.StabOrbit.stabTransitive | exact GlobalTheory.StabOrbit.stabTransitive | (intros; apply GlobalTheory.StabOrbit.stabTransitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureNormalisedByHaarUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureNormalisedByHaarUnique
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique

theorem normaliseQuotientClause : NormaliseQuotientClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH hG hH' dg _ ν _
  obtain ⟨⟨μ₀, hμ₀⟩, huniq⟩ := GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular G H hH hG hH'
  obtain ⟨dg₀, ⟨hdg₀, hF₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ₀ hμ₀
  set c : ℝ≥0 := haarScalarFactor dg dg₀ with hc
  have hcpos : 0 < c := haarScalarFactor_pos_of_isHaarMeasure dg dg₀
  have hdg : dg = c • dg₀ := isMulLeftInvariant_eq_smul dg dg₀
  have hR : IsInvariantRadon H (c • μ₀) := by
    haveI := hμ₀.finiteOnCompacts
    haveI := hμ₀.invariant
    refine ⟨?_, inferInstance, ⟨fun g s hs => ?_⟩⟩
    · intro h
      apply hμ₀.ne_zero
      have : c⁻¹ • (c • μ₀) = μ₀ := by
        rw [smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
      rw [← this, h, smul_zero]
    · simp only [Measure.coe_nnreal_smul_apply]
      rw [SMulInvariantMeasure.measure_preimage_smul g hs]
  have hF : QuotientFormula H dg ν (c • μ₀) := by
    intro f hf
    obtain ⟨h1, h2⟩ := hF₀ f hf
    refine ⟨h1, ?_⟩
    rw [hdg, lintegral_smul_measure, lintegral_smul_measure, h2]
  refine ⟨c • μ₀, ⟨hR, hF⟩, ?_⟩
  rintro μ ⟨hμ, hμF⟩
  obtain ⟨d, -, hd⟩ := huniq _ _ hR hμ
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hKm : MeasurableSet (K : Set G) := K.isCompact.measurableSet
  have hfm : Measurable ((K : Set G).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hKm
  have e1 := (hF _ hfm).2
  have e2 := (hμF _ hfm).2
  rw [hd, lintegral_smul_measure, ← e1, lintegral_indicator_const hKm, one_mul] at e2
  have hpos : dg K ≠ 0 := (measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
  have hfin : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have hd1 : d = 1 := by
    have : (d : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]; exact e2.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).mp this
  rw [hd, hd1, one_smul]

end GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureNormalisedByHaarUniqueStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_normalised_by_haar_unique : NormaliseQuotientClause := by
  first | exact @GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | exact GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause | (intros; apply GlobalTheory.Proof.quotientMeasure_normalised_by_haar_unique.normaliseQuotientClause <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarSubgroupQuotientIntegralFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarSubgroupQuotientIntegralFormula
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal NNReal

namespace GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)

theorem fibreIntegral_smul (c : ℝ≥0) (ν : Measure H) [ν.IsMulLeftInvariant]
    [(c • ν).IsMulLeftInvariant] (f : G → ℝ≥0∞) :
    fibreIntegral H (c • ν) f = fun q => (c : ℝ≥0∞) * fibreIntegral H ν f q := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [fibreIntegral_mk, fibreIntegral_mk, lintegral_smul_measure]
  rfl

theorem quotientFormula_smul [MeasurableSpace (G ⧸ H)] (c : ℝ≥0) (dg : Measure G)
    (ν : Measure H) [ν.IsMulLeftInvariant] [(c • ν).IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) : QuotientFormula H (c • dg) (c • ν) μ := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  rw [fibreIntegral_smul]
  refine ⟨h1.const_mul _, ?_⟩
  rw [lintegral_const_mul _ h1, lintegral_smul_measure, h2]
  rfl

theorem eq_of_quotientFormula [MeasurableSpace (G ⧸ H)] {dg dg' : Measure G}
    (ν : Measure H) [ν.IsMulLeftInvariant] (μ : Measure (G ⧸ H))
    (h : QuotientFormula H dg ν μ) (h' : QuotientFormula H dg' ν μ) : dg = dg' := by
  ext s hs
  have hm : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (h _ hm).2, (h' _ hm).2]

end

theorem normaliseSubgroupClause : NormaliseSubgroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ dg _ μ hμ
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H :=
    inferInstanceAs (SecondCountableTopology (H : Set G))
  have key : ∀ (ν ν' : Measure H) [ν.IsHaarMeasure] [ν'.IsHaarMeasure],
      QuotientFormula H dg ν μ → QuotientFormula H dg ν' μ → ν' = ν := by
    intro ν ν' _ _ h h'
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν' = c • ν := ⟨_, Measure.isMulLeftInvariant_eq_smul ν' ν⟩
    subst hc
    have h1 := eq_of_quotientFormula H _ μ (quotientFormula_smul H c dg ν μ h) h'
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
    have hK0 : dg K ≠ 0 :=
      (Measure.measure_pos_of_nonempty_interior dg K.interior_nonempty).ne'
    have hKt : dg K ≠ ∞ := K.isCompact.measure_lt_top.ne
    have h2 : (c : ℝ≥0∞) * dg K = 1 * dg K := by
      rw [one_mul]
      have := congrArg (fun m : Measure G => m K) h1
      simpa using this
    have h3 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp h2
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h4, one_smul]
  obtain ⟨dg₀, ⟨_, h₀⟩, -⟩ := GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH (Measure.haar : Measure H) μ hμ
  have hc : dg = Measure.haarScalarFactor dg dg₀ • dg₀ :=
    Measure.isMulLeftInvariant_eq_smul dg dg₀
  have hpos : Measure.haarScalarFactor dg dg₀ ≠ 0 :=
    (Measure.haarScalarFactor_pos_of_isHaarMeasure dg dg₀).ne'
  haveI hν : (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)).IsHaarMeasure :=
    Measure.IsHaarMeasure.nnreal_smul _ hpos
  have h₁ : QuotientFormula H dg
      (Measure.haarScalarFactor dg dg₀ • (Measure.haar : Measure H)) μ := by
    have := quotientFormula_smul H (Measure.haarScalarFactor dg dg₀) dg₀ _ μ h₀
    rwa [← hc] at this
  refine ⟨_, ⟨hν, h₁⟩, ?_⟩
  rintro ν ⟨_, h⟩
  exact key _ _ h₁ h

end GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarSubgroupQuotientIntegralFormulaStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula : NormaliseSubgroupClause := by
  first | exact @GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause | exact GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause | (intros; apply GlobalTheory.Proof.existsUnique_haar_subgroup_quotient_integral_formula.normaliseSubgroupClause <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarGroupQuotientIntegralFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarGroupQuotientIntegralFormula
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

namespace GlobalTheory

theorem normaliseGroupClause_holds : NormaliseGroupClause := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH _ _ ν _ μ hμ
  exact GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets G H hH ν μ hμ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarGroupQuotientIntegralFormulaStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula : NormaliseGroupClause := by
  first | exact @GlobalTheory.normaliseGroupClause_holds | exact GlobalTheory.normaliseGroupClause_holds | (intros; apply GlobalTheory.normaliseGroupClause_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodular
section -- CompactSubgroupQuotientInvariantMeasure + CompactSubgroupQuotientInvariantMeasureStatement
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal

theorem _root_.GlobalTheory.T.compactSubgroup_quotient_invariant_measure : CompactClause := by
  intro G _ _ _ _ _ _ H _ _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  borelize G
  refine GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space G H hH.isClosed fun h => ?_
  rw [GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact H hH h.2,
    GlobalTheory.AdelicPointsUnimod.modular_of_mem_compact (⊤ : Subgroup H) (by simpa using isCompact_univ)
      (Subgroup.mem_top h)]
end

namespace GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular

theorem quotientMeasures : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures :=
  ⟨GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular, GlobalTheory.T.quotientMeasure_normalised_by_haar_unique, GlobalTheory.T.existsUnique_haar_subgroup_quotient_integral_formula, GlobalTheory.T.existsUnique_haar_group_quotient_integral_formula, GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left, GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space,
    GlobalTheory.T.compactSubgroup_quotient_invariant_measure⟩

end GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodularStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_integration_formulas_unimodular : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures := by
  first | exact @GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | exact GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures | (intros; apply GlobalTheory.Proof.quotientMeasure_integration_formulas_unimodular.quotientMeasures <;> assumption)
end
end

namespace GlobalTheory.UnfoldingObj

theorem unfolding : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding.Unfolding D := fun D =>
  (GlobalTheory.UnfoldingCompare.unfolding_iff D).1 (GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer GlobalTheory.T.quotientMeasure_integration_formulas_unimodular GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof GlobalTheory.T.stabSelfDualLattice_transitive_on_length D)

end GlobalTheory.UnfoldingObj
