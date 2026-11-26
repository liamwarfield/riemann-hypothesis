module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem pi_hom_ext {r : ℕ} {N : Fin r → Type} [∀ i, Monoid (N i)] {M : Type} [Monoid M]
    (f g : (∀ i, N i) →* M) (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) : f = g := by
  apply (MonoidHom.noncommPiCoprodEquiv (ι := Fin r) (N := N) (M := M)).symm.injective
  apply Subtype.ext
  funext i
  exact MonoidHom.ext fun x => h i x

private noncomputable def cfH {K : Type} [Field K] [NumberField K] {n : ℕ} (v : Pl K) : FA K n →* Gw n v where
  toFun := GM.cf v
  map_one' := by simp only [GM.cf]; rw [map_one, finAt_one]
  map_mul' a b := by simp only [GM.cf]; rw [map_mul, finAt_mul]

private theorem cf_ext {K : Type} [Field K] [NumberField K] {n : ℕ} {a b : FA K n}
    (h : ∀ v : Pl K, GM.cf v a = GM.cf v b) : a = b := by
  apply (AdelicGLn.finiteRestrictedEquiv K n).injective
  ext v : 1
  exact h v

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.embEx :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) {r : ℕ} (w : Fin r → Pl K), Function.Injective w → (∃ ι, IsEmb (n := n) w ι) ∧ ∀ ι : GS n w →* FA K n, IsEmb w ι →
      Continuous ι ∧ (∀ g i, GM.cf (w i) (ι g) = g i) ∧ (∀ g, ∀ v ∉ im w, GM.cf v (ι g) = 1) ∧
      (∀ h : FA K n, ∃ g h', h = ι g * h' ∧ ∀ i, GM.cf (w i) h' = 1) ∧ (∀ g (h' : FA K n), (∀ i, GM.cf (w i) h' = 1) → Commute (ι g) h') ∧
      ∀ (U : ∀ v : Pl K, Subgroup (Gw n v)) (h : FA K n), h ∈ levOn (im w) U ↔
        ∃ g h', h = ι g * h' ∧ (∀ i, g i ∈ U (w i)) ∧ (∀ i, GM.cf (w i) h' = 1) ∧ ∀ v, GM.cf v h' ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  intro K _ _ n r w hw
  have L := fun v : Pl K => UpperTheory.ConvolutionTheory.Tf.locEmb K n v
  refine ⟨?_, ?_⟩
  · refine ⟨MonoidHom.noncommPiCoprod (fun i => AdelicGLn.localEmbedding (w i)) ?_, ?_⟩
    · intro i j hij x y
      exact (L (w i)).2.2.2.1 (w j) (fun e => hij (hw e).symm) x y
    · intro i g
      exact MonoidHom.noncommPiCoprod_mulSingle (N := fun i => Gw n (w i)) (fun i => AdelicGLn.localEmbedding (w i)) i g
  intro ι hι
  have hmul : ∀ (v : Pl K) (a b : FA K n), GM.cf v (a * b) = GM.cf v a * GM.cf v b :=
    fun v a b => map_mul (cfH v) a b
  have hinv : ∀ (v : Pl K) (a : FA K n), GM.cf v a⁻¹ = (GM.cf v a)⁻¹ :=
    fun v a => map_inv (cfH v) a
  have hone : ∀ v : Pl K, GM.cf v (1 : FA K n) = 1 := fun v => map_one (cfH v)
  have hcf : ∀ g i, GM.cf (w i) (ι g) = g i := by
    intro g i
    have e : (cfH (w i)).comp ι = Pi.evalMonoidHom (fun j => Gw n (w j)) i := by
      refine pi_hom_ext _ _ fun j x => ?_
      change GM.cf (w i) (ι (Pi.mulSingle j x)) = (Pi.mulSingle j x : GS n w) i
      rw [hι j x]
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact (L (w j)).2.1 x
      · rw [Pi.mulSingle_eq_of_ne (Ne.symm h)]
        exact (L (w j)).2.2.1 (w i) (fun e => h (hw e).symm) x
    exact DFunLike.congr_fun e g
  have hoff : ∀ g, ∀ v ∉ im w, GM.cf v (ι g) = 1 := by
    intro g v hv
    have e : (cfH v).comp ι = 1 := by
      refine pi_hom_ext _ _ fun j x => ?_
      change GM.cf v (ι (Pi.mulSingle j x)) = 1
      rw [hι j x]
      exact (L (w j)).2.2.1 v (fun e => hv (e ▸ Finset.mem_image_of_mem w (Finset.mem_univ j))) x
    exact DFunLike.congr_fun e g
  have hcomm : ∀ g (h' : FA K n), (∀ i, GM.cf (w i) h' = 1) → Commute (ι g) h' := by
    intro g h' hh
    refine cf_ext fun v => ?_
    rw [hmul, hmul]
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hh i, one_mul, mul_one]
    · rw [hoff g v hv, one_mul, mul_one]
  have hsplit : ∀ h : FA K n, ∀ i, GM.cf (w i) ((ι fun j => GM.cf (w j) h)⁻¹ * h) = 1 := by
    intro h i
    rw [hmul, hinv, hcf, inv_mul_cancel]
  have hcont : Continuous ι := by
    let tr : Finset (Fin r) → GS n w → GS n w := fun s g i => if i ∈ s then g i else 1
    have hc : ∀ s : Finset (Fin r), Continuous fun g => ι (tr s g) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e : (fun g => ι (tr ∅ g)) = fun _ => 1 := by
          funext g
          have : tr ∅ g = 1 := by funext i; simp [tr]
          rw [this, map_one]
        rw [e]
        exact continuous_const
      | insert a s ha ih =>
        have e : (fun g => ι (tr (insert a s) g)) =
            fun g => ι (tr s g) * AdelicGLn.localEmbedding (w a) (g a) := by
          funext g
          rw [← hι a (g a), ← map_mul]
          congr 1
          funext i
          by_cases h : i = a
          · subst h
            simp [tr, ha]
          · simp [tr, h, Pi.mulSingle_eq_of_ne h]
        rw [e]
        exact ih.mul ((L (w a)).1.comp (continuous_apply a))
    have e : (fun g => ι (tr Finset.univ g)) = ι := by
      funext g
      congr 1
      funext i
      simp [tr]
    rw [← e]
    exact hc Finset.univ
  refine ⟨hcont, hcf, hoff, ?_, hcomm, ?_⟩
  · intro h
    exact ⟨fun j => GM.cf (w j) h, _, (mul_inv_cancel_left _ _).symm, hsplit h⟩
  · intro U h
    constructor
    · intro hh
      have hh' : ∀ v, GM.cf v h ∈ (if v ∈ im w then U v else GLnLocal.integralGL (v.adicCompletion K) n) := hh
      refine ⟨fun j => GM.cf (w j) h, _, (mul_inv_cancel_left _ _).symm, fun i => ?_, hsplit h, fun v => ?_⟩
      · have := hh' (w i)
        rwa [if_pos (Finset.mem_image_of_mem w (Finset.mem_univ i))] at this
      · by_cases hv : v ∈ im w
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
          rw [hsplit h i]
          exact one_mem _
        · have := hh' v
          rw [if_neg hv] at this
          rw [hmul, hinv, hoff _ v hv, inv_one, one_mul]
          exact this
    · rintro ⟨g, h', rfl, hg, h1, hint⟩
      have hh' : ∀ v, GM.cf v (ι g * h') ∈ (if v ∈ im w then U v else GLnLocal.integralGL (v.adicCompletion K) n) := by
        intro v
        rw [hmul]
        by_cases hv : v ∈ im w
        · rw [if_pos hv]
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
          rw [hcf, h1 i, mul_one]
          exact hg i
        · rw [if_neg hv, hoff g v hv, one_mul]
          exact hint v
      exact hh'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensLaws
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem coef_mem {A B ι : Type} (X : Submodule ℂ (A → ℂ)) (s : Finset ι) (φ : ι → A → ℂ) (ψ : ι → B → ℂ)
    (hψ : LinearIndependent ℂ ψ) (h : ∀ b, (fun a => ∑ i ∈ s, φ i a * ψ i b) ∈ X) : ∀ i ∈ s, φ i ∈ X := by
  intro i hi
  by_contra hn
  obtain ⟨f, hf, hX⟩ := Submodule.exists_le_ker_of_notMem hn
  have h0 : ∑ j ∈ s, f (φ j) • ψ j = 0 := by
    funext b
    have h1 : f (fun a => ∑ i ∈ s, φ i a * ψ i b) = 0 := hX (h b)
    have h2 : (fun a => ∑ i ∈ s, φ i a * ψ i b) = ∑ i ∈ s, ψ i b • φ i := by
      funext a
      simp [Finset.sum_apply, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    simpa [Finset.sum_apply, mul_comm] using h1
  exact hf (linearIndependent_iff'.1 hψ s _ h0 i hi)

private noncomputable def prodMap {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    X₁ ⊗[ℂ] X₂ →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun φ ψ x => φ.1 x.1 * ψ.1 x.2)
    (fun _ _ _ => by funext x; simp [add_mul]) (fun _ _ _ => by funext x; simp [mul_assoc])
    (fun _ _ _ => by funext x; simp [mul_add]) (fun _ _ _ => by funext x; simp [mul_left_comm]))

private theorem prodMap_tmul {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) (φ : X₁) (ψ : X₂) :
    prodMap X₁ X₂ (φ ⊗ₜ ψ) = fun x => φ.1 x.1 * ψ.1 x.2 := by
  simp only [prodMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]

private theorem prodMap_inj {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    Function.Injective (prodMap X₁ X₂) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  let β := Module.Basis.ofVectorSpace ℂ X₂
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right β t
  have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
    β.linearIndependent.map' X₂.subtype (Submodule.ker_subtype _)
  have hc := coef_mem (⊥ : Submodule ℂ (A → ℂ)) c.support (fun i => (c i).1) (fun i => (β i).1) hβ (by
    intro b
    rw [Submodule.mem_bot]
    funext a
    have := congrFun ht (a, b)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Finsupp.sum, map_sum, prodMap_tmul, Finset.sum_apply] using this)
  refine Finset.sum_eq_zero fun i hi => ?_
  have : c i = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 (hc i hi))
  simp [this]

private theorem prodMap_range {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    LinearMap.range (prodMap X₁ X₂) = tensFn X₁ X₂ := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul φ ψ => exact Submodule.subset_span ⟨φ.1, φ.2, ψ.1, ψ.2, prodMap_tmul X₁ X₂ φ ψ⟩
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩
    exact ⟨⟨φ, hφ⟩ ⊗ₜ ⟨ψ, hψ⟩, prodMap_tmul X₁ X₂ _ _⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensLaws :
    ∀ {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)), (∃ e : X₁ ⊗[ℂ] X₂ ≃ₗ[ℂ] tensFn X₁ X₂, ∀ φ ψ x, (e (φ ⊗ₜ ψ)).1 x = φ.1 x.1 * ψ.1 x.2) ∧
      ∀ (F : A × B → ℂ) (d : ℕ) (φ : Fin d → A → ℂ) (ψ : Fin d → B → ℂ), (∀ x, F x = ∑ i, φ i x.1 * ψ i x.2) →
        (∀ b, (fun a => F (a, b)) ∈ X₁) → (∀ a, (fun b => F (a, b)) ∈ X₂) → F ∈ tensFn X₁ X₂ := by
  intro A B X₁ X₂
  refine ⟨⟨(LinearEquiv.ofInjective _ (prodMap_inj X₁ X₂)).trans (LinearEquiv.ofEq _ _ (prodMap_range X₁ X₂)), ?_⟩, ?_⟩
  · intro φ ψ x
    exact congrFun (prodMap_tmul X₁ X₂ φ ψ) x
  · intro F d φ ψ hF h₁ h₂
    let W : Submodule ℂ (B → ℂ) := X₂ ⊓ Submodule.span ℂ (Set.range ψ)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
    have hW : ∀ a, (fun b => F (a, b)) ∈ W := by
      intro a
      refine ⟨h₂ a, ?_⟩
      have : (fun b => F (a, b)) = ∑ i, φ i a • ψ i := by
        funext b
        simp [hF, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let β := Module.finBasis ℂ W
    have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
      β.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
    have hrep : ∀ a b, F (a, b) = ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b := by
      intro a b
      have := congrFun (congrArg Subtype.val (β.sum_repr ⟨_, hW a⟩)) b
      rw [Submodule.coe_sum, Finset.sum_apply] at this
      exact this.symm
    have hc := coef_mem X₁ Finset.univ (fun i a => β.repr ⟨_, hW a⟩ i) (fun i => (β i).1) hβ (by
      intro b
      have : (fun a => ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b) = fun a => F (a, b) := by
        funext a
        exact (hrep a b).symm
      rw [this]
      exact h₁ b)
    have : F = ∑ i, fun x : A × B => β.repr ⟨_, hW x.1⟩ i * (β i).1 x.2 := by
      funext x
      rw [Finset.sum_apply]
      exact hrep x.1 x.2
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨_, hc i (Finset.mem_univ i), _, (β i).2.1, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ConjMemIwahori
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private noncomputable def onSub (ρ : Representation ℂ G V) (Z : Submodule ℂ V)
    (hZ : ∀ g, ∀ v ∈ Z, ρ g v ∈ Z) : Representation ℂ G Z where
  toFun g := (ρ g).restrict (hZ g)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

private theorem cosets_finite [TopologicalSpace G] [IsTopologicalGroup G] (I : Subgroup G)
    (hc : IsCompact (I : Set G)) (ho : IsOpen (I : Set G)) (t : G) :
    {c : G ⧸ I | ∃ u ∈ I, c = QuotientGroup.mk (u * t)}.Finite := by
  haveI := QuotientGroup.discreteTopology ho
  have h : IsCompact ((fun u : G => (QuotientGroup.mk (u * t) : G ⧸ I)) '' (I : Set G)) :=
    hc.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))
  refine h.finite_of_discrete.subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private theorem mem_twKer_of_sum (π : Representation ℂ G V) (I N : Subgroup G) (t : G) (v : V)
    (hv : ∀ u ∈ I, π u v = v) (T : Finset (G ⧸ I))
    (hT : ∀ c, c ∈ T ↔ ∃ u ∈ I, c = QuotientGroup.mk (u * t))
    (hfac : ∀ u ∈ I, ∃ x ∈ N, ∃ b ∈ I, u * t = x * t * b)
    (hnorm : ∀ x ∈ N, t⁻¹ * x * t ∈ N)
    (hsum : ∑ c ∈ T, π c.out v = 0) : v ∈ twKer π N 1 := by
  have key : ∀ c ∈ T, π c.out v - π t v ∈ twKer π N 1 := by
    intro c hc
    obtain ⟨u, hu, rfl⟩ := (hT c).1 hc
    obtain ⟨x, hx, b, hb, e⟩ := hfac u hu
    obtain ⟨i, hi⟩ := QuotientGroup.mk_out_eq_mul I (u * t)
    have h1 : π (QuotientGroup.mk (u * t) : G ⧸ I).out v = π x (π t v) := by
      rw [hi, e, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        Module.End.mul_apply, hv _ i.2, hv _ hb]
    rw [h1]
    exact GlobalTheory.IwahoriInj.sub_mem_twKer hx _
  have h2 : ∑ c ∈ T, (π c.out v - π t v) ∈ twKer π N 1 := Submodule.sum_mem _ key
  rw [Finset.sum_sub_distrib, hsum, zero_sub, neg_mem_iff, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℂ] at h2
  have hne : (T.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, (hT _).2 ⟨1, one_mem _, by rw [one_mul]⟩⟩)
  have h3 : π t v ∈ twKer π N 1 := (Submodule.smul_mem_iff _ hne).1 h2
  have h4 : twKer π N 1 ≤ (twKer π N 1).comap (π t⁻¹) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, w, rfl⟩
    have e : π t⁻¹ (π (h : G) w - w) =
        π (t⁻¹ * h * t) (π t⁻¹ w) - π t⁻¹ w := by
      rw [map_sub, ← Module.End.mul_apply (π (t⁻¹ * h * t)), ← map_mul,
        ← Module.End.mul_apply (π t⁻¹) (π (h : G)), ← map_mul]
      congr 3
      group
    simpa [e] using GlobalTheory.IwahoriInj.sub_mem_twKer (π := π) (hnorm h h.2) (π t⁻¹ w)
  have h5 := h4 h3
  rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul] at h5
  simpa using h5

end Abstract

section Local

open ValuativeRel Matrix

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

private theorem conj_apply (ν : Fin n → ℤ) (g : GL (Fin n) F) (i j : Fin n) :
    (((Cartan.diagPow F n ν)⁻¹ * g * Cartan.diagPow F n ν : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      ((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (ν j - ν i) * (g : Matrix (Fin n) (Fin n) F) i j := by
  have h0 : ((GLnLocal.uniformizer F : 𝒪[F]) : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have e : (((Cartan.diagPow F n ν)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => ((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (-ν i) := rfl
  rw [Units.val_mul, Units.val_mul, e, Cartan.coe_diagPow, mul_diagonal, diagonal_mul,
    sub_eq_add_neg, add_comm, zpow_add₀ h0]
  ring

private theorem conj_mem_iwahori {ν : Fin n → ℤ} (hν : Antitone ν) {b : GL (Fin n) F}
    (hb : b ∈ GLnLocal.iwahori F n)
    (hl : ∀ i j, i < j → (b : Matrix (Fin n) (Fin n) F) i j = 0) :
    (Cartan.diagPow F n ν)⁻¹ * b * Cartan.diagPow F n ν ∈ GLnLocal.iwahori F n := by
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff F n).1 hb
  have hle : ∀ i j, j ≤ i → valuation F
      (((GLnLocal.uniformizer F : 𝒪[F]) : F) ^ (ν j - ν i) * (b : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ((b : Matrix (Fin n) (Fin n) F) i j) := fun i j hij => by
    have hz : 0 ≤ ν j - ν i := sub_nonneg.mpr (hν hij)
    rw [← Int.toNat_of_nonneg hz, zpow_natCast, map_mul, map_pow]
    exact mul_le_of_le_one_left' (pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le _)
  refine (GLnLocal.mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_apply]
    rcases lt_or_ge i j with h | h
    · rw [hl i j h, mul_zero, map_zero]
      exact zero_le'
    · exact (hle i j h).trans (h1 i j)
  · rw [conj_apply]
    exact (hle i j hij.le).trans_lt (h2 i j hij)
  · rw [conj_apply, sub_self, zpow_zero, one_mul]
    exact h3 i

private theorem conj_mem_unipB (ν : Fin n → ℤ) {x : GL (Fin n) F} (hx : x ∈ unipB F (Fin n)) :
    (Cartan.diagPow F n ν)⁻¹ * x * Cartan.diagPow F n ν ∈ unipB F (Fin n) := by
  obtain ⟨h1, h2⟩ := (mem_unipB F).1 hx
  refine (mem_unipB F).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_apply, h1 i j hij, mul_zero]
  · rw [conj_apply, h2 i, sub_self, zpow_zero, one_mul]

private theorem iwahori_le (g : GL (Fin n) F) (hg : g ∈ iwahori F (Fin n)) :
    g ∈ GLnLocal.iwahori F n := by
  obtain ⟨u, hu, rfl⟩ := hg
  refine ⟨u, ?_, ?_⟩
  · refine Subgroup.mem_comap.2 ((GroundTheory.Automorphic.mem_borel_iff _).2 fun i j hij => ?_)
    rw [GLnLocal.residueReduction_apply]
    exact (GlobalTheory.SmGL.mem_borel _).1 hu i j hij
  · refine Units.ext ?_
    ext i j
    rfl

private theorem factor {ν : Fin n → ℤ} (hν : Antitone ν) (u : GL (Fin n) F)
    (hu : u ∈ GLnLocal.iwahori F n) :
    ∃ x ∈ unipB F (Fin n), ∃ b ∈ GLnLocal.iwahori F n,
      u * Cartan.diagPow F n ν = x * Cartan.diagPow F n ν * b := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id u hu
  obtain ⟨hxP, hx1⟩ := Parabolic.mem_unipotentRadical.1 hx.2
  have hyL := Parabolic.mem_levi.1 hy.2
  obtain ⟨hz0, -⟩ := Parabolic.mem_oppositeUnipotentRadical.1 hz.2
  refine ⟨x, (mem_unipB F).2 ⟨fun i j hij => hxP hij, fun i => ?_⟩, _,
    mul_mem (conj_mem_iwahori hν hy.1 fun i j h => hyL i j h.ne)
      (conj_mem_iwahori hν hz.1 fun i j h => hz0 i j h), ?_⟩
  · simpa using hx1 i i rfl
  · group

private theorem local_inj {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (Z : Submodule ℂ V) (hZ : ∀ g, ∀ v ∈ Z, ρ g v ∈ Z)
    (hsm : ∀ v ∈ Z, IsOpen {g | ρ g v = v}) (ν : Fin n → ℤ) (hν : Antitone ν) (v : V) (hvZ : v ∈ Z)
    (hv : ∀ u ∈ GLnLocal.iwahori F n, ρ u v = v)
    (h0 : hopR ρ (GLnLocal.iwahori F n) (Cartan.diagPow F n ν) v = 0) : v = 0 := by
  have hS := cosets_finite (GLnLocal.iwahori F n) (GLnLocal.isCompact_iwahori F n)
    (GLnLocal.isOpen_iwahori F n) (Cartan.diagPow F n ν)
  have h1 : ∑ c ∈ hS.toFinset, ρ c.out v = 0 := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hS]
    exact h0
  let π := onSub ρ Z hZ
  have hπ : ∀ (g : GL (Fin n) F) (a : Z), ((π g a : Z) : V) = ρ g a := fun _ _ => rfl
  have hsmooth : GlobalTheory.PRep.IsSmooth π := fun a => by
    have : {g : GL (Fin n) F | π g a = a} = {g | ρ g a = a} := by
      ext g
      exact Subtype.ext_iff
    rw [this]
    exact hsm a a.2
  have hker : (⟨v, hvZ⟩ : Z) ∈ twKer π (unipB F (Fin n)) 1 := by
    refine mem_twKer_of_sum π (GLnLocal.iwahori F n) _ (Cartan.diagPow F n ν) _
      (fun u hu => Subtype.ext (hv u hu)) hS.toFinset (fun c => by simp)
      (factor hν) (fun x hx => conj_mem_unipB ν hx) (Subtype.ext ?_)
    rw [Submodule.coe_sum]
    exact h1
  have hfix : (⟨v, hvZ⟩ : Z) ∈ fixed π (iwahori F (Fin n)) :=
    GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => Subtype.ext (hv h (iwahori_le h hh))
  have h2 := (injective_iff_map_eq_zero _).1
    (GlobalTheory.IwahoriInj.iwahoriProj_injective F (Fin n) Z π hsmooth) ⟨_, hfix⟩
    (Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 hker))
  exact congrArg (fun a : fixed π (iwahori F (Fin n)) => ((a : Z) : V)) h2

end Local

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.iwInj :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (w : Pl K) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Gw n w) V) (Z : Submodule ℂ V), (∀ g, ∀ v ∈ Z, ρ g v ∈ Z) →
      (∀ v ∈ Z, IsOpen {g | ρ g v = v}) → ∀ ν : Fin n → ℤ, Antitone ν → ∀ v ∈ Z, (∀ u ∈ GLnLocal.iwahori (w.adicCompletion K) n, ρ u v = v) →
        hopR ρ (GLnLocal.iwahori (w.adicCompletion K) n) (Cartan.diagPow (w.adicCompletion K) n ν) v = 0 → v = 0 := by
  intro K _ _ n w V _ _ ρ Z hZ hsm ν hν v hvZ hv h0
  exact UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IwahoriInjection.local_inj ρ Z hZ hsm ν hν v hvZ hv h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopProd
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

private def dbl {G : Type} [Group G] (U : Subgroup G) (g : G) : Set (G ⧸ U) :=
  {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}

private theorem dbl_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
    (hU : CO U) (g : G) : (dbl U g).Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hU.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

private theorem act_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {U : Subgroup G} {v : V} (hv : ∀ u ∈ U, ρ u v = v) {x y : G}
    (h : (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk y) : ρ x v = ρ y v := by
  have h1 := hv _ (QuotientGroup.eq.1 h)
  calc ρ x v = ρ x (ρ (x⁻¹ * y) v) := by rw [h1]
    _ = ρ y v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

variable {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)]

private theorem mk_eq (U : ∀ i, Subgroup (G i)) (x y : ∀ i, G i) :
    (QuotientGroup.mk x : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk y ↔
      ∀ j, (QuotientGroup.mk (x j) : G j ⧸ U j) = QuotientGroup.mk (y j) := by
  simp [QuotientGroup.eq, Subgroup.mem_pi]

private noncomputable def pr (U : ∀ i, Subgroup (G i)) (j : Fin r) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : G j ⧸ U j :=
  QuotientGroup.mk (c.out j)

private theorem pr_mk (U : ∀ i, Subgroup (G i)) (j : Fin r) (x : ∀ i, G i) :
    pr U j (QuotientGroup.mk x) = QuotientGroup.mk (x j) :=
  (mk_eq U _ _).1 (QuotientGroup.out_eq' _) j

private theorem pr_ext (U : ∀ i, Subgroup (G i)) {c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U}
    (h : ∀ j, pr U j c = pr U j d) : c = d := by
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
  exact (mk_eq U _ _).2 h

private theorem mem_dbl (U : ∀ i, Subgroup (G i)) (g : ∀ i, G i) (c : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    c ∈ dbl (Subgroup.pi Set.univ U) g ↔ ∀ j, pr U j c ∈ dbl (U j) (g j) := by
  constructor
  · rintro ⟨u, hu, rfl⟩ j
    exact ⟨u j, hu j trivial, pr_mk U j _⟩
  · intro h
    choose u hu he using h
    exact ⟨u, fun j _ => hu j, pr_ext U fun j => by rw [pr_mk]; exact he j⟩

private theorem mem_dbl_one {H : Type} [Group H] (U : Subgroup H) (c : H ⧸ U) :
    c ∈ dbl U 1 ↔ c = QuotientGroup.mk 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [QuotientGroup.eq] using hu
  · rintro rfl
    exact ⟨1, U.one_mem, by simp⟩

private noncomputable def glue (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) :
    (∀ i, G i) ⧸ Subgroup.pi Set.univ U :=
  QuotientGroup.mk (Pi.mulSingle i (c.out i) * d.out)

private theorem pr_glue_same (U : ∀ i, Subgroup (G i)) (i : Fin r) (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U)
    (hd : pr U i d = QuotientGroup.mk 1) : pr U i (glue U i c d) = pr U i c := by
  rw [glue, pr_mk]
  have := QuotientGroup.eq.1 hd
  simpa [pr, QuotientGroup.eq] using this

private theorem pr_glue_ne (U : ∀ i, Subgroup (G i)) {i j : Fin r} (h : j ≠ i)
    (c d : (∀ i, G i) ⧸ Subgroup.pi Set.univ U) : pr U j (glue U i c d) = pr U j d := by
  rw [glue, pr_mk]
  simp [pr, Pi.mulSingle_eq_of_ne h]

private theorem hop_mul [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (hU : ∀ i, CO (U i))
    (i : Fin r) (x : G i) (b : ∀ i, G i) (hb : b i = 1) (v : V) (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v)
    (hw : ∀ u ∈ Subgroup.pi Set.univ U, ρ u (hopR ρ (Subgroup.pi Set.univ U) b v) = hopR ρ (Subgroup.pi Set.univ U) b v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x * b) v =
      hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
  have hW : CO (Subgroup.pi Set.univ U) :=
    ⟨isCompact_univ_pi fun j => (hU j).1, isOpen_set_pi Set.finite_univ fun j _ => (hU j).2⟩
  have hs : ∀ g w, hopR ρ (Subgroup.pi Set.univ U) g w = ∑ c ∈ (dbl_finite hW g).toFinset, ρ c.out w :=
    fun g w => finsum_mem_eq_finite_toFinset_sum _ (dbl_finite hW g)
  have ha : ∀ c ∈ dbl (Subgroup.pi Set.univ U) (Pi.mulSingle i x), ∀ j, j ≠ i → pr U j c = QuotientGroup.mk 1 := by
    intro c hc j hj
    have := (mem_dbl U _ c).1 hc j
    rwa [Pi.mulSingle_eq_of_ne hj, mem_dbl_one] at this
  have hb' : ∀ d ∈ dbl (Subgroup.pi Set.univ U) b, pr U i d = QuotientGroup.mk 1 := by
    intro d hd
    have := (mem_dbl U _ d).1 hd i
    rwa [hb, mem_dbl_one] at this
  have h1 : hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i x) (hopR ρ (Subgroup.pi Set.univ U) b v) =
      ∑ p ∈ (dbl_finite hW (Pi.mulSingle i x)).toFinset ×ˢ (dbl_finite hW b).toFinset,
        ρ (glue U i p.1 p.2).out v := by
    rw [hs (Pi.mulSingle i x), Finset.sum_product]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Set.Finite.mem_toFinset] at hc
    have e : ρ c.out (hopR ρ (Subgroup.pi Set.univ U) b v) =
        ρ (Pi.mulSingle i (c.out i)) (hopR ρ (Subgroup.pi Set.univ U) b v) := by
      refine act_congr ρ hw ((mk_eq U _ _).2 fun j => ?_)
      by_cases hj : j = i
      · subst hj; simp
      · rw [Pi.mulSingle_eq_of_ne hj]; exact ha c hc j hj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, hs b, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact act_congr ρ hv (QuotientGroup.out_eq' _).symm
  rw [h1, hs]
  symm
  refine Finset.sum_bij (fun p _ => glue U i p.1 p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨c, d⟩ hp
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp ⊢
    refine (mem_dbl U _ _).2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [pr_glue_same U j c d (hb' d hp.2), Pi.mul_apply, hb, mul_one]
      exact (mem_dbl U _ _).1 hp.1 j
    · rw [pr_glue_ne U hj, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul]
      exact (mem_dbl U _ _).1 hp.2 j
  · rintro ⟨c, d⟩ hp ⟨c', d'⟩ hp' h
    simp only [Finset.mem_product, Set.Finite.mem_toFinset] at hp hp'
    have h' : glue U i c d = glue U i c' d' := h
    refine Prod.ext (pr_ext U fun j => ?_) (pr_ext U fun j => ?_)
    · by_cases hj : j = i
      · subst hj
        rw [← pr_glue_same U j c d (hb' d hp.2), h', pr_glue_same U j c' d' (hb' d' hp'.2)]
      · rw [ha c hp.1 j hj, ha c' hp'.1 j hj]
    · by_cases hj : j = i
      · subst hj
        rw [hb' d hp.2, hb' d' hp'.2]
      · rw [← pr_glue_ne U hj c d, h', pr_glue_ne U hj]
  · intro e he
    rw [Set.Finite.mem_toFinset, mem_dbl] at he
    have hd : pr U i (QuotientGroup.mk (Function.update e.out i 1)) = QuotientGroup.mk 1 := by
      rw [pr_mk, Function.update_self]
    refine ⟨(QuotientGroup.mk (Pi.mulSingle i (e.out i)), QuotientGroup.mk (Function.update e.out i 1)), ?_, ?_⟩
    · simp only [Finset.mem_product, Set.Finite.mem_toFinset, mem_dbl]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [Pi.mul_apply, hb, mul_one] at this
          rw [pr_mk, Pi.mulSingle_eq_same j (Quotient.out e j)]
          exact this
        · rw [pr_mk, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, mem_dbl_one]
      · have := he j
        by_cases hj : j = i
        · subst hj
          rw [hd, hb, mem_dbl_one]
        · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul] at this
          rw [pr_mk, Function.update_of_ne hj]
          exact this
    · refine pr_ext U fun j => ?_
      by_cases hj : j = i
      · subst hj
        rw [pr_glue_same U j _ _ hd, pr_mk, Pi.mulSingle_eq_same]
        rfl
      · rw [pr_glue_ne U hj, pr_mk, Function.update_of_ne hj]
        rfl

private theorem hop_one {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    {U : Subgroup H} {v : V} (hv : ∀ u ∈ U, ρ u v = v) : hopR ρ U 1 v = v := by
  have h : dbl U 1 = {QuotientGroup.mk 1} := Set.ext fun c => mem_dbl_one U c
  change ∑ᶠ c ∈ dbl U 1, ρ c.out v = v
  rw [h, finsum_mem_singleton, act_congr ρ hv (QuotientGroup.out_eq' _), map_one, Module.End.one_apply]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.HopfProductGluing in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.hopProd :
    ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (Q : Submodule ℂ V), (∀ i, CO (U i)) →
      (∀ v ∈ Q, ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) → (∀ i g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i g) v ∈ Q) →
      ∀ g, ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
  intro r G _ _ _ V _ _ ρ U Q hU hfix hone
  have key : ∀ s : Finset (Fin r), ∀ g : ∀ i, G i, (∀ j, j ∉ s → g j = 1) →
      ∀ v ∈ Q, hopR ρ (Subgroup.pi Set.univ U) g v ∈ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg v hv
      have : g = 1 := funext fun j => hg j (Finset.notMem_empty j)
      rw [this, hop_one ρ (hfix v hv)]
      exact hv
    | insert i s hi ih =>
      intro g hg v hv
      have hb : hopR ρ (Subgroup.pi Set.univ U) (Function.update g i 1) v ∈ Q := by
        refine ih _ (fun j hj => ?_) v hv
        by_cases hji : j = i
        · subst hji; exact Function.update_self ..
        · rw [Function.update_of_ne hji]
          exact hg j (by simp [hji, hj])
      have e : g = Pi.mulSingle i (g i) * Function.update g i 1 := by
        funext j
        by_cases hji : j = i
        · subst hji; simp
        · simp [Pi.mulSingle_eq_of_ne hji, Function.update_of_ne hji]
      rw [e, hop_mul ρ U hU i (g i) _ (Function.update_self ..) v (hfix v hv) (hfix _ hb)]
      exact hone i _ _ hb
  exact fun g => key Finset.univ g (fun j hj => absurd (Finset.mem_univ j) hj)
end
