module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ZSimple
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.GalLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AlgTrace

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HeckeSimple
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private lemma map_zero_eq_one_of_additive_to_group {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ Γ V)
    (Z : Submodule ℂ V) (hZ : ∀ z ∈ Z, ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z) (w : V)
    (hw : w ∈ Submodule.span ℂ {x | ∃ u : Γ, ∃ z ∈ Z, x = σ u z - z}) (hfix : ∀ u, σ u w = w) : w = 0 := by
  have key : ∃ N : Subgroup Γ, N.FiniteIndex ∧ ∀ (N' : Subgroup Γ) [Fintype (Γ ⧸ N')], N' ≤ N → N'.Normal →
      ∑ c : Γ ⧸ N', σ c.out w = 0 := by
    clear hfix
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, z, hz, rfl⟩ := hx
      obtain ⟨N, hN, hNz⟩ := hZ z hz
      refine ⟨N, hN, fun N' _ hle hn => ?_⟩
      simp only [map_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      refine Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) _ _ fun c => ?_
      obtain ⟨n, hn'⟩ := QuotientGroup.mk_out_eq_mul N' (c.out * u)
      have h1 : (Equiv.mulRight (QuotientGroup.mk u : Γ ⧸ N')) c = QuotientGroup.mk (c.out * u) := by
        simp
      rw [h1, hn', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hNz n (hle n.2)]
    | zero => exact ⟨⊤, inferInstance, fun N' _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      obtain ⟨N₂, h₂, k₂⟩ := hy
      refine ⟨N₁ ⊓ N₂, inferInstance, fun N' _ hle hn => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [k₁ N' (hle.trans inf_le_left) hn, k₂ N' (hle.trans inf_le_right) hn, add_zero]
    | smul a x _ hx =>
      obtain ⟨N₁, h₁, k₁⟩ := hx
      refine ⟨N₁, h₁, fun N' _ hle hn => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, k₁ N' hle hn, smul_zero]
  obtain ⟨N, hN, k⟩ := key
  letI : Fintype (Γ ⧸ N.normalCore) := Fintype.ofFinite _
  have h := k N.normalCore N.normalCore_le inferInstance
  simp only [hfix, Finset.sum_const, Finset.card_univ] at h
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h
  exact h.resolve_left (by exact_mod_cast Fintype.card_ne_zero)

private lemma finite_translates_double_coset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : CO U) (g : G) :
    {c : G ⧸ U | ∃ u ∈ U, c = QuotientGroup.mk (u * g)}.Finite := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ U) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have := (hU.1.image hc).finite_of_discrete
  refine this.subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.heckeSimple :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (Z : Submodule ℂ V) (U : Subgroup G), CO U → SimpleIn ρ Z → (∀ v ∈ Z, IsOpen {g | ρ g v = v}) →
      ∀ Q ≤ Z, (∀ v ∈ Q, ∀ u ∈ U, ρ u v = v) → (∀ g, ∀ v ∈ Q, hopR ρ U g v ∈ Q) → Q = ⊥ ∨ ∀ v ∈ Z, (∀ u ∈ U, ρ u v = v) → v ∈ Q := by
  intro G _ _ _ V _ _ ρ Z U hU hS hsm Q hQZ hQfix hQhop
  by_cases hQ : Q = ⊥
  · exact Or.inl hQ
  right
  let σ : Representation ℂ U V := ρ.comp U.subtype
  have hσ : ∀ (u : U) (x : V), σ u x = ρ u x := fun _ _ => rfl
  set W : Submodule ℂ V := Submodule.span ℂ {x | ∃ u : U, ∃ z ∈ Z, x = σ u z - z} with hW
  have hZN : ∀ z ∈ Z, ∃ N : Subgroup U, N.FiniteIndex ∧ ∀ n ∈ N, σ n z = z := by
    intro z hz
    let N : Subgroup U :=
      { carrier := {n | σ n z = z}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.1
    have ho : IsOpen (N : Set U) := (hsm z hz).preimage continuous_subtype_val
    haveI := N.quotient_finite_of_isOpen ho
    exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun n hn => hn⟩
  have htr : ∀ g, ∀ q ∈ Q, ρ g q ∈ Q ⊔ W := by
    intro g q hq
    have hfin := finite_translates_double_coset U hU g
    have h1 := hQhop g q hq
    unfold hopR at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have h2 : ∑ c ∈ hfin.toFinset, (ρ c.out q - ρ g q) ∈ W := by
      refine W.sum_mem fun c hc => ?_
      obtain ⟨u, hu, rfl⟩ := hfin.mem_toFinset.mp hc
      obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul U (u * g)
      refine Submodule.subset_span ⟨⟨u, hu⟩, ρ g q, hS.1 g q (hQZ hq), ?_⟩
      rw [hn, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hQfix q hq n n.2, hσ]
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    have h3 := (Q ⊔ W).sub_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
    rw [sub_sub_cancel] at h3
    have hne : ((hfin.toFinset.card : ℕ) : ℂ) ≠ 0 := by
      have : hfin.toFinset.Nonempty := ⟨QuotientGroup.mk (1 * g), hfin.mem_toFinset.mpr ⟨1, U.one_mem, rfl⟩⟩
      exact_mod_cast this.card_ne_zero
    exact ((Q ⊔ W).smul_mem_iff hne).mp h3
  set T : Submodule ℂ V := Submodule.span ℂ {x | ∃ g : G, ∃ q ∈ Q, x = ρ g q} with hT
  have hTZ : T ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact hS.1 g q (hQZ hq)
  have hTst : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    have : T.map (ρ g) ≤ T := by
      rw [hT, Submodule.map_span_le]
      rintro x ⟨g', q, hq, rfl⟩
      exact Submodule.subset_span ⟨g * g', q, hq, by rw [map_mul, Module.End.mul_apply]⟩
    exact this ⟨v, hv, rfl⟩
  have hQT : Q ≤ T := fun q hq => Submodule.subset_span ⟨1, q, hq, by simp⟩
  have hTeq : T = Z := (hS.2 T hTZ hTst).resolve_left fun h => hQ (le_bot_iff.mp (h ▸ hQT))
  have hTle : T ≤ Q ⊔ W := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨g, q, hq, rfl⟩
    exact htr g q hq
  intro v hv hvfix
  obtain ⟨q, hq, w, hw, rfl⟩ := Submodule.mem_sup.mp (hTle (hTeq ▸ hv))
  have hw0 : w = 0 := by
    refine map_zero_eq_one_of_additive_to_group σ Z hZN w hw fun u => ?_
    have := hvfix u u.2
    rw [map_add (f := _), hQfix q hq u u.2] at this
    exact add_left_cancel this
  simpa [hw0] using hq
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IrreducibleCuspidalWeightComponent
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irreducible_cuspidal_weight_component {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K (2 + 2)))
    [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hP : Pair μ₂ τ₁ τ₂)
    {κ e κ₂ p₁ p₂ k₀} (hA : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (hw : Function.Injective w)
    (U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)) (hU : Lev U) (D : TypeDat K (2 + 2)) (hD : IsTy D κ e (levOn (im w) U))
    (d : ℕ) (A : Line μ τ₁ τ₂ D d) (P : Submodule ℂ (Eu d))
    (hst : ∀ v ∈ im w, ∀ (g : Gw (2 + 2) v) M, HeckeAt A (levOn (im w) U) (AdelicGLn.localEmbedding v g) M → ∀ x ∈ P, M x ∈ P) :
    P = ⊥ ∨ P = ⊤ := by
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (2 + 2) w hw
  obtain ⟨-, hc1, hc2, -, -, hlev⟩ := hemb ι hι
  have hcf1 : ∀ v : Pl K, GM.cf v (1 : FA K (2 + 2)) = 1 := by
    intro v
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have h := hc1 1 i
      rwa [map_one] at h
    · have h := hc2 1 v hv
      rwa [map_one] at h
  have hinU : ∀ u ∈ Subgroup.pi Set.univ (fun i => U (w i)), ι u ∈ levOn (im w) U := fun u hu =>
    (hlev U _).2 ⟨u, 1, (mul_one _).symm, fun i => hu i trivial, fun i => hcf1 _, fun v => by rw [hcf1]; exact one_mem _⟩
  obtain ⟨-, hfl, hinj, -⟩ := secTr μ₂ τ₁ τ₂ κ e hA.idem
  obtain ⟨hZ, hZ'⟩ := zMem μ₂ τ₁ τ₂ κ e hA.idem
  have hle := (levLaws (2 + 2) (im w)).1
  have hsimple := zSimple μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA w ι hw hι
  have hex := (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hA.idem (im w) U hU D hD d A).1
  let Φ : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ) :=
    { toFun := fun v => flat 0 (A.sec v)
      map_add' := fun a b => by funext x; simp [flat, mul_add]
      map_smul' := fun c a => by funext x; simp [flat, mul_left_comm] }
  have hΦ : ∀ v, Φ v = flat 0 (A.sec v) := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun a b h => A.inj (hinj _ _ h)
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ FixA κ e (A.sec v) ∧ FixF (levOn (im w) U) (A.sec v) := fun v => by
    obtain ⟨h1, h2⟩ := (A.onto _).1 (LinearMap.mem_range_self A.sec v)
    exact ⟨h1, (hD.fix _ h1.cont).1 h2⟩
  have hfixΦ : ∀ v, FixF (levOn (im w) U) (Φ v) := fun v =>
    ((hfl _ (hsec v).1.cont).2 _ (hle U hU).2).2 (hsec v).2.2
  have hmem : ∀ v, Φ v ∈ Zs τ₁ τ₂ κ e (im w) := fun v =>
    (hZ _ _).2 ⟨_, (hsec v).1, (hsec v).2.1, ⟨U, hU, (hsec v).2.2⟩, rfl⟩
  have hCO : ∀ i, CO (U (w i)) := fun i => (hU (w i)).1
  have hCOpi : CO (Subgroup.pi Set.univ fun i => U (w i)) := by
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_pi]; exact isCompact_univ_pi fun i => (hCO i).1
    · rw [Subgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (hCO i).2
  have hrS : ∀ g (φ : G1 K (2 + 2) → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g)) := fun _ _ _ => rfl
  have hQfix : ∀ φ ∈ P.map Φ, ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u φ = φ := by
    rintro _ ⟨v, -, rfl⟩ u hu
    funext x
    rw [hrS]
    exact hfixΦ v _ (hinU u hu) x
  have hQhop : ∀ g, ∀ φ ∈ P.map Φ, hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ ∈ P.map Φ := by
    refine hopProd (rS ι) (fun i => U (w i)) (P.map Φ) hCO hQfix ?_
    rintro i g _ ⟨v, hv, rfl⟩
    obtain ⟨M, hM, -⟩ := hex (AdelicGLn.localEmbedding (w i) g)
    refine ⟨M v, hst (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)) g M hM v hv, ?_⟩
    rw [← hopEmb (2 + 2) w ι hw hι U hU _ (hfixΦ v), hι i g]
    exact hM v
  rcases heckeSimple (rS ι) (Zs τ₁ τ₂ κ e (im w)) _ hCOpi hsimple (fun φ hφ => (hZ' w ι hw hι φ hφ).1) (P.map Φ)
    (by rintro _ ⟨v, -, rfl⟩; exact hmem v) hQfix hQhop with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => hΦinj ?_
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h _ ⟨v, hv, rfl⟩
  · right
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u (Φ v) = Φ v := by
      intro u hu
      funext x
      rw [hrS]
      exact hfixΦ v _ (hinU u hu) x
    obtain ⟨v', hv', he⟩ := h _ (hmem v) hv
    rwa [← hΦinj he]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irrW :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IrrW := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hA S U hU D hD d A P hst
  obtain ⟨r, w, hw, rfl⟩ : ∃ (r : ℕ) (w : Fin r → Pl K), Function.Injective w ∧ S = im w := by
    refine ⟨S.card, fun i => (S.equivFin.symm i : Pl K), fun a b h => S.equivFin.symm.injective (Subtype.ext h), ?_⟩
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hv => ⟨S.equivFin ⟨v, hv⟩, by simp⟩, fun ⟨i, hi⟩ => hi ▸ (S.equivFin.symm i).2⟩
  exact irreducible_cuspidal_weight_component μ μ₂ τ₁ τ₂ hP hA w hw U hU D hD d A P hst
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.FamScalar
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical InnerProductSpace ComplexOrder

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.famScalar :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2))
          [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ → ∀ κ e κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
          ∀ (S : Finset (Pl K)) (U : ∀ w : Pl K, Subgroup (Gw (2 + 2) w)), Lev U → ∀ (D : TypeDat K (2 + 2)), IsTy D κ e (levOn S U) →
          ∀ (d : ℕ) (A : Line μ τ₁ τ₂ D d) (𝔞 : Amp μ) (φ : TF K (2 + 2)) (c : ℂ) (β : ℝ → Eu d →L[ℂ] Eu d), 𝔞.U = levOn S U →
          (∀ x, φ x = (levOn S U : Set (FA K (2 + 2))).indicator 1 x) → c ≠ 0 → Rop μ (c • UpperTheory.ConvolutionTheory.tens 𝔞.a₀ φ) = 𝔞.A → ActsBy μ A (c • UpperTheory.ConvolutionTheory.tens 𝔞.a₀ φ) β →
          (∃ v g, ∫ y, 𝔞.a₀ y * flat 0 (A.sec v) (g * archP K (2 + 2) y) ∂𝔞.ν ≠ 0) → 0 < d ∧ ∃ x : ℝ, 0 < x ∧ symb β 0 = (x : ℂ) • (1 : Eu d →L[ℂ] Eu d) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A 𝔞 φ c β hU hφ hc hR hA hne
  obtain ⟨v₀, g₀, hI⟩ := hne
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hflat0 : ∀ x, flat 0 (0 : G1 K (2 + 2) → ℂ) x = 0 := fun x => by simp [flat]
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      apply hI
      rw [show v₀ = 0 from Subsingleton.elim _ _, map_zero]
      simp only [hflat0, mul_zero, integral_zero]
    · exact h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨h0, h1, -⟩ := UpperTheory.ConvolutionTheory.evEx K (2 + 2) (by norm_num) μ 𝔞
  have hpos := (posSymb A.J 𝔞.A β hA.1 (hR ▸ hA.2.1) h0 h1).1
  have hcomm : ∀ h M, HeckeAt A (levOn S U) h M → Commute M (symb β 0 : Eu d →ₗ[ℂ] Eu d) := by
    have hA' : ActsBy μ A (UpperTheory.ConvolutionTheory.tens (c • 𝔞.a₀) φ) β := by
      rw [((UpperTheory.ConvolutionTheory.Tf.tensApply K (2 + 2) (by norm_num) 𝔞.a₀ φ).2.2.2.2 c).1]
      exact hA
    exact (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hL.idem S U hLev D hD d A).2.2 _ φ β hφ hA'
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (symb β 0 : Eu d →ₗ[ℂ] Eu d)
  have hE : Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l = ⊤ := by
    refine (irrW K μ μ₂ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hL S U hLev D hD d A _ fun w _ g M hM v hv => ?_).resolve_left hl
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h := LinearMap.congr_fun (hcomm _ M hM).eq v
    simp only [Module.End.mul_apply] at h
    rw [← h, hv, map_smul]
  have hT : ∀ v, symb β 0 v = l • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top : v ∈ Module.End.eigenspace (symb β 0 : Eu d →ₗ[ℂ] Eu d) l)
  have hl0 : 0 ≤ l := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Eu d)
    have hp := ContinuousLinearMap.nonneg_iff_isPositive.1 hpos
    have h2 := hp.inner_nonneg_right v
    rw [hT, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
    have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
    have h3 : 0 ≤ l * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h2
    obtain ⟨a, b⟩ := Complex.nonneg_iff.1 h3
    rw [Complex.re_mul_ofReal] at a
    rw [Complex.im_mul_ofReal] at b
    refine Complex.nonneg_iff.2 ⟨le_of_mul_le_mul_right (by simpa using a) hn, ?_⟩
    exact ((mul_eq_zero.1 (by simpa using b.symm)).resolve_right hn.ne').symm
  have hlne : l ≠ 0 := by
    rintro rfl
    obtain ⟨⟨c', hc', hint, -⟩, -⟩ := tensAmp K (2 + 2) (by norm_num) μ 𝔞 φ (fun x => by rw [hφ, hU])
    have hH : Continuous fun x : G1 K (2 + 2) => Complex.exp ((0 + 2) * (HP 2 2 x : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hpSpec.2.2.2.1))
    have hΘ : Continuous (flat 0 (A.sec v₀)) := hH.mul (hsec v₀).1.cont
    have hfix : FixF 𝔞.U (flat 0 (A.sec v₀)) := by
      refine (((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr μ₂ τ₁ τ₂ κ e hL.idem).2.1 _ (hsec v₀).1.cont).2 𝔞.U 𝔞.le).2 ?_
      rw [hU]
      exact ((hD.fix _ (hsec v₀).1.cont).1 (hsec v₀).2).2
    have e1 := hA.2.2 0 v₀ g₀
    rw [hT, zero_smul, map_zero, hflat0] at e1
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, mul_assoc] at e1
    rw [integral_const_mul, hint _ hΘ hfix g₀] at e1
    exact mul_ne_zero hc (mul_ne_zero (Complex.ofReal_ne_zero.2 hc'.ne') hI) e1
  obtain ⟨a, b⟩ := Complex.nonneg_iff.1 hl0
  have hre : l = ((l.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← b])
  refine ⟨hd, l.re, lt_of_le_of_ne a fun h => hlne (by rw [hre, ← h]; simp), ?_⟩
  ext1 v
  rw [hT, ← hre]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeInj
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem hopR_single {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (∀ i, G i) V) (U : ∀ i, Subgroup (G i)) (i : Fin r) (t : G i) (v : V)
    (hv : ∀ u ∈ Subgroup.pi Set.univ U, ρ u v = v) :
    hopR ρ (Subgroup.pi Set.univ U) (Pi.mulSingle i t) v =
      hopR (ρ.comp (MonoidHom.mulSingle G i)) (U i) t v := by
  have hsing : ∀ {a b : G i}, a⁻¹ * b ∈ U i →
      (Pi.mulSingle i a : ∀ j, G j)⁻¹ * Pi.mulSingle i b ∈ Subgroup.pi Set.univ U := by
    intro a b hab j _
    by_cases hj : j = i
    · subst hj
      simpa using hab
    · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
  let f : G i ⧸ U i → (∀ j, G j) ⧸ Subgroup.pi Set.univ U :=
    Quotient.lift (fun a => (QuotientGroup.mk (Pi.mulSingle i a) : (∀ j, G j) ⧸ Subgroup.pi Set.univ U)) (by
      intro a b hab
      exact QuotientGroup.eq.2 (hsing (QuotientGroup.leftRel_apply.1 hab)))
  have hf : ∀ a : G i, f (QuotientGroup.mk a) = QuotientGroup.mk (Pi.mulSingle i a) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro c c' h
    induction c using QuotientGroup.induction_on with | _ a => ?_
    induction c' using QuotientGroup.induction_on with | _ b => ?_
    rw [hf, hf, QuotientGroup.eq] at h
    have := h i (Set.mem_univ i)
    simpa [QuotientGroup.eq] using this
  unfold hopR
  symm
  refine finsum_mem_eq_of_bijOn f ⟨?_, hinj.injOn, ?_⟩ ?_
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨Pi.mulSingle i u, ?_, ?_⟩
    · intro j _
      by_cases hj : j = i
      · subst hj
        simpa using hu
      · simpa [Pi.mulSingle_eq_of_ne hj] using (U j).one_mem
    · rw [hf, Pi.mulSingle_mul]
  · rintro c ⟨u, hu, rfl⟩
    refine ⟨QuotientGroup.mk (u i * t), ⟨u i, hu i (Set.mem_univ i), rfl⟩, ?_⟩
    rw [hf, QuotientGroup.eq]
    intro j _
    by_cases hj : j = i
    · subst hj
      simp
    · simpa [Pi.mulSingle_eq_of_ne hj] using hu j (Set.mem_univ j)
  · intro c _
    have hc : (QuotientGroup.mk (f c).out : (∀ j, G j) ⧸ Subgroup.pi Set.univ U) = QuotientGroup.mk (Pi.mulSingle i c.out) := by
      rw [QuotientGroup.out_eq', ← hf, QuotientGroup.out_eq']
    have hu := QuotientGroup.eq.1 hc
    calc (ρ.comp (MonoidHom.mulSingle G i)) c.out v
        = ρ ((f c).out * ((f c).out⁻¹ * Pi.mulSingle i c.out)) v := by
          rw [mul_inv_cancel_left]; rfl
      _ = ρ (f c).out (ρ ((f c).out⁻¹ * Pi.mulSingle i c.out) v) := by rw [map_mul]; rfl
      _ = ρ (f c).out v := by rw [hv _ hu]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.heckeInj :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.HeckeInj := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e he S U hU D hD d A w hw hUw ν hν M hM
  obtain ⟨r, w', hinj, rfl⟩ : ∃ (r : ℕ) (w' : Fin r → Pl K), Function.Injective w' ∧ im w' = S := by
    refine ⟨S.card, fun j => (S.equivFin.symm j : Pl K), ?_, ?_⟩
    · intro a b h
      exact S.equivFin.symm.injective (Subtype.ext h)
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        exact (S.equivFin.symm j).2
      · intro hx
        exact ⟨S.equivFin ⟨x, hx⟩, by simp⟩
  obtain ⟨i, rfl⟩ : ∃ i, w' i = w := by simpa [im] using hw
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (K := K) (2 + 2) w' hinj
  obtain ⟨-, -, -, -, -, hmem⟩ := hemb ι hι
  have hlev := (levLaws (K := K) (2 + 2) (im w')).1 U hU
  have hsec := secTr μ₂ τ₁ τ₂ κ e he
  have hz := zMem μ₂ τ₁ τ₂ κ e he
  have hZ2 := hz.2 w' ι hinj hι
  have hflat0 : flat 0 (0 : G1 K (2 + 2) → ℂ) = 0 := by
    funext x
    simp [flat]
  refine (injective_iff_map_eq_zero M).2 fun v hv => ?_
  have hfS : IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := (A.onto _).1 ⟨v, rfl⟩
  have hfix := (hD.fix _ hfS.1.cont).1 hfS.2
  have hFφ : FixF (levOn (im w') U) (flat 0 (A.sec v)) := ((hsec.2.1 _ hfS.1.cont).2 _ hlev.2).2 hfix.2
  have hZ : flat 0 (A.sec v) ∈ Zs τ₁ τ₂ κ e (im w') :=
    (hz.1 _ _).2 ⟨_, hfS.1, hfix.1, ⟨U, hU, hfix.2⟩, rfl⟩
  have hWfix : ∀ u ∈ Subgroup.pi Set.univ (fun j => U (w' j)), rS ι u (flat 0 (A.sec v)) = flat 0 (A.sec v) := by
    intro u hu
    have hin : ι u ∈ levOn (im w') U :=
      (hmem U _).2 ⟨u, 1, by simp, fun j => hu j (Set.mem_univ j), fun j => by simp [GM.cf], fun x => by simp [GM.cf, one_mem]⟩
    funext x
    exact hFφ _ hin x
  have hzero : hopR ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i))
      (GLnLocal.iwahori ((w' i).adicCompletion K) (2 + 2)) (Cartan.diagPow ((w' i).adicCompletion K) (2 + 2) ν)
      (flat 0 (A.sec v)) = 0 := by
    have h1 := hM v
    rw [hv, map_zero, hflat0, ← hι i, hopEmb (2 + 2) w' ι hinj hι U hU _ hFφ,
      hopR_single (rS ι) (fun j => U (w' j)) i _ _ hWfix, hUw] at h1
    exact h1.symm
  have hφ : flat 0 (A.sec v) = 0 :=
    iwInj (2 + 2) (w' i) ((rS ι).comp (MonoidHom.mulSingle (fun j => Gw (2 + 2) (w' j)) i)) (Zs τ₁ τ₂ κ e (im w'))
      (fun g φ hφ => (hZ2 φ hφ).2 _)
      (fun φ hφ => (hZ2 φ hφ).1.preimage (continuous_mulSingle i))
      ν hν _ hZ
      (fun u hu => hWfix _ fun j _ => by
        by_cases hj : j = i
        · subst hj
          simpa [hUw] using hu
        · simpa [Pi.mulSingle_eq_of_ne hj] using (U (w' j)).one_mem)
      hzero
  have hs0 : A.sec v = 0 := hsec.2.2.1 _ _ (hφ.trans hflat0.symm)
  exact A.inj (hs0.trans (map_zero A.sec).symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.ExistsTracePowNe
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem exists_trace_pow_ne {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (R : Module.End ℂ W) (hR : Function.Injective R) : ∃ j : ℕ, LinearMap.trace ℂ W (R ^ (j + 1)) ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : R.charpoly.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff R).1 h0
    exact hm (hR (by rw [hm0, map_zero]))
  have h1 := congrArg (LinearMap.trace ℂ W) (LinearMap.aeval_self_charpoly R)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ', map_add (f := _), map_sum] at h1
  simp only [map_smul, (LinearMap.trace ℂ W).map_zero, h, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, LinearMap.trace_one, smul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact h0 h2
  · exact (Module.finrank_pos (R := ℂ) (M := W)).ne' (by exact_mod_cast h2)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.finTw :
    FinTw := by
  intro W X _ _ _ _ T hc hirr U hU i x hinj
  obtain ⟨c, hc0, H⟩ := UpperTheory.ConvolutionTheory.L1.algTrace W X 1 T
    (by
      intro a b hab y z
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · exact hc y z
      · exact (hc z y).symm
      · exact absurd rfl hab) hirr U hU
  have hcom : ∀ (k : ℕ) (j : Fin 2), j ≠ i → ∀ y, Commute (T i x ^ k) (T j y) := by
    intro k j hj y
    apply Commute.pow_left
    fin_cases i <;> fin_cases j
    · exact absurd rfl hj
    · exact hc x y
    · exact (hc y x).symm
    · exact absurd rfl hj
  rw [Filter.frequently_atTop]
  intro N
  have hN : Function.Injective (T i x ^ N : Module.End ℂ W) := by
    rw [Module.End.coe_pow]
    exact hinj.iterate N
  obtain ⟨j, hj⟩ := exists_trace_pow_ne _ hN
  refine ⟨N * (j + 1), Nat.le_mul_of_pos_right N j.succ_pos, ?_⟩
  rw [H i _ (hcom _), pow_mul]
  exact mul_ne_zero hc0 hj
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section SlopeTestRemainingChoices

private theorem coset_tr {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f) (t : H ≃* H)
    (ht : ∀ g, t (t g) = g) (L : Subgroup G) (hL : ∀ u ∈ L, ∃ u' ∈ L, t (f u) = f u') (h h' : G) (hh : t (f h) = f h')
    (ψ : H → ℂ) (hψ : ∀ u ∈ L, ∀ y, ψ (y * f u) = ψ y) (x : H) :
    ∑ᶠ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h)}, ψ (x * f c.out) =
      ∑ᶠ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h')}, ψ (t (t x * f c.out)) := by
  have hh' : t (f h') = f h := by rw [← hh, ht]
  have dec : ∀ (a : G) (c : G ⧸ L), c = QuotientGroup.mk a → ∃ l ∈ L, c.out = a * l := by
    intro a c hc
    have : (QuotientGroup.mk c.out : G ⧸ L) = QuotientGroup.mk a := by rw [QuotientGroup.out_eq', hc]
    have h2 := QuotientGroup.eq.1 this.symm
    exact ⟨_, h2, by group⟩
  have imgOf : ∀ (p p' : G), t (f p) = f p' → ∀ u ∈ L, ∀ l ∈ L, ∃ g' u' l', u' ∈ L ∧ l' ∈ L ∧ g' = u' * p' * l' ∧ t (f (u * p * l)) = f g' := by
    intro p p' hp u hu l hl
    obtain ⟨u', hu', e1⟩ := hL u hu
    obtain ⟨l', hl', e2⟩ := hL l hl
    exact ⟨_, u', l', hu', hl', rfl, by simp only [map_mul, e1, e2, hp]⟩
  have key : ∀ c ∈ {c : G ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * h)}, ∃ g', t (f c.out) = f g' ∧
      ∃ u' ∈ L, ∃ l' ∈ L, g' = u' * h' * l' := by
    rintro c ⟨u, hu, rfl⟩
    obtain ⟨l, hl, e⟩ := dec _ _ rfl
    obtain ⟨g', u', l', hu', hl', e1, e2⟩ := imgOf h h' hh u hu l hl
    exact ⟨g', by rw [e, e2], u', hu', l', hl', e1⟩
  classical
  let m : G ⧸ L → G ⧸ L := fun c => if hc : ∃ g', t (f c.out) = f g' then QuotientGroup.mk hc.choose else c
  have hm : ∀ c g', t (f c.out) = f g' → m c = QuotientGroup.mk g' := by
    intro c g' hg
    have hc : ∃ g', t (f c.out) = f g' := ⟨g', hg⟩
    have : hc.choose = g' := hf (hc.choose_spec.symm.trans hg)
    simp only [m, dif_pos hc, this]
  refine finsum_mem_eq_of_bijOn m ⟨?_, ?_, ?_⟩ ?_
  · intro c hc
    obtain ⟨g', e, u', hu', l', hl', rfl⟩ := key c hc
    refine ⟨u', hu', ?_⟩
    rw [hm c _ e]
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hl')
  · intro c hc c' hc' e
    obtain ⟨g, eg, -⟩ := key c hc
    obtain ⟨g', eg', -⟩ := key c' hc'
    rw [hm c _ eg, hm c' _ eg'] at e
    obtain ⟨l', hl', e2⟩ := hL _ (QuotientGroup.eq.1 e)
    have e3 : f (c.out⁻¹ * c'.out) = f l' := by
      rw [← e2]
      simp only [map_mul, map_inv, ← eg, ← eg', ht]
    have e4 : c.out⁻¹ * c'.out ∈ L := by rw [hf e3]; exact hl'
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
    exact QuotientGroup.eq.2 e4
  · rintro c' ⟨u', hu', rfl⟩
    obtain ⟨u, hu, e1⟩ := hL u' hu'
    have e0 : t (f (u * h)) = f (u' * h') := by
      have : f (u * h) = t (f (u' * h')) := by simp only [map_mul, e1, hh']
      rw [this, ht]
    refine ⟨QuotientGroup.mk (u * h), ⟨u, hu, rfl⟩, ?_⟩
    obtain ⟨l, hl, e⟩ := dec (u * h) _ rfl
    obtain ⟨l', hl', e2⟩ := hL l hl
    have e3 : t (f (QuotientGroup.mk (u * h) : G ⧸ L).out) = f (u' * h' * l') := by
      rw [e, map_mul, map_mul, e0, e2]
      simp only [map_mul]
    rw [hm _ _ e3]
    exact (QuotientGroup.eq.2 (by simpa [mul_assoc] using L.inv_mem hl')).symm
  · intro c hc
    obtain ⟨g', e, -⟩ := key c hc
    obtain ⟨l, hl, e2⟩ := dec g' (m c) (hm c _ e)
    obtain ⟨l', hl', e3⟩ := hL l hl
    rw [e2, map_mul, map_mul, map_mul, ht, ← e, ht, e3, ← mul_assoc, hψ _ hl']

end SlopeTestRemainingChoices

section Hop

variable {K : Type} [Field K] [NumberField K]

private theorem finite_adele_inclusion_injective {n : ℕ} : Function.Injective (fin1 : FA K n → G1 K n) := by
  intro a b h
  have h2 : ((MultiplicityOne.finProj K n a : G1 K n) : AdelicGLn.AdelicGL K n) = (MultiplicityOne.finProj K n b : G1 K n) :=
    congrArg Subtype.val h
  rw [MultiplicityOne.coe_finProj, MultiplicityOne.coe_finProj] at h2
  have h3 := congrArg (CuspidalSpectrum.finPart K n) h2
  simpa only [map_mul, map_inv, finPart_centralSection, inv_one, mul_one, finPart_finEmb] using h3

private theorem hop_tr {n : ℕ} {μ : Measure (G1 K n)} [μ.IsHaarMeasure] (θ : Twist μ) (hinv : ∀ g, θ.e (θ.e g) = g)
    (L : Subgroup (FA K n)) (hL : ∀ u ∈ L, ∃ u' ∈ L, θ.e (fin1 u) = fin1 u') (h h' : FA K n) (hh : θ.e (fin1 h) = fin1 h')
    (ψ : G1 K n → ℂ) (hψ : FixF L ψ) (x : G1 K n) :
    hop L h ψ x = hop L h' (fun y => ψ (θ.e y)) (θ.e x) :=
  coset_tr (MultiplicityOne.finProj K n) finite_adele_inclusion_injective θ.e.toMulEquiv hinv L hL h h' hh ψ hψ x

private theorem flat_fix {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure]
    {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d) {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ}
    {L : Subgroup (FA K (2 + 2))} (hty : IsTy D κ e L) (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2)) (v : Eu d) :
    FixF L (flat 0 (A.sec v)) := by
  obtain ⟨hs, hD⟩ := (A.onto _).1 ⟨v, rfl⟩
  have hF := ((hty.fix _ hs.cont).1 hD).2
  intro u hu g
  have hk : fin1 u ∈ KG K (2 + 2) := by
    change ((MultiplicityOne.finProj K (2 + 2) u : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup _)
    rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact (hle hu)))]
    exact finEmb_mem_maxCompact (hle hu)
  have hh : HP 2 2 (g * fin1 u) = HP 2 2 g := ((hpSpec (K := K)).2.1 _ hk).2 g
  simp only [flat, hh, hF u hu g]

end Hop

section Lines

variable {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
  {μ : Measure (G1 K (2 + 2))} [μ.IsHaarMeasure] {D : TypeDat K (2 + 2)} {d d' : ℕ}

private theorem flat_tw (θ : Twist μ) (hH : ∀ g, HH (θ.e g) = HH g) (f f' : G1 K (2 + 2) → ℂ)
    (h : ∀ x, f' x = f (θ.e.symm x)) (x : G1 K (2 + 2)) : flat 0 f' x = flat 0 f (θ.e.symm x) := by
  have h1 : HP 2 2 (θ.e.symm x) = HP 2 2 x := by
    have := hH (θ.e.symm x)
    rw [ContinuousMulEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [flat, h1, h]

private theorem exists_heckeAt_transport_of_linearIsometryEquiv (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d') {κ : Measure (archCompact K (2 + 2))}
    {e : archCompact K (2 + 2) → ℂ} {L : Subgroup (FA K (2 + 2))} (hty : IsTy D κ e L)
    (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2)) (θ : Twist μ) (hinv : ∀ g, θ.e (θ.e g) = g)
    (hH : ∀ g, HH (θ.e g) = HH g) (hL : ∀ u ∈ L, ∃ u' ∈ L, θ.e (fin1 u) = fin1 u') (s : Eu d ≃ₗᵢ[ℂ] Eu d')
    (hs : ∀ v x, A'.sec (s v) x = A.sec v (θ.e.symm x)) (h h' : FA K (2 + 2)) (hh : θ.e (fin1 h) = fin1 h')
    (M : Eu d →ₗ[ℂ] Eu d) (hM : HeckeAt A L h M) :
    ∃ M' : Eu d' →ₗ[ℂ] Eu d', HeckeAt A' L h' M' ∧ ∀ v, M' (s v) = s (M v) := by
  have hsy : ∀ y, θ.e.symm y = θ.e y := fun y => θ.e.injective (by rw [ContinuousMulEquiv.apply_symm_apply, hinv])
  refine ⟨(s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d') ∘ₗ M ∘ₗ (s.symm.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d), fun v' => ?_, fun v => ?_⟩
  · obtain ⟨v, rfl⟩ := s.surjective v'
    funext x
    have e1 : ((s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d') ∘ₗ M ∘ₗ (s.symm.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d)) (s v) = s (M v) := by simp
    rw [e1, flat_tw θ hH _ _ (hs (M v)) x, hM v, hop_tr θ hinv L hL h h' hh _ (flat_fix A hty hle v),
      ContinuousMulEquiv.apply_symm_apply]
    congr 1
    funext y
    rw [flat_tw θ hH _ _ (hs v) y, hsy]
  · simp

private theorem hecke_N (hp : Pair μ₂ τ₁ τ₂) [_root_.NumberField.IsTotallyComplex K] (A : Line μ τ₁ τ₂ D d) (A' : Line μ τ₂ τ₁ D d')
    {L : Subgroup (FA K (2 + 2))} (hlev : D.Level L) (hle : L ≤ AdelicGLn.integralFiniteGL K (2 + 2))
    (hu : ∀ h, ∃! M, HeckeAt A L h M) (hu' : ∀ h, ∃! M, HeckeAt A' L h M) (N : Eu d' ≃ₗᵢ[ℂ] Eu d)
    (hN : ∀ (Y : L2 μ →L[ℂ] L2 μ) s s', Act A.J Y s → Act A'.J Y s' → ∀ w, N (s' 0 w) = s 0 (N w))
    (h : FA K (2 + 2)) (M : Eu d →ₗ[ℂ] Eu d) (M' : Eu d' →ₗ[ℂ] Eu d') (hM : HeckeAt A L h M) (hM' : HeckeAt A' L h M')
    (w : Eu d') : N (M' w) = M (N w) := by
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  obtain ⟨Y, hY⟩ : ∃ Y : L2 μ →L[ℂ] L2 μ, Y = (∑ᶠ c ∈ {c : AdelicGLn.FiniteAdelicGL K (2 + 2) ⧸ L | ∃ k ∈ L, c = QuotientGroup.mk (k * h)},
      rhoF μ c.out) ∘L prj (fixF μ L) := ⟨_, rfl⟩
  obtain ⟨⟨s, hs, hsv⟩, -⟩ := cosAct K μ μ₂ τ₁ τ₂ hp D d d' A A' L hlev hle h Y hY
  obtain ⟨⟨s', hs', hsv'⟩, -⟩ := cosAct K μ μ₂ τ₂ τ₁ hp' D d' d A' A L hlev hle h Y hY
  have e1 : M = (s 0 : Eu d →ₗ[ℂ] Eu d) := (hu h).unique hM fun v => funext fun x => hsv 0 v x
  have e2 : M' = (s' 0 : Eu d' →ₗ[ℂ] Eu d') := (hu' h).unique hM' fun v => funext fun x => hsv' 0 v x
  rw [e1, e2]
  exact hN Y s s' hs hs' w

end Lines

section Tr

private theorem gl_surj {R T : Type*} [Field R] [Field T] (f : R →+* T) (hf : Function.Surjective f) {n : ℕ}
    (g : GL (Fin n) T) : ∃ g', mapGL n f g' = g := by
  let e : R ≃+* T := RingEquiv.ofBijective f ⟨f.injective, hf⟩
  refine ⟨Matrix.GeneralLinearGroup.map (e.symm : T →+* R) g, ?_⟩
  ext i j
  exact e.apply_symm_apply _

private theorem trace_step {d d' : ℕ} (N : Eu d' ≃ₗᵢ[ℂ] Eu d) (s : Eu d ≃ₗᵢ[ℂ] Eu d') (u a g : Eu d' →L[ℂ] Eu d')
    (V : Module.End ℂ (Eu d)) (hV : ∀ w, N (u w) = V (N w)) (x : ℝ) (r : ℂ) (ha : a = (x : ℂ) • 1) (hg : g = r • 1) (j : ℕ) :
    LinearMap.trace ℂ (Eu d) ((N.toLinearEquiv : Eu d' →ₗ[ℂ] Eu d) ∘ₗ
      ((eigP a x ∘L (u ^ j) ∘L g : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ (s.toLinearEquiv : Eu d →ₗ[ℂ] Eu d')) =
    r * LinearMap.trace ℂ (Eu d) ((V ^ j) ∘ₗ ((s.toLinearEquiv.trans N.toLinearEquiv : Eu d ≃ₗ[ℂ] Eu d) : Eu d →ₗ[ℂ] Eu d)) := by
  have hpow : ∀ (j : ℕ) (y : Eu d'), N ((u ^ j) y) = (V ^ j) (N y) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, ih, hV, Module.End.mul_apply]
  have hP : ∀ y, eigP a x y = y := by
    intro y
    refine Submodule.starProjection_eq_self_iff.2 ?_
    rw [Module.End.mem_eigenspace_iff, ha]
    simp
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  refine LinearMap.ext fun w => ?_
  change N (eigP a x ((u ^ j) (g (s w)))) = r • (V ^ j) (N (s w))
  rw [hP, hg]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul, hpow]

end Tr

private abbrev Zs (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (Pl E)) : Type :=
  {v : Pl F // ∃ w ∈ S, w.under (𝓞 F) = v}

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.famNe :
    FamNe := by
  intro F E _ _ _ _ _ _ _ _ σ hdeg hgen μ _ θ hθ 𝔢 𝔵 κ e κ₂ p₁ p₂ k₀ hAL S U hU hS heU hty hUθ w₀ hw₀ hI ν hν hUq φ hφ hg hac hBi hne N hN
  obtain ⟨c, hc, ha⟩ := hac
  have hp := 𝔵.pair
  have hp' : Pair (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  have hle : levOn S U ≤ AdelicGLn.integralFiniteGL E (2 + 2) := by
    intro u hu
    refine (AdelicGLn.mem_integralFiniteGL_iff_forall E (2 + 2)).2 fun v => ?_
    have h : finAt v (finEmb E (2 + 2) u) ∈ (if v ∈ S then U v else GLnLocal.integralGL (v.adicCompletion E) (2 + 2)) := hu v
    split_ifs at h
    · exact (hU v).2 h
    · exact h
  have hac := ha
  rw [hg] at hac

  obtain ⟨β, hβ⟩ := convR E μ _ 𝔵.τ₁ 𝔵.τ₂ hp 𝔵.D 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' 𝔢.a 𝔵.a_hecke
  rw [hac] at hβ
  obtain ⟨hd, x, hx, hsym⟩ := famScalar E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e κ₂ p₁ p₂ k₀ hAL S U hU 𝔵.D hty 𝔵.d 𝔵.A 𝔢.toAmp φ c β heU hφ hc
    (by rw [← hac]; exact 𝔢.a_op) hβ hne
  have hAct : Act 𝔵.A.J (Rop μ 𝔢.a) (symb β) := by
    rw [hac]
    exact (actLaws 𝔵.A.J).2.1 _ β hβ.1 hβ.2.1
  have hAct' : Act 𝔵.A'.J (Rop μ 𝔢.a) (symb 𝔵.βa) := (actLaws 𝔵.A'.J).2.1 _ 𝔵.βa 𝔵.a_acts.1 𝔵.a_acts.2.1
  have ha0 : 𝔵.a₀ = (x : ℂ) • 1 := by
    refine ContinuousLinearMap.ext fun w => N.injective ?_
    have := hN _ _ _ hAct hAct' w
    rw [hsym] at this
    change N (symb 𝔵.βa 0 w) = N (((x : ℂ) • (1 : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d')) w)
    rw [this]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_smul]
  have hg0 : symb 𝔵.βg 0 = ((x : ℂ) / c) • 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hsec : 𝔵.A'.sec (𝔵.a₀ v) = 𝔵.A'.sec (c • symb 𝔵.βg 0 v) := by
      funext y
      have e1 := 𝔵.a_acts.2.2 0 v y
      have e2 := 𝔵.g_acts.2.2 0 v y
      have e3 : ∫ g, 𝔢.a g * flat 0 (𝔵.A'.sec v) (y * g) ∂μ = c * ∫ g, 𝔢.g g * flat 0 (𝔵.A'.sec v) (y * g) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp [ha, mul_assoc]
      rw [e1, e2] at e3
      rw [map_smul]
      simp only [flat, Pi.smul_apply, smul_eq_mul] at e3 ⊢
      have hne' := Complex.exp_ne_zero ((0 + 2) * (HP 2 2 y : ℂ))
      apply mul_left_cancel₀ hne'
      rw [show symb 𝔵.βa 0 = 𝔵.a₀ from rfl] at e3
      rw [e3]
      ring
    have h1 := 𝔵.A'.inj hsec
    rw [ha0] at h1
    have h2 : (x : ℂ) • v = c • symb 𝔵.βg 0 v := by simpa using h1
    have h3 : symb 𝔵.βg 0 v = c⁻¹ • (x : ℂ) • v := by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h3]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul, div_eq_inv_mul]

  have HE := heckeEx E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e hAL.idem S U hU 𝔵.D hty 𝔵.d 𝔵.A
  have HE' := heckeEx E μ _ 𝔵.τ₂ 𝔵.τ₁ hp' κ e hAL.idem S U hU 𝔵.D hty 𝔵.d' 𝔵.A'
  choose Mh hMh using fun h => (HE.1 h).exists
  have huniq : ∀ h M, HeckeAt 𝔵.A (levOn S U) h M → M = Mh h := fun h M hM => (HE.1 h).unique hM (hMh h)
  obtain ⟨hinv, -, hsplit⟩ := (galLoc F E σ hdeg hgen (2 + 2) (by norm_num) μ θ).2 hθ
  have hH : ∀ g, HH (θ.e g) = HH g := (galLaws μ _ 𝔵.σ θ 𝔵.θ₂ 𝔵.gal 𝔵.gal₂).2.2.2.2
  have hsp : ∀ z : Zs F E S, GM.Split E z.1 := by
    rintro ⟨_, w, hw, rfl⟩
    exact (hS w hw).1
  choose wv hwv using fun z : Zs F E S => hsplit z.1 (hsp z)
  obtain ⟨hh, hhd⟩ : ∃ hh : Fin 2 → (Σ z : Zs F E S, Gw (2 + 2) z.1) → FA E (2 + 2), ∀ i z g, hh i ⟨z, g⟩ =
      AdelicGLn.localEmbedding (wv z i).1 (mapGL (2 + 2) (completionMap z.1 (wv z i).1) g) :=
    ⟨fun i x => AdelicGLn.localEmbedding (wv x.1 i).1 (mapGL (2 + 2) (completionMap x.1.1 (wv x.1 i).1) x.2), fun _ _ _ => rfl⟩
  have hθh : ∀ i x, θ.e (fin1 (hh i x)) = fin1 (hh (i + 1) x) := by
    rintro i ⟨z, g⟩
    rw [hhd, hhd]
    exact hwv z i g
  have hreach : ∀ w ∈ S, ∀ g : Gw (2 + 2) w, ∃ i x, hh i x = AdelicGLn.localEmbedding w g := by
    intro w hw g
    have hlies : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : Zs F E S, z = ⟨w.under (𝓞 F), w, hw, rfl⟩ := ⟨_, rfl⟩
    have hlies' : w.asIdeal.LiesOver z.1.asIdeal := by rw [hz]; exact hlies
    obtain ⟨i, hi⟩ := (wv z).surjective ⟨w, hlies'⟩
    have H : ∀ g' : Gw (2 + 2) (wv z i).1, ∃ i' x, hh i' x = AdelicGLn.localEmbedding (wv z i).1 g' := by
      intro g'
      obtain ⟨g₀, rfl⟩ := gl_surj _ (hsp z (wv z i)) g'
      exact ⟨i, ⟨z, g₀⟩, hhd i z g₀⟩
    rw [hi] at H
    exact H g
  have hcomm : ∀ x y, Commute (Mh (hh 0 x)) (Mh (hh 1 y)) := by
    rintro ⟨z, g⟩ ⟨z', g'⟩
    rw [hhd, hhd]
    refine HE.2.1 _ _ ?_ _ _ _ _ (hMh _) (hMh _)
    intro heq
    have o1 : (wv z 0).1.under (𝓞 F) = z.1 := HeightOneSpectrum.ext (wv z 0).2.over.symm
    have o2 : (wv z' 1).1.under (𝓞 F) = z'.1 := HeightOneSpectrum.ext (wv z' 1).2.over.symm
    have hz : z = z' := Subtype.ext (o1.symm.trans ((congrArg (HeightOneSpectrum.under (𝓞 F)) heq).trans o2))
    subst hz
    exact absurd ((wv z).injective (Subtype.ext heq)) (by decide)
  have hirr : ∀ P : Submodule ℂ (Eu 𝔵.d), (∀ i x, ∀ w ∈ P, Mh (hh i x) w ∈ P) → P = ⊥ ∨ P = ⊤ := fun P hP =>
    irrW E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e κ₂ p₁ p₂ k₀ hAL S U hU 𝔵.D hty 𝔵.d 𝔵.A P fun w hw g M hM v hv => by
      obtain ⟨i, x', hx'⟩ := hreach w hw g
      rw [← hx'] at hM
      rw [huniq _ _ hM]
      exact hP i x' v hv
  have htw : ∀ i x (w : Eu 𝔵.d), ((𝔵.s.toLinearEquiv.trans N.toLinearEquiv : Eu 𝔵.d ≃ₗ[ℂ] Eu 𝔵.d)) (Mh (hh (i + 1) x) w) =
      Mh (hh i x) ((𝔵.s.toLinearEquiv.trans N.toLinearEquiv : Eu 𝔵.d ≃ₗ[ℂ] Eu 𝔵.d) w) := by
    intro i x' w
    have hi2 : i + 1 + 1 = i := by revert i; decide
    have e1 : θ.e (fin1 (hh (i + 1) x')) = fin1 (hh i x') := by
      have := hθh (i + 1) x'
      rwa [hi2] at this
    obtain ⟨M', hM', hcmp⟩ := exists_heckeAt_transport_of_linearIsometryEquiv 𝔵.A 𝔵.A' hty hle θ hinv hH hUθ 𝔵.s 𝔵.s_sec _ _ e1 _ (hMh _)
    have h2 := hecke_N hp 𝔵.A 𝔵.A' hty.level hle HE.1 HE'.1 N hN _ _ _ (hMh (hh i x')) hM' (𝔵.s w)
    rw [hcmp] at h2
    exact h2

  obtain ⟨⟨s₀, hact, hs₀⟩, -⟩ := (uiwAct E μ _ 𝔵.τ₁ 𝔵.τ₂ hp S U hU 𝔵.D hty.level 𝔵.d 𝔵.d' 𝔵.A 𝔵.A' w₀ hw₀ hI ν)
  have hv0 : 𝔵.v 0 = s₀ := actUniq _ _ _ _ (hUq ▸ 𝔵.v_act 0) hact
  obtain ⟨i₀, x₀, hx₀⟩ := hreach w₀ hw₀ (Cartan.diagPow (w₀.adicCompletion E) (2 + 2) ν)
  have hV : Mh (hh i₀ x₀) = (𝔵.v 0 0 : Eu 𝔵.d →ₗ[ℂ] Eu 𝔵.d) := by
    rw [hv0]
    refine (huniq _ _ ?_).symm
    rw [hx₀]
    exact hs₀
  have hinj : Function.Injective (Mh (hh i₀ x₀)) :=
    heckeInj E μ _ 𝔵.τ₁ 𝔵.τ₂ hp κ e hAL.idem S U hU 𝔵.D hty 𝔵.d 𝔵.A w₀ hw₀ hI ν hν _ (hx₀ ▸ hMh _)
  have hN0 : ∀ w, N (𝔵.u 0 0 w) = Mh (hh i₀ x₀) (N w) := by
    intro w
    rw [hV]
    exact hN _ _ _ (𝔵.v_act 0) (𝔵.u_act 0) w
  haveI : Nontrivial (Eu 𝔵.d) := Module.nontrivial_of_finrank_pos (R := ℂ) (by simpa using hd)
  have hF := finTw (Eu 𝔵.d) _ (fun i x => Mh (hh i x)) hcomm hirr (𝔵.s.toLinearEquiv.trans N.toLinearEquiv) htw i₀ x₀ hinj
  refine ⟨x, hx, hF.mono fun j hj => ?_⟩
  have hxc : (x : ℂ) / c ≠ 0 := div_ne_zero (by exact_mod_cast hx.ne') hc
  have hT := trace_step N 𝔵.s (𝔵.u 0 0) 𝔵.a₀ (symb 𝔵.βg 0) (Mh (hh i₀ x₀)) hN0 x ((x : ℂ) / c) ha0 hg0 j
  change LinearMap.trace ℂ (Eu 𝔵.d) _ ≠ 0
  rw [hT]
  exact mul_ne_zero hxc hj
