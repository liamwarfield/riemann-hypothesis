module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ExistsInjectionIntoL2Cusp
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RestScalar
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.MemOfTranslates
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Abs

variable {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem rep_smul (π : UnitaryRep G H) (γ : G) (d : ℂ) (x : H) : π γ (d • x) = d • π γ x :=
  map_smul (π γ) d x

private theorem cut_abs (π : UnitaryRep G H) (P T : H →L[ℂ] H) {x y z : G} {q : H} {c c' : ℂ}
    (h₁ : ∀ v, P (π x v) = π x (P v)) (h₂ : ∀ v, P (π y v) = π y (P v)) (h₃ : ∀ v, T (π x v) = π x (T v))
    (e₂ : P (π z q) = c • q) (e₃ : T (π y q) = c' • q) : T (P (π (x * (y * z)) q)) = (c * c') • π x q := by
  rw [UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, h₁, h₂, e₂, h₃, rep_smul, map_smul, e₃, rep_smul, rep_smul, smul_smul]

private theorem prj_comm (π : UnitaryRep G H) {A : Submodule ℂ H} (hA : IsClosed (A : Set H)) (γ : G)
    (h₁ : ∀ v ∈ A, π γ v ∈ A) (h₂ : ∀ v ∈ A, π γ⁻¹ v ∈ A) (x : H) : prj A (π γ x) = π γ (prj A x) := by
  have hcl := hA.submodule_topologicalClosure_eq
  have hP : prj A x ∈ A := by
    have : prj A x ∈ A.topologicalClosure := Submodule.starProjection_apply_mem _ x
    rwa [hcl] at this
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [hcl]
    exact h₁ _ hP
  · intro f hf
    rw [hcl] at hf
    have e : f = π γ (π γ⁻¹ f) := by
      rw [← UnitaryRep.map_mul_apply, mul_inv_cancel, UnitaryRep.map_one_apply]
    rw [e, ← map_sub, UnitaryRep.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero (K := A.topologicalClosure) x _ (by rw [hcl]; exact h₂ f hf)

private theorem mem_of_translates (π : UnitaryRep G H) {τ Q : Submodule ℂ H} (hτc : IsClosed (τ : Set H))
    (hτi : ∀ g, ∀ v ∈ τ, π g v ∈ τ)
    (hirr : ∀ ρ : Submodule ℂ H, ρ ≤ τ → IsClosed (ρ : Set H) → (∀ g, ∀ v ∈ ρ, π g v ∈ ρ) → ρ = ⊥ ∨ ρ = τ)
    (hQc : IsClosed (Q : Set H)) (E : H →L[ℂ] H) {q : H} (hqτ : q ∈ τ) (hq0 : q ≠ 0) (key : ∀ γ, E (π γ q) ∈ Q)
    {v : H} (hv : v ∈ τ) (hE : E v = v) : v ∈ Q := by
  let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun γ => π γ q)
  have hSinv : π.IsInvariant S := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact S.smul_mem a hx
  have hSτ : S ≤ τ := Submodule.span_le.2 (by
    rintro _ ⟨γ, rfl⟩
    exact hτi _ _ hqτ)
  have hclτ : S.topologicalClosure ≤ τ := Submodule.topologicalClosure_minimal _ hSτ hτc
  have hqS : q ∈ S.topologicalClosure :=
    S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
  have hSeq : S.topologicalClosure = τ := by
    rcases hirr _ hclτ S.isClosed_topologicalClosure (fun g v hv => hSinv.topologicalClosure g v hv) with h0 | h1
    · exfalso
      rw [h0] at hqS
      exact hq0 (by simpa using hqS)
    · exact h1
  have hES : ∀ x ∈ S, E x ∈ Q := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ, rfl⟩ := hx
      exact key γ
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact Q.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Q.smul_mem a hx
  have hvc : v ∈ closure (S : Set H) := by
    have : v ∈ S.topologicalClosure := by rw [hSeq]; exact hv
    exact this
  have hm := map_mem_closure E.continuous hvc (t := (Q : Set H)) (fun x hx => hES x hx)
  rw [hQc.closure_eq, hE] at hm
  exact hm

end Abs

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

private theorem integrable_orbit {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ} (hI : IdemA κ e) (v : L2 μ) :
    Integrable (fun k => e k • rightRegularRep (Gam K n) μ (arc1 k) v) κ := by
  haveI := hI.haar.prob
  haveI : CompactSpace (archCompact K n) := (levLaws (K := K) n ∅).2.2.2.2.1
  have hc : Continuous fun k : archCompact K n => e k • rightRegularRep (Gam K n) μ (arc1 k) v :=
    hI.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp (levLaws (K := K) n ∅).2.2.2.1)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem exists_clm {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ} (hI : IdemA κ e) :
    ∃ T : L2 μ →L[ℂ] L2 μ, ∀ v, T v = pOp μ κ e v := by
  haveI := hI.haar.prob
  haveI : CompactSpace (archCompact K n) := (levLaws (K := K) n ∅).2.2.2.2.1
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hI.cont.continuousOn
  let T : L2 μ →ₗ[ℂ] L2 μ :=
    { toFun := pOp μ κ e
      map_add' := fun x y => by
        unfold pOp
        rw [← integral_add (integrable_orbit μ hI x) (integrable_orbit μ hI y)]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun c x => by
        unfold pOp
        rw [RingHom.id_apply, ← integral_smul]
        simp only [map_smul, smul_comm c] }
  refine ⟨T.mkContinuous C fun v => ?_, fun v => rfl⟩
  have h := norm_integral_le_of_norm_le_const (μ := κ) (C := C * ‖v‖)
    (f := fun k => e k • rightRegularRep (Gam K n) μ (arc1 k) v) (Eventually.of_forall fun k => by
      rw [norm_smul]
      have h1 : ‖rightRegularRep (Gam K n) μ (arc1 k) v‖ = ‖v‖ := by simp
      rw [h1]
      exact mul_le_mul_of_nonneg_right (hC k (Set.mem_univ k)) (norm_nonneg v))
  simpa [pOp, T] using h

private theorem pOp_fin {κ : Measure (archCompact K n)} {e : archCompact K n → ℂ} (hI : IdemA κ e) (h : FA K n) (v : L2 μ) :
    pOp μ κ e (rightRegularRep (Gam K n) μ (fin1 h) v) = rightRegularRep (Gam K n) μ (fin1 h) (pOp μ κ e v) := by
  unfold pOp
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_orbit μ hI v)]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [map_smul]
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ((levLaws (K := K) n ∅).2.2.1 k h).eq]

private theorem mem_sph {P : Finset (Pl K)} {v : L2 μ} :
    v ∈ sphOff μ P ↔ ∀ u ∉ P, ∀ x ∈ GLnLocal.integralGL (u.adicCompletion K) n, rhoL μ u x v = v := by
  simp only [sphOff, fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

private theorem closed_sph (P : Finset (Pl K)) : IsClosed (sphOff μ P : Set (L2 μ)) := by
  have h : (sphOff μ P : Set (L2 μ)) =
      ⋂ u ∈ {u | u ∉ P}, ⋂ x ∈ (GLnLocal.integralGL (u.adicCompletion K) n : Set _), {v | rhoL μ u x v = v} := by
    ext v
    simp [mem_sph]
  rw [h]
  exact isClosed_biInter fun u _ => isClosed_biInter fun x _ => isClosed_eq (rhoL μ u x).continuous continuous_id

private theorem sph_stable {P : Finset (Pl K)} (γ : G1 K n)
    (hγ : ∀ u ∉ P, ∀ x : Gw n u, Commute γ (fin1 (AdelicGLn.localEmbedding u x))) {v : L2 μ} (hv : v ∈ sphOff μ P) :
    rightRegularRep (Gam K n) μ γ v ∈ sphOff μ P := by
  rw [mem_sph] at hv ⊢
  intro u hu x hx
  have h := hv u hu x hx
  show rightRegularRep (Gam K n) μ (fin1 (AdelicGLn.localEmbedding u x)) _ = _
  rw [← UnitaryRep.map_mul_apply, ← (hγ u hu x).eq, UnitaryRep.map_mul_apply]
  exact congrArg _ h

private theorem summand_of {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ) : IsSummand μ τ :=
  ⟨hτ.le, hτ.closed, fun g v hv => hτ.inv g v hv, hτ.ne, fun V' hle hc hi => hτ.irr V' hle hc fun g v hv => hi g v hv⟩

private theorem rest_sph {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ) (P : Finset (Pl K)) (h : FA K n)
    (hh : ∀ u ∈ P, GM.cf u h = 1) :
    ∃ c : ℂ, ∀ v ∈ τ, v ∈ sphOff μ P → prj (sphOff μ P) (rhoF μ h v) = c • v := by
  have hCO : ∀ u : Pl K, CO (GLnLocal.integralGL (u.adicCompletion K) n) := fun u =>
    ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩
  have hChr : ∀ u : Pl K, UpperTheory.ConvolutionTheory.L1.IsChr (GLnLocal.integralGL (u.adicCompletion K) n) (1 : Gw n u → ℂ) := fun u =>
    ⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ _ => by simp⟩
  have hA : (⨅ u ∉ (P : Set (Pl K)), UpperTheory.ConvolutionTheory.L1.eigL μ u (GLnLocal.integralGL (u.adicCompletion K) n) (1 : Gw n u → ℂ)) =
      sphOff μ P := by
    unfold sphOff
    simp only [Finset.mem_coe]
    exact iInf_congr fun u => iInf_congr fun _ => (UpperTheory.ConvolutionTheory.L1.eigBasic K n μ u _ 1 (hCO u) (hChr u)).2.1
  obtain ⟨c, hc⟩ := UpperTheory.ConvolutionTheory.L1.restScalar K n μ τ (summand_of μ hτ) (fun u => GLnLocal.integralGL (u.adicCompletion K) n)
    (fun u => (1 : Gw n u → ℂ)) (fun u => ⟨hCO u, hChr u⟩) (Eventually.of_forall fun _ => ⟨rfl, rfl⟩) (P : Set (Pl K))
    (fun u _ => UpperTheory.ConvolutionTheory.L1.sphRank K n μ τ (summand_of μ hτ) u) h (fun u hu => hh u hu)
  simp only [hA] at hc
  exact ⟨c, fun v hv hs => hc v ⟨hv, hs⟩⟩

private theorem comm_arch (a : archGroup K n) (h : FA K n) : Commute (archP K n a) (fin1 h) :=
  (MultiplicityOne.finProj_mul_archProj_comm h (a : ArchUnits K n)).symm

private theorem grp_split (a : archGroup K n) (x y : FA K n) :
    archP K n a * fin1 (x * y) = fin1 x * (archP K n a * fin1 y) := by
  have h : fin1 (x * y) = fin1 x * fin1 y := map_mul (MultiplicityOne.finProj K n) x y
  rw [h, ← mul_assoc, ← mul_assoc, (comm_arch a x).eq]

private theorem comm_emb {r : ℕ} {w : Fin r → Pl K} {ι : GS n w →* FA K n} (hw : Function.Injective w) (hι : IsEmb w ι)
    (g : GS n w) {u : Pl K} (hu : u ∉ im w) (x : Gw n u) : Commute (fin1 (ι g)) (fin1 (AdelicGLn.localEmbedding u x)) := by
  have h1 : Commute (ι g) (AdelicGLn.localEmbedding u x) :=
    ((embEx (K := K) n w hw).2 ι hι).2.2.2.2.1 g _ fun i => by
      refine (UpperTheory.ConvolutionTheory.Tf.locEmb K n u).2.2.1 (w i) (fun e => hu ?_) x
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, e⟩
  exact h1.map (MultiplicityOne.finProj K n)

private theorem prj_arch (P : Finset (Pl K)) (a : archGroup K n) (x : L2 μ) :
    prj (sphOff μ P) (rightRegularRep (Gam K n) μ (archP K n a) x) =
      rightRegularRep (Gam K n) μ (archP K n a) (prj (sphOff μ P) x) :=
  prj_comm _ (closed_sph μ P) _ (fun _ hv => sph_stable μ _ (fun _ _ _ => comm_arch _ _) hv)
    (fun _ hv => sph_stable μ _ (fun _ _ _ => (comm_arch _ _).inv_left) hv) x

private theorem prj_emb {r : ℕ} {w : Fin r → Pl K} {ι : GS n w →* FA K n} (hw : Function.Injective w) (hι : IsEmb w ι)
    (g : GS n w) (x : L2 μ) :
    prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ (fin1 (ι g)) x) =
      rightRegularRep (Gam K n) μ (fin1 (ι g)) (prj (sphOff μ (im w)) x) :=
  prj_comm _ (closed_sph μ _) _ (fun _ hv => sph_stable μ _ (fun _ hu _ => comm_emb hw hι g hu _) hv)
    (fun _ hv => sph_stable μ _ (fun _ hu _ => (comm_emb hw hι g hu _).inv_left) hv) x

private theorem cut_step {κ : Measure (archCompact K n)} {p : archCompact K n → ℂ} (hI : IdemA κ p) {r : ℕ} {w : Fin r → Pl K}
    {ι : GS n w →* FA K n} (hw : Function.Injective w) (hι : IsEmb w ι) (T : L2 μ →L[ℂ] L2 μ) (hT : ∀ v, T v = pOp μ κ p v)
    {q : L2 μ} (g : GS n w) (a : archGroup K n) (h' : FA K n) (c c' : ℂ)
    (e2 : prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ (fin1 h') q) = c • q)
    (e3 : pOp μ κ p (rightRegularRep (Gam K n) μ (archP K n a) q) = c' • q) :
    T (prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ (fin1 (ι g) * (archP K n a * fin1 h')) q)) =
      (c * c') • rhoF μ (ι g) q :=
  cut_abs (rightRegularRep (Gam K n) μ) (prj (sphOff μ (im w))) T (prj_emb μ hw hι g) (prj_arch μ _ a)
    (fun v => by rw [hT, hT, pOp_fin μ hI]) e2 ((hT _).trans e3)

private theorem cut_translate {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ) {κ : Measure (archCompact K n)}
    {p : archCompact K n → ℂ} (hR : RankInf μ τ κ p) {r : ℕ} {w : Fin r → Pl K} {ι : GS n w →* FA K n}
    (hw : Function.Injective w) (hι : IsEmb w ι) (T : L2 μ →L[ℂ] L2 μ) (hT : ∀ v, T v = pOp μ κ p v) {q : L2 μ}
    (hq : InH μ τ κ p (im w) q) (γ : G1 K n) :
    ∃ (g : GS n w) (c : ℂ), T (prj (sphOff μ (im w)) (rightRegularRep (Gam K n) μ γ q)) = c • rhoF μ (ι g) q := by
  obtain ⟨A₀, u, hγ⟩ := MultiplicityOne.exists_archProj_mul_finProj γ
  obtain ⟨g, h', hu, hh'⟩ := ((embEx (K := K) n w hw).2 ι hι).2.2.2.1 u
  obtain ⟨c, hc⟩ := rest_sph μ hτ (im w) h' (fun v hv => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
    rw [← hi]
    exact hh' i)
  obtain ⟨c', hc'⟩ := hR.2.2 ⟨A₀, trivial⟩
  have e1 : γ = fin1 (ι g) * (archP K n ⟨A₀, trivial⟩ * fin1 h') := by
    rw [← grp_split, ← hu]
    exact hγ.symm
  refine ⟨g, c * c', ?_⟩
  rw [e1]
  exact cut_step μ hR.1 hw hι T hT g _ h' c c' (hc q hq.1 hq.2.2) (hc' q hq.1 hq.2.1)

end SlopeTestRemainingChoices

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xTop :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), CuspIrr μ τ → RankInf μ τ κ p → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι → ∀ Q : Submodule ℂ (L2 μ), IsClosed (Q : Set (L2 μ)) →
      (∀ v ∈ Q, InH μ τ κ p (im w) v) → (∀ g, ∀ v ∈ Q, rhoF μ (ι g) v ∈ Q) → Q = ⊥ ∨ ∀ v, InH μ τ κ p (im w) v → v ∈ Q := by
  intro K _ _ _ μ _ τ κ p hτ hR r w ι hw hι Q hQc hQ hQι
  by_cases hbot : Q = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨q, hqQ, hq0⟩ := Q.ne_bot_iff.1 hbot
  obtain ⟨T, hT⟩ := exists_clm μ hR.1
  intro v hv
  refine mem_of_translates (rightRegularRep (Gam K 2) μ) hτ.closed hτ.inv hτ.irr hQc (T ∘L prj (sphOff μ (im w)))
    (hQ q hqQ).1 hq0 (fun γ => ?_) hv.1 ?_
  · obtain ⟨g, c, h⟩ := cut_translate μ hτ hR hw hι T hT (hQ q hqQ) γ
    rw [ContinuousLinearMap.comp_apply, h]
    exact Q.smul_mem c (hQι g q hqQ)
  · have hfix : prj (sphOff μ (im w)) v = v :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv.2.2)
    rw [ContinuousLinearMap.comp_apply, hfix, hT, hv.2.1]
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

section Abs

variable {G : Type} [Group G] [TopologicalSpace G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma orbit_finite [IsTopologicalGroup G] (π : UnitaryRep G H) {L L' : Subgroup G} (hL : IsCompact (L : Set G))
    (hL' : IsOpen (L' : Set G)) {m : H} (hm : ∀ u ∈ L', π u m = m) : ((fun u => π u m) '' (L : Set G)).Finite := by
  have hlc : IsLocallyConstant fun u : G => π u m := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' (L' : Set G), hL'.preimage (by fun_prop), by simp, fun y hy => ?_⟩
    have : y = x * (x⁻¹ * y) := by simp
    rw [this, UnitaryRep.map_mul_apply, hm _ hy]
  haveI : CompactSpace (L : Set G) := isCompact_iff_compactSpace.1 hL
  rw [Set.image_eq_range]
  exact (hlc.comp_continuous continuous_subtype_val).range_finite

private lemma mem_of_closure (π : UnitaryRep G H) (L : Subgroup G) (M E : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hst : ∀ u ∈ L, ∀ m ∈ M, π u m ∈ M) (hfin : ∀ m ∈ M, ((fun u => π u m) '' (L : Set G)).Finite)
    (hE : ∀ m ∈ M, (∀ u ∈ L, π u m = m) → m ∈ E) {v : H} (hv : v ∈ closure (M : Set H))
    (hfix : ∀ u ∈ L, π u v = v) : v ∈ M := by
  haveI : FiniteDimensional ℂ ↥(M ⊓ E) := Submodule.finiteDimensional_of_le inf_le_right
  have hcl : IsClosed ((M ⊓ E : Submodule ℂ H) : Set H) := Submodule.closed_of_finiteDimensional _
  suffices h : v ∈ closure ((M ⊓ E : Submodule ℂ H) : Set H) by
    rw [hcl.closure_eq] at h
    exact h.1
  rw [Metric.mem_closure_iff] at hv ⊢
  intro ε hε
  obtain ⟨m, hm, hd⟩ := hv ε hε
  set O := (hfin m hm).toFinset with hO
  have hmem : ∀ x, x ∈ O ↔ ∃ u ∈ L, π u m = x := by
    intro x
    simp [hO]
  have hne : O.Nonempty := ⟨π 1 m, (hmem _).2 ⟨1, L.one_mem, rfl⟩⟩
  have hcard : (0 : ℝ) < O.card := by exact_mod_cast hne.card_pos
  have haM : O.centerMass (fun _ => (1 : ℝ)) id ∈ M := by
    rw [Finset.centerMass]
    refine M.smul_of_tower_mem _ (M.sum_mem fun x hx => M.smul_of_tower_mem _ ?_)
    obtain ⟨u, hu, rfl⟩ := (hmem x).1 hx
    exact hst u hu m hm
  refine ⟨O.centerMass (fun _ => (1 : ℝ)) id, ⟨haM, hE _ haM fun u hu => ?_⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.centerMass, ContinuousLinearMap.map_smul_of_tower, map_sum]
      congr 1
      simp only [one_smul, id]
      refine Finset.sum_nbij' (fun x => π u x) (fun x => π u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
        exact (hmem _).2 ⟨u * a, L.mul_mem hu ha, UnitaryRep.map_mul_apply _ _ _ _⟩
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
        exact (hmem _).2 ⟨u⁻¹ * a, L.mul_mem (L.inv_mem hu) ha, UnitaryRep.map_mul_apply _ _ _ _⟩
      · intro x _
        simp [← UnitaryRep.map_mul_apply]
      · intro x _
        simp [← UnitaryRep.map_mul_apply]
  · rw [dist_comm, ← Metric.mem_ball]
    refine (convex_ball v ε).centerMass_mem (fun _ _ => zero_le_one) (by simpa using hcard) fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := (hmem x).1 hx
    rw [Metric.mem_ball, id, dist_comm, dist_eq_norm, ← hfix a ha, ← map_sub, UnitaryRep.norm_map, ← dist_eq_norm]
    exact hd

end Abs

section Cl

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private lemma continuous_pOp (μ : Measure (G1 K n)) [μ.IsHaarMeasure] {κ : Measure (archCompact K n)}
    {p : archCompact K n → ℂ} (hp : IdemA κ p) : Continuous (pOp μ κ p) := by
  obtain ⟨-, -, -, harc, hcs, -⟩ := levLaws (K := K) n ∅
  haveI := hcs
  haveI := hp.haar.prob
  have hi : ∀ v, Integrable (fun k => p k • rightRegularRep (Gam K n) μ (arc1 k) v) κ := fun v =>
    (hp.cont.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp harc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : ∀ v v', dist (pOp μ κ p v) (pOp μ κ p v') ≤ (∫ k, ‖p k‖ ∂κ) * dist v v' := by
    intro v v'
    rw [dist_eq_norm, dist_eq_norm, pOp, pOp, ← integral_sub (hi v) (hi v'), ← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext k
    rw [← smul_sub, ← map_sub, norm_smul, UnitaryRep.norm_map]
  exact (LipschitzWith.of_dist_le' hb).continuous

private lemma mem_fixF (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (U : Subgroup (FA K n)) (v : L2 μ) :
    v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v := by
  simp [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private lemma isClosed_inH (μ : Measure (G1 K n)) [μ.IsHaarMeasure] {τ : Submodule ℂ (L2 μ)} (hτ : CuspIrr μ τ)
    {κ : Measure (archCompact K n)} {p : archCompact K n → ℂ} (hp : IdemA κ p) (S : Finset (Pl K)) :
    IsClosed {v | InH μ τ κ p S v} := by
  have hf : ∀ U : Subgroup (FA K n), IsClosed (fixF μ U : Set (L2 μ)) := by
    intro U
    have h : (fixF μ U : Set (L2 μ)) = ⋂ u ∈ U, {v | rhoF μ u v = v} := by
      ext v
      simp [mem_fixF]
    rw [h]
    exact isClosed_biInter fun u _ => isClosed_eq (rhoF μ u).continuous continuous_id
  have hs : IsClosed (sphOff μ S : Set (L2 μ)) := by
    rw [sphOff]
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun v => isClosed_iInter fun _ => hf _
  exact hτ.closed.inter ((isClosed_eq (continuous_pOp μ hp) continuous_id).inter hs)

end Cl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xSimple :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), CuspIrr μ τ → RankInf μ τ κ p → ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι →
      SimpleIn (rS ι) (Xs μ τ κ p (im w)) ∧ SchurIn (rS ι) (Xs μ τ κ p (im w)) := by
  intro K _ _ _ μ _ τ κ p hτ hR r w ι hw hι
  have hp : IdemA κ p := hR.1
  obtain ⟨hX, hX'⟩ := xMem μ τ κ p hp
  have hstab := fun φ hφ => (hX' hτ w ι hw hι φ hφ).2
  obtain ⟨J, hJi, hJ, hJr, hJU⟩ := exists_injection_into_l2_cusp μ τ κ p hτ hp (im w)
  obtain ⟨-, hcw, hco, -, -, hlev⟩ := (embEx 2 w hw).2 ι hι
  have hcw1 : ∀ i, GM.cf (w i) (1 : FA K 2) = 1 := fun i => by
    have := hcw 1 i
    rwa [map_one] at this
  have hcv1 : ∀ v, GM.cf v (1 : FA K 2) = 1 := fun v => by
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact hcw1 i
    · have := hco 1 v hv
      rwa [map_one] at this
  have hCO := (levLaws (K := K) 2 (im w)).1
  have hrS : ∀ g (φ : G1 K 2 → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g)) := fun _ _ _ => rfl

  have hdec : ∀ U, ∀ u ∈ levOn (im w) U, ∃ g, ι g ∈ levOn (im w) U ∧
      ∀ φ ∈ Xs μ τ κ p (im w), ∀ x, φ (x * fin1 u) = rS ι g φ x := by
    intro U u hu
    obtain ⟨g, h', rfl, hg, h1, h2⟩ := (hlev U u).1 hu
    refine ⟨g, (hlev U _).2 ⟨g, 1, (mul_one _).symm, hg, hcw1, fun v => ?_⟩, fun φ hφ x => ?_⟩
    · rw [hcv1]
      exact one_mem _
    · obtain ⟨-, -, -, U', -, hU'⟩ := (hX _ _).1 hφ
      have := hU' h' ((hlev U' _).2 ⟨1, h', by simp, fun i => one_mem _, h1, h2⟩) (x * fin1 (ι g))
      rw [hrS, ← this]
      simp only [fin1, map_mul, mul_assoc]
  let π : UnitaryRep (FA K 2) (L2 μ) :=
    (rightRegularRep (rationalGLOne (K := K) (n := 2)) μ).compHom (MultiplicityOne.finProj K 2) MultiplicityOne.continuous_finProj
  have hπ : ∀ h, π h = rhoF μ h := fun _ => rfl
  have hfixJ : ∀ (L : Subgroup (FA K 2)) (φ : Xs μ τ κ p (im w)), FixF L φ.1 → ∀ u ∈ L, rhoF μ u (J φ) = J φ :=
    fun L φ hφ u hu => (hJr u φ φ fun x => (hφ u hu x).symm).symm
  have hS : SimpleIn (rS ι) (Xs μ τ κ p (im w)) := by
    refine ⟨fun g φ hφ => hstab φ hφ g, fun Q hQ hQs => ?_⟩
    let M : Submodule ℂ (L2 μ) := (Q.comap (Xs μ τ κ p (im w)).subtype).map J
    have hM : ∀ g, ∀ m ∈ M, rhoF μ (ι g) m ∈ M := by
      rintro g _ ⟨φ, hφ, rfl⟩
      exact ⟨⟨rS ι g φ.1, hstab _ φ.2 g⟩, hQs g _ hφ, hJr _ _ _ fun x => rfl⟩
    have hT := xTop μ τ κ p hτ hR w ι hw hι M.topologicalClosure M.isClosed_topologicalClosure
      (fun v hv => closure_minimal (s := (M : Set (L2 μ))) (by rintro _ ⟨φ, -, rfl⟩; exact (hJ φ).2)
        (isClosed_inH μ hτ hp (im w)) hv)
      (fun g v hv => map_mem_closure (rhoF μ (ι g)).continuous hv (hM g))
    rcases hT with hT | hT
    · left
      rw [eq_bot_iff]
      intro φ hφ
      have h0 : J ⟨φ, hQ hφ⟩ ∈ M.topologicalClosure := M.le_topologicalClosure ⟨⟨φ, hQ hφ⟩, hφ, rfl⟩
      rw [hT, Submodule.mem_bot, ← map_zero J] at h0
      exact congrArg Subtype.val (hJi h0)
    · right
      refine le_antisymm hQ fun φ hφ => ?_
      obtain ⟨-, -, -, U, hU, hφU⟩ := (hX _ _).1 hφ
      obtain ⟨hsur, E, hE, hEU⟩ := hJU U hU
      haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) :=
        FiniteDimensional.of_injective
          (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2)
          fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 K 2 → ℂ)) h))
      have key : J ⟨φ, hφ⟩ ∈ M := by
        refine mem_of_closure π (levOn (im w) U) M ((E.comap (Xs μ τ κ p (im w)).subtype).map J) ?_ ?_ ?_
          (hT _ (hJ _).2) (hfixJ _ ⟨φ, hφ⟩ hφU)
        · rintro u hu _ ⟨ψ, hψ, rfl⟩
          obtain ⟨g, -, hg⟩ := hdec U u hu
          exact ⟨⟨rS ι g ψ.1, hstab _ ψ.2 g⟩, hQs g _ hψ, hJr _ _ _ fun x => (hg _ ψ.2 x).symm⟩
        · rintro _ ⟨ψ, -, rfl⟩
          obtain ⟨-, -, -, U', hU', hψU⟩ := (hX _ _).1 ψ.2
          exact orbit_finite π (hCO U hU).1.1 (hCO U' hU').1.2 (hfixJ _ ψ hψU)
        · rintro _ ⟨ψ, -, rfl⟩ hf
          obtain ⟨ψ', h1, h2⟩ := hsur _ (hJ ψ).2 ((mem_fixF μ _ _).2 hf)
          exact ⟨ψ', hEU _ ψ'.2 h2, h1⟩
      obtain ⟨ψ, hψ, h⟩ := key
      rw [hJi h] at hψ
      exact hψ
  refine ⟨hS, fun T hT => ?_⟩
  by_cases h0 : ∀ φ : Xs μ τ κ p (im w), φ = 0
  · exact ⟨0, fun v => by rw [h0 (T v), zero_smul]⟩
  push Not at h0
  obtain ⟨φ, hφ0⟩ := h0
  obtain ⟨-, -, -, U, hU, hφU⟩ := (hX _ _).1 φ.2
  obtain ⟨-, E, hE, hEU⟩ := hJU U hU
  let F : Submodule ℂ (Xs μ τ κ p (im w)) :=
    { carrier := {ψ | FixF (levOn (im w) U) ψ.1}
      add_mem' := fun ha hb u hu g => by simp [ha u hu g, hb u hu g]
      zero_mem' := fun u hu g => rfl
      smul_mem' := fun c _ ha u hu g => by simp [ha u hu g] }
  haveI : FiniteDimensional ℂ ↥(E.comap (Xs μ τ κ p (im w)).subtype) :=
    FiniteDimensional.of_injective
          (((Xs μ τ κ p (im w)).subtype.domRestrict (E.comap (Xs μ τ κ p (im w)).subtype)).codRestrict E fun a => a.2)
          fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : E => (z : G1 K 2 → ℂ)) h))
  haveI : FiniteDimensional ℂ F :=
    Submodule.finiteDimensional_of_le (S₂ := E.comap (Xs μ τ κ p (im w)).subtype) fun ψ hψ => hEU _ ψ.2 hψ
  haveI : Nontrivial F := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  have hTF : ∀ ψ ∈ F, T ψ ∈ F := by
    intro ψ hψ u hu x
    obtain ⟨g, hg, hg'⟩ := hdec U u hu
    rw [hg' _ (T ψ).2, ← hT g ψ ψ (funext fun y => (hψ _ hg y).symm)]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hTF)
  obtain ⟨ψ, hψ⟩ := hc.exists_hasEigenvector
  have hψ1 : T ψ.1 = c • ψ.1 := congrArg Subtype.val hψ.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases hS.2 ((Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype) (Submodule.map_subtype_le _ _) (by
    rintro g _ ⟨a, ha, rfl⟩
    refine ⟨⟨rS ι g a.1, hstab _ a.2 g⟩, Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_), rfl⟩
    rw [hT g a _ rfl, Module.End.mem_eigenspace_iff.1 ha]
    simp) with h | h
  · have : (ψ.1 : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype :=
      ⟨ψ.1, Module.End.mem_eigenspace_iff.2 hψ1, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact absurd (Subtype.ext (Subtype.ext this)) hψ.2
  · intro v
    have : (v : G1 K 2 → ℂ) ∈ (Module.End.eigenspace T c).map (Xs μ τ κ p (im w)).subtype := by
      rw [h]
      exact v.2
    obtain ⟨a, ha, hav⟩ := this
    rw [← Subtype.ext hav]
    exact Module.End.mem_eigenspace_iff.1 ha
