module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebra
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

open Polynomial Module.End

theorem part_projector_mem_adjoin :
    ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
      [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
      [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) →
      (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) →
      (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) →
      ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) →
      ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S,
        (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧
          ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ S hS hsplit hint L _ _ _ 𝔪
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨F, hF, -⟩ := NCov.exists_finset_pts hinj hS hsplit hint
  by_cases hA : ∃ ψ0 : Algebra.adjoin O S →ₐ[O] O, NCov.cls ψ0 = 𝔪
  swap
  · push_neg at hA
    refine ⟨0, Subalgebra.zero_mem _, fun x hx => ?_, fun x _ => rfl⟩
    have : NCov.part (Algebra.adjoin O S) 𝔪 = ⊥ := by
      unfold NCov.part
      exact iSup₂_eq_bot.2 fun ψ h => absurd h (hA ψ)
    rw [this, Submodule.mem_bot] at hx
    simp [hx]
  obtain ⟨ψ0, rfl⟩ := hA
  have hmax := NCov.cls_isMaximal ψ0
  have hs : ∀ φ : Algebra.adjoin O S →ₐ[O] O, ∃ s : Algebra.adjoin O S,
      (NCov.cls φ ≠ NCov.cls ψ0 → s ∈ NCov.cls φ) ∧ s ∉ NCov.cls ψ0 := by
    intro φ
    by_cases h : NCov.cls φ = NCov.cls ψ0
    · exact ⟨1, fun h' => absurd h h', fun h1 => hmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)⟩
    · have : ¬ NCov.cls φ ≤ NCov.cls ψ0 := fun hle =>
        h ((NCov.cls_isMaximal φ).eq_of_le hmax.ne_top hle)
      obtain ⟨s, hs1, hs2⟩ := SetLike.not_le_iff_exists.1 this
      exact ⟨s, fun _ => hs1, hs2⟩
  choose s hsin hsout using hs
  set FA := F.filter (fun ψ => NCov.cls ψ = NCov.cls ψ0)
  set FB := F.filter (fun ψ => NCov.cls ψ ≠ NCov.cls ψ0)
  letI : IsMulCommutative (Algebra.adjoin O S) :=
    Algebra.isMulCommutative_adjoin O (fun a ha b hb _ => hS a ha b hb)
  open scoped IsMulCommutative in
  obtain ⟨f, hfdef⟩ : ∃ f : Algebra.adjoin O S, f = ∏ φ ∈ FB, s φ := ⟨_, rfl⟩
  have hres : ∀ ψ : Algebra.adjoin O S →ₐ[O] O, ∀ u, u ∈ NCov.cls ψ ↔ IsLocalRing.residue O (ψ u) = 0 :=
    fun ψ u => Iff.rfl
  have hfA : ∀ ψ, NCov.cls ψ = NCov.cls ψ0 → IsLocalRing.residue O (ψ f) ≠ 0 := by
    intro ψ hψ
    rw [hfdef, map_prod, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun φ _ => ?_
    have := hsout φ
    rw [← hψ, hres] at this
    exact this
  have hfB : ∀ φ ∈ FB, IsLocalRing.residue O (φ f) = 0 := by
    intro φ hφ
    rw [hfdef, map_prod, map_prod]
    exact Finset.prod_eq_zero hφ ((hres φ _).1 (hsin φ (Finset.mem_filter.1 hφ).2))
  let d : (Algebra.adjoin O S →ₐ[O] O) → ℕ := fun ψ =>
    (f : End K V).maxGenEigenspaceIndex (NCov.pt ψ f)
  let g : O[X] := ∏ ψ ∈ FA, (X - C (ψ f)) ^ d ψ
  let h : O[X] := ∏ φ ∈ FB, (X - C (φ f)) ^ d φ
  have hcop : IsCoprime g h := by
    refine IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => IsCoprime.pow ?_
    refine isCoprime_X_sub_C_of_isUnit_sub ?_
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_sub, hfB φ hφ, sub_zero]
    exact hfA ψ (Finset.mem_filter.1 hψ).2
  obtain ⟨p, q, hpq⟩ := hcop
  have hkill : ∀ (G : Finset (Algebra.adjoin O S →ₐ[O] O)) (ψ) (_ : ψ ∈ G) (x : V),
      x ∈ NCov.W _ (NCov.pt ψ) → aeval (f : End K V) (∏ φ ∈ G, (X - C (φ f)) ^ d φ) x = 0 := by
    intro G ψ hψ x hx
    rw [show (∏ φ ∈ G, (X - C (φ f)) ^ d φ) =
        (∏ φ ∈ G.erase ψ, (X - C (φ f)) ^ d φ) * (X - C (ψ f)) ^ d ψ from
      (Finset.prod_erase_mul _ _ hψ).symm]
    rw [map_mul, Module.End.mul_apply, map_pow, map_sub, aeval_X, aeval_C]
    rw [NCov.pow_sub_apply_eq_zero ψ f hx, map_zero]
  have hval : ((aeval f (q * h) : Algebra.adjoin O S) : End K V) = aeval (f : End K V) (q * h) := by
    have e := aeval_algHom_apply (Algebra.adjoin O S).val f (q * h)
    simpa using e.symm
  refine ⟨_, (aeval f (q * h)).2, ?_, ?_⟩
  · intro x hx
    rw [hval]
    have hle : NCov.part (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h) - 1) := by
      unfold NCov.part
      refine iSup₂_le fun ψ hψ => ?_
      intro y hy
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      by_cases hW : NCov.W _ (NCov.pt ψ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hψA : ψ ∈ FA := Finset.mem_filter.2 ⟨hF ψ hW, hψ⟩
      have e1 := congrArg (fun P => aeval (f : End K V) P y) hpq
      simp only [map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply, map_one,
        Module.End.one_apply] at e1
      rw [hkill FA ψ hψA y hy, map_zero, zero_add] at e1
      simpa [map_mul, Module.End.mul_apply] using e1
    have := hle hx
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  · intro x hx
    rw [hval]
    have hle : NCov.off (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h)) := by
      unfold NCov.off
      refine iSup₂_le fun φ hφ => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      by_cases hW : NCov.W _ (NCov.pt φ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hφB : φ ∈ FB := Finset.mem_filter.2 ⟨hF φ hW, hφ⟩
      rw [map_mul, Module.End.mul_apply, hkill FB φ hφB y hy, map_zero]
    exact hle hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebraStatement
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra : ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) → (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) → (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) → ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) → ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S, (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧ ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  first | exact @GlobalTheory.part_projector_mem_adjoin | exact GlobalTheory.part_projector_mem_adjoin | (intros; apply GlobalTheory.part_projector_mem_adjoin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormLatticeEqSumLocalisedLattices
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.LatSplit

theorem form_gen_span {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

variable {D : D7} {M : MtFam D}

theorem genSet_props (j : ℕ) (w : D.what₂.places.Pl) :
    (genSet D (D.what₂.muTw w) j).Finite ∧ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j) = ⊤ :=
  form_gen_span (D.what₂.jMt _ j) (Module.Free.chooseBasis _ _) (D.what₂.jMt_basis _ j _) _
    (D.what₂.MtLat _ j).span_top (D.what₂.MtLat_sub _ j)

theorem latLoc_fg (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) : (latLoc B j w).FG :=
  Submodule.fg_span ((genSet_props (D := D) j w).1.image _)

theorem latLoc_span (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) :
    Submodule.span (FractionRing (B.Oc j w)) (latLoc B j w : Set (B.V j w)) = ⊤ := by
  rw [latLoc, Submodule.span_span_of_tower]
  have hG := (genSet_props (D := D) j w).2
  have key : ∀ x ∈ Submodule.span D.what₂.LL (genSet D (D.what₂.muTw w) j),
      B.iV j w x ∈ Submodule.span (FractionRing (B.Oc j w)) (B.iV j w '' genSet D (D.what₂.muTw w) j) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  rw [eq_top_iff, ← (B.iV_basis j w b).2, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact key _ (hG ▸ Submodule.mem_top)

theorem alg_stable (B : NLocBase D M) {j : ℕ} {w : D.what₂.places.Pl} (hl : LatStable B j w) :
    ∀ t ∈ heckeAlg B j w, ∀ x ∈ latLoc B j w, t x ∈ latLoc B j w := by
  intro t ht
  induction ht using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    exact hl v k hvk
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact (latLoc B j w).smul_mem r hx
  | add f g _ _ hf hg => intro x hx; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  | mul f g _ _ hf hg => intro x hx; exact hf _ (hg x hx)

end GlobalTheory.LatSplit

namespace GlobalTheory.LatSplit

variable {D : D7} {M : MtFam D}

theorem proj_facts {K V : Type} [Field K] [AddCommGroup V] [Module K V] {P Q : Submodule K V} (hc : IsCompl P Q)
    (t : Module.End K V) (hP : ∀ x ∈ P, t x = x) (hQ : ∀ x ∈ Q, t x = 0) (y : V) : t y ∈ P ∧ y - t y ∈ Q := by
  have hy : y ∈ P ⊔ Q := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add (f := _), hP p hp, hQ q hq, add_zero, add_sub_cancel_left]
  exact ⟨hp, hq⟩

theorem part_le_off {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] [IsLocalRing O] (T : Subalgebra O (Module.End K V)) {I J : Ideal T} (h : I ≠ J) :
    NCov.part T I ≤ NCov.off T J :=
  iSup₂_le fun ψ hψ => le_iSup₂_of_le (f := fun ψ (_ : NCov.cls ψ ≠ J) => NCov.W T (NCov.pt ψ)) ψ
    (by rw [hψ]; exact h) le_rfl

theorem exists_proj (T : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw T.B) {j : ℕ} {w : D.what₂.places.Pl} (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (hl : LatStable T.B j w) (I : Ideal (heckeAlg T.B j w)) :
    ∃ t ∈ heckeAlg T.B j w, (∀ x ∈ NCov.part (heckeAlg T.B j w) I, t x = x) ∧
      ∀ x ∈ NCov.off (heckeAlg T.B j w) I, t x = 0 := by
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  exact GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra (T.B.Oc j w) (FractionRing (T.B.Oc j w)) (T.B.V j w) (heckeGens T.B j w) hS hsplit hint
    (latLoc T.B j w) (latLoc_fg T.B j w) (latLoc_span T.B j w)
    (fun a ha x hx => alg_stable T.B hl a (Algebra.subset_adjoin ha) x hx) I

theorem main : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m →
    D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ∀ y : T.B.V j w,
    y ∈ latLoc T.B j w ↔ ∃ z : ∀ i : D.nd.Loc, TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i),
      (∀ i, z i ∈ D.nd.MtIn i) ∧ y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (z i.1) := by
  classical
  intro D M T j w h1 h2 hw hstd hl y
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  obtain ⟨hS, hsplit, hint⟩ := gens_hypsTw T.B hstd h1 h2 (Or.inl hw)
  have hinj := IsFractionRing.injective (T.B.Oc j w) (FractionRing (T.B.Oc j w))
  choose tp htp hpart hoff using exists_proj T hstd h1 h2 hw hl
  have hc := fun I => NCov.isCompl_part_off hinj hS hsplit hint I
  have eL : latC T.B j w = latLoc T.B j w := rfl

  have hlp : ∀ I x, x ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) I → x ∈ latLoc T.B j w := by
    intro I x hx
    obtain ⟨hxP, hxL⟩ := Submodule.mem_inf.1 hx
    obtain ⟨l, hlL, q, hq, rfl⟩ := Submodule.mem_sup.1 hxL
    have e : tp I (l + q) = l + q := hpart I _ hxP
    rw [map_add (f := _), hoff I q hq, add_zero] at e
    rw [← e]
    exact alg_stable T.B hl _ (htp I) l hlL
  constructor
  · intro hy

    have ex : ∀ i (h : i ∈ D.nd.locs j w), ∃ z, z ∈ D.nd.MtIn i ∧ T.Psi j w i h z = tp (T.mx j w i) y := by
      intro i h
      haveI := RingHomInvPair.of_ringEquiv (T.phO j w i h)
      have hm : tp (T.mx j w i) y ∈ NCov.latPart (heckeAlg T.B j w) (latC T.B j w) (T.mx j w i) := by
        refine Submodule.mem_inf.2 ⟨(proj_facts (hc _) _ (hpart _) (hoff _) y).1, ?_⟩
        exact Submodule.mem_sup_left (alg_stable T.B hl _ (htp _) y hy)
      rw [← map_psiO_MtIn T hstd h] at hm
      obtain ⟨z, hz, e⟩ := Submodule.mem_map.1 hm
      exact ⟨z, hz, e⟩
    refine ⟨fun i => if h : i ∈ D.nd.locs j w then (ex i h).choose else 0, fun i => ?_, ?_⟩
    · by_cases h : i ∈ D.nd.locs j w
      · dsimp only; rw [dite_eq_left h]; exact (ex i h).choose_spec.1
      · dsimp only; rw [dite_eq_right h]; exact Submodule.zero_mem _
    · have hsum : ∑ i ∈ (D.nd.locs j w).attach,
          T.Psi j w i.1 i.2 (if h : i.1 ∈ D.nd.locs j w then (ex i.1 h).choose else 0) =
          ∑ i ∈ (D.nd.locs j w).attach, tp (T.mx j w i.1) y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [dite_eq_left i.2]
        exact (ex i.1 i.2).choose_spec.2
      rw [hsum, ← sub_eq_zero]
      refine NCov.eq_zero_of_forall_mem_off hinj hS hsplit hint ((D.nd.locs j w).image (T.mx j w))
        (fun I hI => ?_) ?_
      · obtain ⟨i, hi, rfl⟩ := T.mx_all j w h1 h2 hw I hI
        exact Finset.mem_image_of_mem _ hi
      · intro I hI
        obtain ⟨i0, hi0, rfl⟩ := Finset.mem_image.1 hI
        rw [← Finset.add_sum_erase _ _ (Finset.mem_attach _ ⟨i0, hi0⟩), sub_add_eq_sub_sub]
        refine Submodule.sub_mem _ (proj_facts (hc _) _ (hpart _) (hoff _) y).2 (Submodule.sum_mem _ fun i hi => ?_)
        have hne : T.mx j w i.1 ≠ T.mx j w i0 := by
          intro e
          have := T.mx_inj j w i.2 hi0 e
          exact (Finset.mem_erase.1 hi).1 (Subtype.ext this)
        exact part_le_off _ hne (proj_facts (hc _) _ (hpart _) (hoff _) y).1
  · rintro ⟨z, hz, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    haveI := RingHomInvPair.of_ringEquiv (T.phO j w i.1 i.2)
    refine hlp (T.mx j w i.1) _ ?_
    rw [← map_psiO_MtIn T hstd i.2]
    exact Submodule.mem_map_of_mem (hz i.1)

end GlobalTheory.LatSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFormLatticeEqSumLocalisedLatticesStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFormLattice_eq_sum_localised_lattices : ∀ (D : D7) (M : MtFam D) (T : NormalizedLocalCompatibility D M) (j : ℕ) (w : D.what₂.places.Pl), 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → HeckeStdTw T.B → LatStable T.B j w → ∀ y : T.B.V j w, y ∈ latLoc T.B j w ↔ ∃ z : ∀ i : D.nd.Loc, TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i), (∀ i, z i ∈ D.nd.MtIn i) ∧ y = ∑ i ∈ (D.nd.locs j w).attach, T.Psi j w i.1 i.2 (z i.1) := by
  exact @GlobalTheory.LatSplit.main
end
