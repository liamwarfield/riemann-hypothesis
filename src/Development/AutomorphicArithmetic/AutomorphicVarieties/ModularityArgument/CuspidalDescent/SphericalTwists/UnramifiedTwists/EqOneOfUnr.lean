module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.LgAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.GdLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.EqOneOfUnr
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = GlobalTheory.SmGL.unrChar k a := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
  have h0 : x ≠ 0 := fun e => ValuativeRel.uniformizer_ne_zero (R := k) (by rw [← hx, e, map_zero])
  exact ⟨_, eq_unrChar h (ϖ := Units.mk0 x h0) hx⟩

private theorem full_chars [CharZero k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsSmoothChar (ξ i)) (hs : HasSupport ρ (GlobalTheory.RoadU.chars ξ hξ))
    (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) : Nonempty (ρ.Equiv (prinSeries ξ)) ∧
    IsL ((List.ofFn fun i => Segment.single (IrrGL.ofChar (ξ i) (hξ i)) (IrrGL.isCusp_ofChar _ _) : List (Segment k)) :
      Multiset (Segment k)) ρ := by
  obtain ⟨hρ, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds k n V ρ ξ hξ).1 hs
  let y : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ξ i) (hξ i)
  have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
  have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i => Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  have hnl : ∀ i j, ¬ (Segment.single (y i) (hy i)).Linked (Segment.single (y j) (hy j)) := fun i j =>
    GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j) (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j))
  have hP : (prodIrr y hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd hnl
      (fun i => (single_spec (hy i)).2.1)
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
    (stdBlocks (fun i => (y i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (ξ i))
  let q := multiProdEquiv (stdBlocks (fun i => (y i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i))
  have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
  letI := nontrivial_of_irreducible hM
  have nontriv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {τ : Representation ℂ G V}
      (h : IsSubquotient σ τ) (hw : Nontrivial W) : Nontrivial V := by
    letI := hw
    obtain ⟨S, f, hf⟩ := h
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  haveI := nontriv (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries
      (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ξ) (nontrivial_of_irreducible hM)
  have equiv_sub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {τ : Representation ℂ G V}
      (h : IsSubquotient σ τ) [Nontrivial W] (hτ : τ.IsIrreducible) : Nonempty (τ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation τ) := hτ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : τ.IntertwiningMap σ := f.comp (topEquiv τ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv τ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨e1⟩ := equiv_sub (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ξ) hM
  obtain ⟨e⟩ := hq.nonempty_equiv hρ (GlobalTheory.Parabolic.isIrreducible_of_equiv e1 hM)
  have φ : ρ.Equiv (prodIrr y hd) := (e.symm.trans e1.symm).trans (p.trans q)
  exact ⟨⟨e.symm⟩, n, y, hd, ⟨fun i => Segment.single (y i) (hy i), ⟨Fin.univ_val_map _, fun i j _ hp => hnl i j hp.1⟩,
    fun i => (single_spec (hy i)).2.1⟩, (isCosocle_self hρ).of_equiv (.refl _) φ⟩

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem eq_one_of_unr {n : ℕ} (c : Fin n → Weil h →* ℂˣ) (hc : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (c i))
    (hu : (sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).unr) (i : Fin n) (t : Ine (F := E) A) :
    c i (ineIncl h t) = 1 := by
  have h1 : ∀ i g, (WD.lpOfChar h (c i) (hc i)).charPol g = X - C (c i g : ℂ) := fun i g => by
    rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  have h2 : ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).charPol (ineIncl h t)).IsRoot (c i (ineIncl h t) : ℂ) := by
    rw [GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn, List.prod_ofFn]
    refine IsRoot.dvd ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    simp [h1]
  generalize sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i)) = x at hu h2
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.unr_mk] at hu
  rw [WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at h2
  obtain ⟨v, hv⟩ := h2.exists_hasEigenvector
  have h3 := hv.apply_eq_smul
  refine Units.ext (smul_left_injective ℂ hv.2 ?_)
  simpa using h3.symm

end WD

theorem sphT : SphT := by
  intro _ F Ω _ _ _ _ _ l _ ι n r _ w hl A h hI rc ⟨a, ha, L⟩ σ hP hx
  haveI : CharZero (w.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have e0 := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -, -⟩ := id hx
  have hxu : (rc (algNorm σ)).unr := e0 ▸ (hN.unr_wdOf_iff hl ht ι).2 hI
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨⟨e⟩, hL0⟩ := full_chars (n := n) σ.ρ ξ hξ hs' hu
  have hL := hL0.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL, segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, L.one]
  rw [algNorm, L.nu, hr, WD.unr_tw] at hxu
  have hun : ∀ i, IsUnram (ξ i) := fun i u hu1 => by
    obtain ⟨g, rfl⟩ := ha.surj u
    have h0 : deg g = 0 := by
      have h1 := ha.ord_eq g
      rw [ord_eq_zero_iff.2 hu1] at h1
      omega
    exact eq_one_of_unr _ _ hxu i ⟨g, deg_eq_zero_iff.1 h0⟩
  choose α hα using fun i => exists_unr (hun i)
  obtain rfl : ξ = fun i => GlobalTheory.SmGL.unrChar _ (α i) := funext hα
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1
    (GlobalTheory.PrinSat.hasSatGL_of_equiv e (GlobalTheory.PrinSat.hasSatGL_prinSeries w α)).1
  exact ⟨v, hv0, GlobalTheory.LGrp.mem_fixed.1 hv⟩

end UpperTheory.V.Z.Desc.W
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SphUntw
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MongeAmpereChartDensityIntegral
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.CharTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hasSupport_rep_tw {x : IrrGL (k := k)} {s : Multiset (IrrGL (k := k))} (hx : HasSupport x.rep s) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : HasSupport (x.tw χ hχ).rep (s.map (·.tw χ hχ)) :=
  (hx.tw χ hχ).of_equiv (x.twEquiv χ hχ)

theorem chars_tw {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (chars ξ hξ).map (·.tw χ hχ) = chars (fun j => ξ j * χ) fun j => (hξ j).mul hχ := by
  simp only [chars, Multiset.map_map, Function.comp_def, IrrGL.tw_ofChar]

end GlobalTheory.RoadU.CharTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingProdIrrSupport
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.BCen.SuppEmbed

theorem exists_embedding_prodIrr_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ (t : ℕ) (x : Fin t → IrrGL (k := k)) (hx : ∑ a, (x a).1 = n) (φ : π.IntertwiningMap (prodIrr x hx)),
      (∀ a, (x a).IsCusp) ∧ Function.Injective φ ∧ ∀ s, HasSupport π s ↔ Finset.univ.val.map x = s := by
  intro k _ _ _ _ n V _ _ π hs hi
  obtain ⟨t, x, hx, hc, φ, hφ⟩ :=
    GlobalTheory.CompanionTheory.SubEmb.subEmbedding_of_stage GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append k n V π hs hi
  have hsupp : HasSupport π (Finset.univ.val.map x) :=
    hasSupport_of_isSubquotient hi hc (.of_injective φ hφ)
  refine ⟨t, x, hx, φ, hc, hφ, fun s => ⟨fun h => ?_, fun h => h ▸ hsupp⟩⟩
  exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.bernsteinZelevinskyFiniteness_holds hsupp h

end GlobalTheory.BCen.SuppEmbed
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end WD

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

end UpperTheory.V.Z.Desc.W
end
end
