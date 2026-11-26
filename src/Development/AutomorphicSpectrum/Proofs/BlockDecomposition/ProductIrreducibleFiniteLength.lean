module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CayleyRuleOfBiInvariantVacuumCoefficient
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.ProdFL

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.T.parabolic_induction_finite_length k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x))

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N),
      HasFiniteLength (prodIrr x hd) :=
  fun hA _ _ x hd => hasFiniteLength_prodIrr hA x hd

end GlobalTheory.CompanionTheory.ProdFL

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_irreducible_finite_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), HasFiniteLength (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.ProdFL.main | exact GlobalTheory.CompanionTheory.ProdFL.main | (intros; apply GlobalTheory.CompanionTheory.ProdFL.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen

theorem lip_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : PI.VolStabS.TensAllW.LIP S) : PI.VolStabS.TensAllW.LIP R := by
  intro m n _ _ _ _ W hW
  obtain ⟨P, hP⟩ := h m n (W.map e) (by
    intro c hc
    have hc' : W *ᵥ (fun j => e.symm (c j)) = 0 := by
      funext i
      apply e.injective
      have := congrFun hc i
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum] using this
    have h0 := hW _ hc'
    funext j
    have := congrFun h0 j
    simpa using this)
  refine ⟨P.map e.symm, ?_⟩
  ext i j
  apply e.injective
  have := congrFun (congrFun hP i) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  simp only [map_mul, Matrix.map_apply, RingEquiv.apply_symm_apply]
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem lip_of_artinian_reduced (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R] :
    PI.VolStabS.TensAllW.LIP R := by
  classical
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  letI : ∀ m : MaximalSpectrum R, Field (R ⧸ m.asIdeal) := fun m =>
    Ideal.Quotient.field m.asIdeal
  exact lip_of_ringEquiv (IsArtinianRing.equivPi R)
    (PI.VolStabS.TensAllW.lip_pi (fun m : MaximalSpectrum R => R ⧸ m.asIdeal)
      (fun m => PI.VolStabS.TensAllW.lip_field _))

theorem isOpen_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ hR n M
  obtain ⟨hT, -, -, -, hA, hRed, hU, -⟩ := hR
  haveI := hT
  haveI := hA
  haveI := hRed
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hUo : IsOpen {r : R | IsUnit r} := by
    have := hU.isOpen_range
    convert this using 1
    ext r
    simp [IsUnit]
  exact PI.VolStabS.TensAllW.isOpen_linIndep (Module.finBasis F E) R hUo
    (lip_of_artinian_reduced R)

end GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearly_independent_frames_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdStage

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two in
theorem equiv_of_iso_two {p q c r t N : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) (H : Iso (two e (pr x hx) (pr y hy)) (pr w hz)) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := H


open GlobalTheory.ProdFlatten in
unseal GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in
theorem equiv_of_iso {q c N : ℕ} (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (w a).1 = N) (H : Iso (pr y hy) (pr w hz)) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) := H

theorem ind₂_prodIrr_empty {c q N : ℕ} (x : Fin 0 → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = 0) (hy : ∑ a, (y a).1 = N)
    (hz : ∑ a, (w a).1 = N) (e : 0 + N = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have A : Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr y hy)) :=
    GlobalTheory.ProdReorder.ind₂_unit_left k N 0 e _ (prodIrr y hy) (isSmooth_prodIrr y hy)
      (fun a => (x a).1) (fun a => (x a).2.rep.V) (fun a => (x a).rep) (stdBlocks (fun a => (x a).1) hx)
  have B : Nonempty ((prodIrr y hy).Equiv (prodIrr w hz)) :=
    equiv_of_iso y w hy hz (GlobalTheory.ProdFlatten.pr_congr hw.symm hy hz)
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem ind₂_prodIrr_equiv_zero {q c r t N : ℕ} (x : Fin 0 → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  have hr : r = 0 := by simpa using hx.symm
  subst hr
  have ht : t = N := by omega
  subst ht
  exact ind₂_prodIrr_empty x y w hw hx hy hz e

theorem ind₂_prodIrr_equiv_pos {p q c r t N : ℕ} (hp : p ≠ 0) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k))
    (w : Fin c → IrrGL (k := k)) (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r)
    (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) :=
  equiv_of_iso_two x y w hx hy hz e
    (GlobalTheory.ProdFlatten.iso_symm (GlobalTheory.ProdFlatten.pr_append x y w hw (Or.inl hp) hx hy hz e))

theorem ind₂_prodIrr_equiv {p q c r t N : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (hz : ∑ a, (w a).1 = N) (e : r + t = N) :
    Nonempty ((ind₂ (stdSum e) (extTensor (prodIrr x hx) (prodIrr y hy))).Equiv (prodIrr w hz)) := by
  cases p with
  | zero => exact ind₂_prodIrr_equiv_zero x y w (by simpa using hw) hx hy hz e
  | succ n => exact ind₂_prodIrr_equiv_pos (Nat.succ_ne_zero n) x y w hw hx hy hz e

theorem prod₂_prodIrr_append : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t),
    Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)) :=
  fun _ _ _ _ _ _ _ _ _ x y hx hy h =>
    ind₂_prodIrr_equiv x y (Fin.append x y) (List.ofFn_fin_append x y) hx hy h rfl

end GlobalTheory.CompanionTheory.ProdStage
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_irreducible_append_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p q r t : ℕ) (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (h : ∑ a, (Fin.append x y a).1 = r + t), Nonempty ((prod₂ (prodIrr x hx) (prodIrr y hy)).Equiv (prodIrr (Fin.append x y) h)) := by
  first | exact @GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append | exact GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append | (intros; apply GlobalTheory.CompanionTheory.ProdStage.prod₂_prodIrr_append <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem KGL_eq_KO (w : Pl E) (n : ℕ) :
    GlobalTheory.LFun.KGL w (n := n) = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
  ext g
  rw [GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff, GlobalTheory.CompanionTheory.IwEntries.mem_KO_iff]

theorem isCompact_KGL (w : Pl E) (n : ℕ) : IsCompact (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem iwGL_le_KGL (w : Pl E) (n : ℕ) : iwGL n w ≤ GlobalTheory.LFun.KGL w (n := n) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SmGL.iwahori_le_KO _ _

theorem isClosed_UL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UL n w : Set (GLw n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
  exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n hc

theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  have h : IsOpen (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) := by
    rw [KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  exact h.preimage (continuous_subtype_val (p := (· ∈ UL n w)))

theorem isCompact_KL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsCompact (KL n w : Set (UL n w)) :=
  (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_KGL w n)

theorem isOpen_iwU (n : ℕ) (w : Pl E) (b : GLw n w) : IsOpen (iwU n w b : Set (UL n w)) := by
  have ho : IsOpen (iwGL n w : Set (GLw n w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n)
  have hcont : Continuous fun γ : UL n w => b⁻¹ * γ.1 * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have e : (iwU n w b : Set (UL n w)) = (fun γ : UL n w => b⁻¹ * γ.1 * b) ⁻¹' (iwGL n w : Set (GLw n w)) := by
    ext γ
    exact GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ
  rw [e]
  exact ho.preimage hcont

theorem iwU_le_KL (n : ℕ) (w : Pl E) (b : GLw n w) (hb : b ∈ GlobalTheory.LFun.KGL w (n := n)) :
    iwU n w b ≤ KL n w := by
  intro γ hγ
  have h1 := iwGL_le_KGL w n ((GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ).1 hγ)
  have h2 : γ.1 = b * (b⁻¹ * γ.1 * b) * b⁻¹ := by group
  rw [KL, Subgroup.mem_subgroupOf, h2]
  exact mul_mem (mul_mem hb h1) (inv_mem hb)

theorem relIndex_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : OpenSubgroup K := ⟨H.subgroupOf K, hH.preimage continuous_subtype_val⟩
  haveI : Finite (K ⧸ (U : Subgroup K)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact Subgroup.index_ne_zero_of_finite

theorem isCompact_support_fU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) (hc : Continuous (cj w)) :
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  set t : GLw n w := b * tdiag ϖ (wexp n l) * b⁻¹ with ht
  have hI : IsCompact (iwU n w b : Set (UL n w)) :=
    GlobalTheory.CompanionTheory.UnitaryWitt.isCompact_iwU hw n b hc
  have hS : IsCompact ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
      ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) :=
    (hI.prod hI).image (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_subtype_val.comp continuous_snd))
  have e : {g : UL n w | fU n w b ϖ l g ≠ 0} = Subtype.val ⁻¹'
      ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
        ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) := by
    ext γ
    simp only [Set.mem_setOf_eq, fU, Set.mem_preimage, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hn
      refine h (if_neg ?_)
      rintro ⟨x, hx, z, hz, e⟩
      exact hn ⟨(x, z), ⟨hx, hz⟩, e.symm⟩
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, e⟩
      rw [if_pos ⟨x, hx, z, hz, e.symm⟩]
      exact one_ne_zero
  rw [e]
  exact (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage hS

theorem levels_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  intro E _ _ _ hU w hw n b hb ϖ l _ _
  have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
  exact ⟨isOpen_KL n w, isCompact_KL hw n hc,
    ⟨isOpen_iwU n w b, iwU_le_KL n w b hb.1, fun k hk => hk⟩,
    relIndex_ne_zero (isOpen_iwU n w b) (isCompact_KL hw n hc),
    isCompact_support_fU hw n b ϖ l hc⟩

end GlobalTheory.CompanionTheory.IwLevels
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupPropertiesStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_level_subgroup_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  exact @GlobalTheory.CompanionTheory.IwLevels.levels_unitary
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem twJ_congr {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    {π' : Representation ℂ G' V} {N : Subgroup G} {N' : Subgroup G'} {θ : N →* ℂˣ} {θ' : N' →* ℂˣ}
    (h : twKer π N θ = twKer π' N' θ') :
    Nontrivial (TwJacquet π N θ) ↔ Nontrivial (TwJacquet π' N' θ') := by
  rw [Submodule.Quotient.nontrivial_iff, Submodule.Quotient.nontrivial_iff, h]

theorem exists_highest (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hn : Nontrivial V)
    (hg : ¬ IsGenericFor ψ π) :
    ∃ n, 0 < n ∧ n < N ∧ Nontrivial (TwJacquet π (derUnip k N n) (derChar k ψ N n)) ∧
      ∀ m < n, Subsingleton (TwJacquet π (derUnip k N m) (derChar k ψ N m)) := by
  have h0 : ¬ Nontrivial (TwJacquet π (derUnip k N 0) (derChar k ψ N 0)) := fun h =>
    hg ((twJ_congr (GlobalTheory.T.derivative_zero_whittaker_kernel k ψ N V π)).1 h)
  rcases N with _ | m
  · exfalso
    refine hg ?_
    show Nontrivial (V ⧸ twKer π (unipB k (Fin 0)) (whitChar ψ 0))
    have hb : twKer π (unipB k (Fin 0)) (whitChar ψ 0) = ⊥ := by
      unfold twKer
      rw [Submodule.span_eq_bot]
      rintro w ⟨u, v, rfl⟩
      have hu : (u : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
      have hu' : u = 1 := Subtype.ext hu
      subst hu'
      simp
    rw [hb]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).toEquiv.nontrivial
  have hex : ∃ n, n ≤ m ∧ Nontrivial (TwJacquet π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n)) := by
    obtain ⟨n, hnm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 m V (resM k π).ρ (isSmooth_comp hs _ continuous_subtype_val) hn
    exact ⟨n, hnm, (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ m n V π)).1 h⟩
  classical
  have hmin := fun (l : ℕ) (hl : l < Nat.find hex) => Nat.find_min hex hl
  obtain ⟨hle, hnt⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.pos_of_ne_zero fun e => h0 (e ▸ hnt), by omega, hnt, fun l hl => ?_⟩
  have := hmin l hl
  rw [not_and] at this
  exact not_nontrivial_iff_subsingleton.1 (this (by omega))

theorem isSmooth_iterPhi (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)), IsSmooth τ.ρ →
    IsSmooth (iterPhi k ψ j τ).ρ
  | 0, _, h => h
  | j + 1, τ, h => isSmooth_iterPhi ψ n j (MRep.phiM k ψ τ) (GlobalTheory.T.smooth_phi_minus k ψ _ _ τ.ρ h)

theorem isSmooth_resM {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin (n + 1)) k) V}
    (h : IsSmooth π) : IsSmooth (resM k π).ρ := isSmooth_comp h _ continuous_subtype_val

theorem isSmooth_deriv (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin (n + j + 1)) k) V} (h : IsSmooth π) : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π) :=
  GlobalTheory.T.smooth_psi_minus k _ _ _ (isSmooth_iterPhi ψ n j _ (isSmooth_resM h))

theorem iterPhi_derUnip (ψ : AddChar k Circle) (n₂ n' : ℕ) (hn : n₂ ≤ n') : ∀ (j : ℕ) (τ : MRep k (n' + j)),
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (derUnipM k n' n₂) (derCharM k ψ n' n₂) ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n' + j) n₂) (derCharM k ψ (n' + j) n₂))
  | 0, _ => ⟨LinearEquiv.refl _ _⟩
  | j + 1, τ => by
    refine Nonempty.elim (iterPhi_derUnip ψ n₂ n' hn j (MRep.phiM k ψ τ)) ?_
    intro e₁
    have hnj : n₂ ≤ n' + j := hn.trans (Nat.le_add_right n' j)
    refine Nonempty.elim (GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ (n' + j) n₂ hnj τ.V τ.ρ) ?_
    intro e₂
    exact ⟨e₁.trans e₂⟩

theorem phi_vanish (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V) (hs : IsSmooth π)
    (hlow : ∀ m < n + 1, Subsingleton (TwJacquet π (derUnip k (n + 1 + j + 1) m) (derChar k ψ (n + 1 + j + 1) m))) :
    Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) := by
  by_contra hcon
  have hnt : Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) :=
    not_subsingleton_iff_nontrivial.1 hcon
  have hT := isSmooth_iterPhi ψ (n + 1) j (resM k π) (isSmooth_resM hs)
  obtain ⟨m, hm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 n _ (phiMinus k ψ (iterPhi k ψ j (resM k π)).ρ)
    (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hT) hnt
  obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ n m hm _ (iterPhi k ψ j (resM k π)).ρ
  obtain ⟨e₁⟩ := iterPhi_derUnip ψ m (n + 1) (by omega) j (resM k π)
  have h3 : Nontrivial (TwJacquet (resM k π).ρ (derUnipM k (n + 1 + j) m) (derCharM k ψ (n + 1 + j) m)) :=
    (e₂.trans e₁).symm.toEquiv.nontrivial
  have h4 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) m V π)).1 h3
  exact not_subsingleton_iff_nontrivial.2 h4 (hlow m (by omega))

theorem deriv_nontrivial (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (h : Nontrivial (TwJacquet π (derUnip k (n + 1 + j + 1) (n + 1)) (derChar k ψ (n + 1 + j + 1) (n + 1)))) :
    Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1) := by
  obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_iterated_phi_equiv k ψ (n + 1) j (resM k π)
  have h2 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) (n + 1) V π)).2 h
  exact e.toEquiv.nontrivial

theorem detChar_zero {n : ℕ} (g : GL (Fin n) k) : ((detChar (Fin n) (absPow k ((0 : ℕ) : ℂ)) g : ℂˣ) : ℂ) = 1 := by
  have : absPow k ((0 : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_zero, absPow_zero]
  rw [this]
  simp [detChar]


set_option maxHeartbeats 2000000 in
theorem pair_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) : ∀ (j s : ℕ) (τ τ' : MRep k (n + 1 + j)),
    IsSmooth τ.ρ → IsSmooth τ'.ρ → ∀ B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1 + j)) v v', B (τ.ρ p v) (τ'.ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j τ').ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (derivM k ψ j τ g w) (derivM k ψ⁻¹ j τ' g w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + j : ℕ) : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0)
  | 0, s, τ, τ', hs, hs', B, hB, hn, hv =>
    GlobalTheory.T.invariant_pairing_mirabolic_vanishing k ψ hc h1 n s τ.V τ'.V τ.ρ τ'.ρ hs hs' B hB hn hv
  | j + 1, s, τ, τ', hs, hs', B, hB, hn, hv => by
    refine Exists.elim (GlobalTheory.T.invariant_pairing_mirabolic_smooth k ψ hc h1
      (n + 1 + j) s τ.V τ'.V τ.ρ τ'.ρ hs hs' B hB hn) ?_
    rintro B₁ ⟨hB₁, hn₁⟩
    refine Exists.elim (pair_iter ψ hc h1 n j (s + 1) (MRep.phiM k ψ τ) (MRep.phiM k ψ⁻¹ τ')
      (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hs) (GlobalTheory.T.smooth_phi_minus k ψ⁻¹ _ _ _ hs') B₁ hB₁ hn₁ hv) ?_
    rintro B₂ ⟨hB₂, hn₂⟩
    refine ⟨B₂, fun g w w' => ?_, hn₂⟩
    have e : s + (j + 1) = s + 1 + j := by omega
    rw [e]
    exact hB₂ g w w'


set_option maxHeartbeats 2000000 in
theorem pair_deriv (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V V' : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (π' : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V') (hs : IsSmooth π) (hs' : IsSmooth π')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π g v) (π' g v') = B v v') (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (hv : Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n))) :
    ∃ B' : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j (resM k π')).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (GlobalTheory.BZMir.deriv k ψ j π g w) (GlobalTheory.BZMir.deriv k ψ⁻¹ j π' g w') =
        ((detChar (Fin (n + 1)) (absPow k (j : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  have hB0 : ∀ (p : Mir k (n + 1 + j)) v v', B ((resM k π).ρ p v) ((resM k π').ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k ((0 : ℕ) : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v' := by
    intro p v v'
    rw [detChar_zero, one_mul]
    exact hB (p : GL (Fin (n + 1 + j + 1)) k) v v'
  obtain ⟨B', h2, h3⟩ := pair_iter ψ hc h1 n j 0 (resM k π) (resM k π') (isSmooth_resM hs) (isSmooth_resM hs') B
    hB0 hn hv
  refine ⟨B', fun g w w' => ?_, h3⟩
  have := h2 g w w'
  rwa [Nat.zero_add] at this

end Proofs
end GlobalTheory.CompanionTheory.BZCuspPair
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp [ptCoord]

theorem isMultiProjPrime_ptIdeal (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsMultiProjPrime (ptIdeal x) :=
  ⟨RingHom.ker_isPrime _, GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal (ptCoord x),
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant (ptCoord x) (ptChart x) fun k => by
      rw [ptCoord_ptChart]; exact one_ne_zero⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebra
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep
open PositivityTheory.Rg.BcB.F.Eig
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SphLine

section Abstract

open GlobalTheory.LFun GlobalTheory.LFun.SatCompare GlobalTheory.LocGL

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem finrank_fixed_eq_one (π : Representation ℂ G V) (K : Subgroup G) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) (hcomm : ∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁)
    (hπ : GlobalTheory.LGrp.IsIrrSmooth π) (hfd : FiniteDimensional ℂ (fixed π K)) (hne : fixed π K ≠ ⊥) :
    Module.finrank ℂ (fixed π K) = 1 := by
  obtain ⟨x₀, hx₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have key : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x₀) = c • x₀ := fun g => by
    obtain ⟨N, hN, e⟩ := HeckeScalar.heckeVec_dosetInd_eq_idem hπ hc hK g hx₀
    obtain ⟨c, hc'⟩ := HeckeScalar.exists_scalar G V π K hc hK hcomm hπ hfd _ (Final.DosetIndMem G K ℂ g)
    have h1 := hc' x₀ hx₀
    rw [e] at h1
    refine ⟨N⁻¹ * c, ?_⟩
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have all : ∀ a : MonoidAlgebra ℂ G, ∃ c : ℂ, idem hπ.1 hc (orbitMap π x₀ a) = c • x₀ := fun a => by
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have : orbitMap π x₀ (MonoidAlgebra.of ℂ G g) = π g x₀ := by
        show π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x₀ = _
        simp
      rw [this]; exact key g
    | add a b ha hb =>
      obtain ⟨c, hc₁⟩ := ha
      obtain ⟨d, hd⟩ := hb
      have : orbitMap π x₀ (a + b) = orbitMap π x₀ a + orbitMap π x₀ b := map_add _ _ _
      exact ⟨c + d, by rw [this, map_add (f := _), hc₁, hd, add_smul]⟩
    | smul r a ha =>
      obtain ⟨c, hc₁⟩ := ha
      have : orbitMap π x₀ (r • a) = r • orbitMap π x₀ a := map_smul _ _ _
      exact ⟨r * c, by rw [this, map_smul, hc₁, smul_smul]⟩
  refine (finrank_eq_one_iff_of_nonzero' (⟨x₀, hx₀⟩ : fixed π K) fun e => h0 (congrArg Subtype.val e)).2 ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, ha⟩ := orbitMap_surjective hπ.2 h0 x
  obtain ⟨c, hc₁⟩ := all a
  refine ⟨c, Subtype.ext ?_⟩
  rw [ha, idem_of_mem hπ.1 hc hx] at hc₁
  exact hc₁.symm

end Abstract

section Gelfand

theorem conv_comm_sub {A : Type} [Group A] (H : Subgroup A) (K : Subgroup H) (θ : A → A)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hi : ∀ x, θ (θ x) = x) (hH : ∀ x ∈ H, θ x ∈ H)
    (hK : ∀ x : H, x ∈ K → (⟨θ x, hH _ x.2⟩ : H) ∈ K)
    (hdc : ∀ g : H, ∃ a b : K, (⟨θ g, hH _ g.2⟩ : H) = (a : H) * g * b)
    (f₁ f₂ : H → ℂ) (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : conv K f₁ f₂ = conv K f₂ f₁ :=
  Formalism.UG.P.heckecomm_gelfand K (fun x : H => (⟨θ x, hH _ x.2⟩ : H)) (fun x y => Subtype.ext (hm _ _))
    (fun x => Subtype.ext (hi _)) hK hdc f₁ f₂ hf₁ hf₂

theorem dc_of_decomp {A : Type} [Group A] (H : Subgroup A) (K : Subgroup H) (θ : A → A)
    (hm : ∀ x y, θ (x * y) = θ y * θ x) (hH : ∀ x ∈ H, θ x ∈ H)
    (hK : ∀ x : H, x ∈ K → (⟨θ x, hH _ x.2⟩ : H) ∈ K) {g k₁ k₂ t : H} (h₁ : k₁ ∈ K) (h₂ : k₂ ∈ K)
    (ht : θ t = t) (e : g = k₁ * t * k₂) : ∃ a b : K, (⟨θ g, hH _ g.2⟩ : H) = (a : H) * g * b := by
  have hm' : ∀ x y : H, (⟨θ (x * y : H), hH _ (x * y).2⟩ : H) = ⟨θ y, hH _ y.2⟩ * ⟨θ x, hH _ x.2⟩ :=
    fun x y => Subtype.ext (hm _ _)
  have ht' : (⟨θ t, hH _ t.2⟩ : H) = t := Subtype.ext ht
  refine ⟨⟨_, K.mul_mem (hK _ h₂) (K.inv_mem h₁)⟩, ⟨_, K.mul_mem (K.inv_mem h₂) (hK _ h₁)⟩, ?_⟩
  subst e
  simp only [hm', ht']
  group

end Gelfand

section Transpose

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem tr_mem_UJ (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {h : GL (Fin n) L} (hh : h ∈ UJ σ (antiJ L n)) :
    Formalism.UG.P.heckecomm_tr h ∈ UJ σ (antiJ L n) := by
  have hJ : antiJ L n * antiJ L n = 1 := GlobalTheory.UnitarySwap.antiJ_mul_self
  have hJσ : (antiJ L n).map σ = antiJ L n := by
    ext i j
    simp only [Matrix.map_apply, antiJ]
    split_ifs <;> simp
  have h0 : cT σ h.val * antiJ L n * h.val = antiJ L n := hh
  have hmm : ((h.val.map σ)ᵀ).map σ = h.valᵀ := by
    ext i j
    simp [hσ]
  have h1 : h.valᵀ * antiJ L n * h.val.map σ = antiJ L n := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) L => M.map σ) h0
    simp only [cT, Matrix.map_mul, hJσ, hmm] at this
    exact this
  have h2 : h.valᵀ * (antiJ L n * h.val.map σ * antiJ L n) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, hJ]
  have h3 : (antiJ L n * h.val.map σ * antiJ L n) * h.valᵀ = 1 := mul_eq_one_comm.1 h2
  change cT σ (Formalism.UG.P.heckecomm_tr h).val * antiJ L n * (Formalism.UG.P.heckecomm_tr h).val = antiJ L n
  have hc : cT σ (Formalism.UG.P.heckecomm_tr h).val = h.val.map σ := by
    ext i j
    simp [cT, Formalism.UG.P.heckecomm_tr_val]
  rw [hc, Formalism.UG.P.heckecomm_tr_val]
  calc h.val.map σ * antiJ L n * h.valᵀ
      = antiJ L n * ((antiJ L n * h.val.map σ * antiJ L n) * h.valᵀ) := by
        simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul]
    _ = antiJ L n := by rw [h3, Matrix.mul_one]

def thb (b x : GL (Fin n) L) : GL (Fin n) L := b * Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) * b⁻¹

theorem thb_mul (b x y : GL (Fin n) L) : thb b (x * y) = thb b y * thb b x := by
  unfold thb
  rw [show b⁻¹ * (x * y) * b = (b⁻¹ * x * b) * (b⁻¹ * y * b) by group, Formalism.UG.P.heckecomm_tr_mul]
  group

theorem thb_thb (b x : GL (Fin n) L) : thb b (thb b x) = x := by
  unfold thb
  rw [show b⁻¹ * (b * Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) * b⁻¹) * b = Formalism.UG.P.heckecomm_tr (b⁻¹ * x * b) by group,
    Formalism.UG.P.heckecomm_tr_tr]
  group

end Transpose

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  by_cases hw : IsSplitAt w
  · have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact isClosed_univ
  · rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1

theorem coe_KL (n : ℕ) (w : Pl E) :
    (KL n w : Set (UL n w)) = Subtype.val ⁻¹' (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) := by
  ext x
  exact Subgroup.mem_subgroupOf

theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  rw [coe_KL]
  exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage continuous_subtype_val

theorem isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) : IsCompact (KL n w : Set (UL n w)) := by
  rw [coe_KL]
  exact (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2

theorem conv_comm_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (f₁ f₂ : UL n w → ℂ)
    (hf₁ : IsBiInv (KL n w) f₁) (hf₂ : IsBiInv (KL n w) f₂) : conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := by
  have hT : UL n w = ⊤ := if_pos hw
  have hmem : ∀ x : GLw n w, x ∈ UL n w := fun x => by
    rw [hT]
    trivial
  refine conv_comm_sub (UL n w) (KL n w) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x _ => hmem _) (fun x hx => ?_) (fun g => ?_) f₁ f₂ hf₁ hf₂
  · exact Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _ (Subgroup.mem_subgroupOf.1 hx))
  · obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1
    exact ⟨⟨⟨a.1, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2⟩, ⟨⟨b.1, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2⟩,
      Subtype.ext e⟩

theorem conv_comm_inert (hU : Unr E) {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (f₁ f₂ : UL n w → ℂ)
    (hf₁ : IsBiInv (KL n w) f₁) (hf₂ : IsBiInv (KL n w) f₂) : conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := by
  obtain ⟨-, hcc, -, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)
  have hb' : cT (cj w) b.val * b.val = antiJ _ n := by simpa using hb
  have hconj : ∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ _ n) := fun g => by
    rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b g hb'
  have hback : ∀ x ∈ UL n w, b⁻¹ * x * b ∈ UJ (cj w) (antiJ _ n) := fun x hx =>
    (hconj _).1 (by rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group])
  have hH : ∀ x ∈ UL n w, thb b x ∈ UL n w := fun x hx =>
    (hconj _).2 (tr_mem_UJ _ hcc (hback x hx))
  have hbi := (GlobalTheory.LFun.KGL w (n := n)).inv_mem hbK
  have hK : ∀ x : UL n w, x ∈ KL n w → (⟨thb b x, hH _ x.2⟩ : UL n w) ∈ KL n w := fun x hx =>
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (Formalism.UG.P.heckecomm_tr_mem (Ov E w) _
      (mul_mem (mul_mem hbi (Subgroup.mem_subgroupOf.1 hx)) hbK))) hbi)
  have hO : Ov E w = intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  have hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) := fun k hk => by
    have h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n) := Subgroup.mem_subgroupOf.1 hk
    show k.1 ∈ (bc (Ov E w).subtype).range
    rw [hO]
    exact (Subgroup.mem_inf.1 h).2
  refine conv_comm_sub (UL n w) (KL n w) (thb b) (thb_mul b) (thb_thb b) hH hK (fun g => ?_) f₁ f₂ hf₁ hf₂
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback g.1 g.2⟩
  have e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1 := congrArg Subtype.val e
  have hk : ∀ k ∈ KU (cj w) n, (⟨b * k.1 * b⁻¹, (hconj _).2 k.2⟩ : UL n w) ∈ KL n w := fun k hk =>
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK (hKU k hk)) hbi)
  refine dc_of_decomp (UL n w) (KL n w) (thb b) (thb_mul b) hH hK (hk k₁ hk₁) (hk k₂ hk₂)
    (t := ⟨b * t.1 * b⁻¹, (hconj _).2 t.2⟩) ?_ (Subtype.ext ?_)
  · have h1 : Formalism.UG.P.heckecomm_tr (t.1 : GLw n w) = t.1 := Units.ext (by
      rw [Formalism.UG.P.heckecomm_tr_val, ht]
      exact Matrix.diagonal_transpose _)
    show thb b (b * t.1 * b⁻¹) = b * t.1 * b⁻¹
    unfold thb
    rw [show b⁻¹ * (b * t.1 * b⁻¹) * b = t.1 by group, h1]
  · show g.1 = b * k₁.1 * b⁻¹ * (b * t.1 * b⁻¹) * (b * k₂.1 * b⁻¹)
    calc g.1 = b * (b⁻¹ * g.1 * b) * b⁻¹ := by group
      _ = _ := by
        rw [e']
        group

theorem sphOne : SphOne := by
  intro E _ _ _ hU n w σ hne hfd
  have hcomm : ∀ f₁ ∈ Hecke ℂ (KL n w), ∀ f₂ ∈ Hecke ℂ (KL n w),
      conv (KL n w) f₁ f₂ = conv (KL n w) f₂ f₁ := fun f₁ h₁ f₂ h₂ => by
    by_cases hw : IsSplitAt w
    · exact conv_comm_split hw f₁ f₂ h₁.1 h₂.1
    · exact conv_comm_inert hU hw f₁ f₂ h₁.1 h₂.1
  exact finrank_fixed_eq_one σ.ρ (KL n w) (isCompact_KL hU n w)
    (PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ (isOpen_KL n w) (isCompact_KL hU n w)) hcomm
    ⟨σ.smooth, σ.irred⟩ hfd hne

theorem locAlg_sphOne : LocAlg → SphOne := fun _ => sphOne

end Local

end GlobalTheory.CompanionTheory.SphLine
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalOneOfLocalAlgebraStatement
open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_one_of_local_algebra : LocAlg → SphOne := by
  first | exact @GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | exact GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne | (intros; apply GlobalTheory.CompanionTheory.SphLine.locAlg_sphOne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SocleFrob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_smul_id {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin n) k) X) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (φ : X →ₗ[ℂ] X) (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  haveI : ρ.IsIrreducible := hi
  have hs' : GroundTheory.Automorphic.IsSmooth ρ := hs
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hs').2
    (⟨φ, fun g => LinearMap.ext fun x => hφ g x⟩ : Representation.IntertwiningMap ρ ρ)
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  exact (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm

theorem isIrreducible_piTensor {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    exists_eq_smul_id _ (x a).2.rep.smooth (x a).2.rep.irr φ hφ

theorem jm_ne_zero_of_isSocle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  intro k _ _ _ _ h N x hd V _ _ π _ _ hS
  obtain ⟨hi, f, hf, -⟩ := hS
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : 1 ≤ Zc.jm x hd π :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac (stdBlocks (fun a => (x a).1) hd) (isIrreducible_piTensor x) f
      ⟨v, fun h0 => hv (hf (h0.trans (map_zero f).symm))⟩
  exact ENat.one_le_iff_ne_zero.1 h1

end GlobalTheory.CompanionTheory.SocleFrob

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos_of_socle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | exact GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle | (intros; apply GlobalTheory.CompanionTheory.SocleFrob.jm_ne_zero_of_isSocle <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.JacquetCongr

theorem jm_congr_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  intro k _ _ _ _ h N x hd V W _ _ _ _ π σ ⟨φ⟩
  exact jhMult_congr_right _ (GlobalTheory.SmGL.Exponents.jacEquiv _ φ)

end GlobalTheory.CompanionTheory.JacquetCongr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquivStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  first | exact @GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | exact GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv | (intros; apply GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem mem_ptIdeal_iff_aeval_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (f : Geo.MRing (Bk n)) (a : Fin (m + 1) → ℕ), Geo.IsMultiHomog f a → (f ∈ ptIdeal x ↔ aeval (ptCoord x) f = 0) := by
  intro m n x f a hf
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.mem_mCoordIdeal_iff (ptCoord x) hf

end GlobalTheory.CompanionTheory.MPDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.DualForms

theorem exists_revOrdered_dual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k →
    ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL (k := k)), LFactors 𝔪 x →
      ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  intro k _ _ _ _ hA hD 𝔪 h x hx
  obtain ⟨Δ, ⟨-, hord⟩, hL⟩ := hx
  refine ⟨fun i => segDual (Δ i), fun i j hij hp => hord i j hij ((GlobalTheory.T.segment_dual_precedes_iff hA _ _).1 hp), fun i => ?_⟩
  rw [GlobalTheory.CompanionTheory.Zcore.dualCl_eq_of hA (x i)]
  exact (hD (Δ i) (x i).rep (hL i)).of_equiv (IrrGL.equivOf _ _ _)

end GlobalTheory.CompanionTheory.DualForms
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrderedStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_factors_dual_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k → ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL (k := k)), LFactors 𝔪 x → ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  first | exact @GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | exact GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual | (intros; apply GlobalTheory.CompanionTheory.DualForms.exists_revOrdered_dual <;> assumption)
end
end
