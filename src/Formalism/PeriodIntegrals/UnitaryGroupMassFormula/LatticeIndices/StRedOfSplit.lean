module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.HaarIdx
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

section Loc

variable {D : D7} (X : HidaSetting D)

abbrev Op (p : TypX X) : Type := p.1.adicCompletionIntegers X.B.I.F

def StResZ (p : TypX X) : Prop :=
  ∃ π : Op X p →+* ZMod (gOf p), Function.Surjective π ∧
    RingHom.ker π = Ideal.span {((gOf p : ℕ) : Op X p)}

def StLatGL (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      ∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p

end Loc

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm

theorem card_conj {G : Type} [Group G] (H : Subgroup G) (c : G) :
    Nat.card (H.map (MulAut.conj c).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def LevelReductionImage (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ₀ ∧
      (∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ A : Subgroup K, Subtype.val '' (A : Set K) = KppX X hb p ∧ ρ₀.ker ≤ A ∧
        ∃ c, A.map ρ₀ = (nuG (ZMod (gOf p)) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

def ParabolicReductionImage (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ₀ ∧
      (∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ B : Subgroup K, Subtype.val '' (B : Set K) = KnatX X u p ∧ ρ₀.ker ≤ B ∧
        ∃ c, B.map ρ₀ = (sG (ZMod (gOf p)) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

theorem stImA_of (p : TypX X) (h : LevelReductionImage X hb p) : StImA X hb p := by
  obtain ⟨K₀, hK₀, ρ₀, hρ₀, hker₀, A, hA, hkA, c, hc⟩ := h
  intro K hK ρ hρ hker
  have hKK : K = K₀ := SetLike.coe_injective (hK.trans hK₀.symm)
  subst hKK
  have hkers : ρ.ker = ρ₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hker₀]
  have hkA' : ρ.ker ≤ A := hkers.le.trans hkA
  refine ⟨A, hA, hkA', ?_⟩
  have hq : ∀ f : ↥K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)),
      Nat.card (A.map f) = Nat.card (↥A ⧸ (f.comp A.subtype).ker) := by
    intro f
    have hr : A.map f = (f.comp A.subtype).range := by
      first
      | rw [MonoidHom.range_comp, Subgroup.range_subtype]
      | rw [MonoidHom.range_comp, Subgroup.subtype_range]
    rw [hr]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp A.subtype)).toEquiv.symm
  have hk2 : (ρ.comp A.subtype).ker = (ρ₀.comp A.subtype).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, hker, hker₀]
  rw [hq ρ, hk2, ← hq ρ₀, hc, card_conj]
  haveI : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  first
  | exact card_nuG (ZMod (gOf p)) D.R.rS D.R.k
  | (rw [card_nuG]; unfold nnC ukC; rfl)
  | (rw [card_nuG]; unfold nnC ukC)

theorem stImB_of (u : D.what₂.Word) (p : TypX X) (h : ParabolicReductionImage X u p) : StImB X u p := by
  obtain ⟨K₀, hK₀, ρ₀, hρ₀, hker₀, A, hA, hkA, c, hc⟩ := h
  intro K hK ρ hρ hker
  have hKK : K = K₀ := SetLike.coe_injective (hK.trans hK₀.symm)
  subst hKK
  have hkers : ρ.ker = ρ₀.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hker₀]
  have hkA' : ρ.ker ≤ A := hkers.le.trans hkA
  refine ⟨A, hA, hkA', ?_⟩
  have hq : ∀ f : ↥K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)),
      Nat.card (A.map f) = Nat.card (↥A ⧸ (f.comp A.subtype).ker) := by
    intro f
    have hr : A.map f = (f.comp A.subtype).range := by
      first
      | rw [MonoidHom.range_comp, Subgroup.range_subtype]
      | rw [MonoidHom.range_comp, Subgroup.subtype_range]
    rw [hr]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp A.subtype)).toEquiv.symm
  have hk2 : (ρ.comp A.subtype).ker = (ρ₀.comp A.subtype).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, hker, hker₀]
  rw [hq ρ, hk2, ← hq ρ₀, hc, card_conj]
  haveI : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  first
  | exact card_sG (ZMod (gOf p)) D.R.rS D.R.k
  | (rw [card_sG]; unfold glkC nnC; rfl)
  | (rw [card_sG]; unfold glkC nnC)

end MassDataIdxSteps
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatOpenCompact
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.T2SpaceScalarTensorExt
noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fdFE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance imt (v : HeightOneSpectrum (𝓞 F)) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

theorem t2Space_scalarTensorExt (v : HeightOneSpectrum (𝓞 F)) : T2Space (Fv F v ⊗[F] E) := by
  have := fdFE (F := F) (E := E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  exact T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem ratV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i; exact map_zero _

theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i; exact map_add _ _ _

theorem ratV_zsmul (m : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (m • x) = m • ratV (F := F) (Fv F v) x := by
  funext i; exact map_zsmul _ _ _

def mulE (e : E) : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (LinearMap.mulLeft (Fv F v) (inclR (F := F) (Fv F v) e)) ∘ₗ LinearMap.proj i

theorem mulE_apply (e : E) (w : Fin n → Fv F v ⊗[F] E) (i : Fin n) :
    mulE v e w i = inclR (F := F) (Fv F v) e * w i := rfl

theorem spanTop (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span (Fv F v) (ratV (F := F) (Fv F v) '' (L : Set (Fin n → E))) = ⊤ := by
  set W := Submodule.span (Fv F v) (ratV (F := F) (Fv F v) '' (L : Set (Fin n → E))) with hW
  have h1 : ∀ a : 𝓞 E, ∀ w ∈ W, mulE v (algebraMap (𝓞 E) E a) w ∈ W := by
    intro a w hw
    have : W.map (mulE v (algebraMap (𝓞 E) E a)) ≤ W := by
      rw [hW, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      funext i
      show inclR (F := F) (Fv F v) ((a • x) i) = inclR (F := F) (Fv F v) (algebraMap (𝓞 E) E a) * inclR _ (x i)
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact this ⟨w, hw, rfl⟩
  have h2 : ∀ e : E, ∀ w ∈ W, mulE v e w ∈ W := by
    intro e w hw
    obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := e) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e))
    let a : 𝓞 E := IsIntegralClosure.mk' (𝓞 E) (y • e) hyi
    have ha : algebraMap (𝓞 E) E a = y • e := IsIntegralClosure.algebraMap_mk' _ _ _
    have hyF : ((y : Fv F v)) ≠ 0 := by
      rw [← map_intCast (algebraMap F (Fv F v))]
      exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hy0)
    have key : algebraMap (Fv F v) (Fv F v ⊗[F] E) ((y : Fv F v))⁻¹ * (y : Fv F v ⊗[F] E) = 1 := by
      rw [← map_intCast (algebraMap (Fv F v) (Fv F v ⊗[F] E)), ← map_mul, inv_mul_cancel₀ hyF, map_one]
    have : mulE v e w = ((y : Fv F v))⁻¹ • mulE v (algebraMap (𝓞 E) E a) w := by
      funext i
      rw [Pi.smul_apply, mulE_apply, mulE_apply, ha, zsmul_eq_mul, map_mul, map_intCast, Algebra.smul_def,
        ← mul_assoc, ← mul_assoc, key, one_mul]
    rw [this]; exact W.smul_mem _ (h1 a w hw)
  have h3 : ∀ x : Fin n → E, ratV (F := F) (Fv F v) x ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [ratV_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [ratV_add]; exact W.add_mem hx hy
    | smul e x _ hx =>
        have : ratV (F := F) (Fv F v) (e • x) = mulE v e (ratV (F := F) (Fv F v) x) := by
          funext i; exact map_mul _ _ _
        rw [this]; exact h2 e _ hx
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine W.sum_mem fun i _ => ?_
  generalize w i = t
  induction t using TensorProduct.induction_on with
  | zero => rw [Pi.single_zero]; exact W.zero_mem
  | tmul r e =>
      have : (Pi.single i (r ⊗ₜ[F] e) : Fin n → Fv F v ⊗[F] E) =
          r • ratV (F := F) (Fv F v) (Pi.single i e) := by
        funext j
        by_cases h : j = i
        · subst h
          simp [ratV, inclR, TensorProduct.smul_tmul']
        · simp [ratV, h]
      rw [this]; exact W.smul_mem r (h3 _)
  | add s t hs ht => rw [Pi.single_add]; exact W.add_mem hs ht

end MassDataIdxK
end
end

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem latImage (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hfg : L.FG) :
    ∃ (m : ℕ) (b : Fin m → (Fin n → Fv F v ⊗[F] E)),
      (∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E))) ∧
      Submodule.span (Fv F v) (Set.range b) = ⊤ ∧
      (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
        (fun c : Fin m → Fv F v => ∑ i, c i • b i) ''
          Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hfg.restrictScalars (R := ℤ))
  have hsL : ∀ i, s i ∈ L := fun i => by
    have : s i ∈ Submodule.span ℤ (Set.range s) := Submodule.subset_span ⟨i, rfl⟩
    rw [hs] at this; exact this
  set b : Fin m → (Fin n → Fv F v ⊗[F] E) := fun i => ratV (F := F) (Fv F v) (s i) with hb
  have hlat : latLoc (E := E) v (L : Set (Fin n → E)) =
      Submodule.span (v.adicCompletionIntegers F) (Set.range b) := by
    apply le_antisymm
    · unfold latLoc
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => rw [ratV_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [ratV_add]; exact add_mem hx hy
      | smul k x _ hx => rw [ratV_zsmul]; exact zsmul_mem hx k
    · unfold latLoc
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨s i, hsL i, rfl⟩
  have hbΛ : ∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E)) := fun i => by
    rw [hlat]; exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨m, b, hbΛ, ?_, ?_⟩
  · rw [eq_top_iff, ← spanTop v L hL, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have : ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v (L : Set (Fin n → E)) :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hlat] at this
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers F) (Fv F v) _ this
  · ext x
    rw [SetLike.mem_coe, hlat, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun i => ⟨d i, hd i (Set.mem_univ _)⟩, rfl⟩

theorem latOpenCompact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsCompact (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  obtain ⟨m, b, -, hsp, heq⟩ := latImage v L hL hfg
  let Φ : (Fin m → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun c => ∑ i, c i • b i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [Φ, Pi.single_apply]
  have himg : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      Φ '' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := heq
  rw [himg]
  refine ⟨IsModuleTopology.isOpenMap_of_surjective hsurj _
    (isOpen_set_pi Set.finite_univ fun i _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v), ?_⟩
  exact (isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (IsModuleTopology.continuous_of_linearMap Φ)

end MassDataIdxK
end
end
