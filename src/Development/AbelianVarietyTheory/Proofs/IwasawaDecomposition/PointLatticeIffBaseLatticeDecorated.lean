module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
public import Formalism.LocalToGlobal.Columns.RowFormsSum
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecorated
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecorated
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtLat

theorem latS_deco_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q S k t y p ht hS hp x
  have hp0 : IsPtOf hc (y * (k * t)) (extTo ∅ p) :=
    hp.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)
  obtain ⟨hg, hd⟩ := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ _ _ rfl).1 hp0
  have hd' : p.deco.1 = decoRaw ST SG (y * (k * t)) := hd
  have hcar := decoRaw_carries hc n ST SG hg x
  rw [hd']
  refine hcar.trans ?_
  have hst := mirabolicLevel_le_stabilizer_base hc n ST (principal_le_congruence_subgroup hc n ST SG (Subgroup.inv_mem _ ht))
  have e : (((y * (k * t))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
      ((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  exact ((hst _).symm).trans (hS _).symm

end GlobalTheory.Mem.Col2.PtLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecoratedStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointLattice_iff_baseLattice_decorated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  first | exact @GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | exact GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | (intros; apply GlobalTheory.Mem.Col2.PtLat.latS_deco_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabIffMemConj
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TopCh

theorem stab_iff_mem_conj : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → IsPtOf hc (y * k') p → ∀ γ : UF E n, (∃ (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p) ↔ ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ U k' y p hlev hp γ
  have hγ : IsPtOf hc (ratAd F γ * (y * k')) (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
    first | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ (y * k') p hp | exact GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd (hc := hc) γ hp | (apply GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd <;> assumption)
  have hx : IsPtOf hc (y * (y⁻¹ * ratAd F γ * y) * k') (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
    have : y * (y⁻¹ * ratAd F γ * y) * k' = ratAd F γ * (y * k') := by group
    rw [this]; exact hγ
  have key := hlev y (y⁻¹ * ratAd F γ * y) p _ hp hx
  have hmem : ratAd F γ ∈ U.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * ratAd F γ * y ∈ U := by
    constructor
    · rintro ⟨u, hu, he⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
      rw [← he]; simpa [mul_assoc] using hu
    · intro hu
      refine ⟨_, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [hmem, key]
  constructor
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have e1 : ((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (γ, h.1, θ.1) := by
      ext <;> simp
    rw [e1, mul_smul, he]
  · rintro ⟨h, θ, he⟩
    refine ⟨h⁻¹, θ⁻¹, ?_⟩
    have : ((γ, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (γ, 1, 1) := by
      ext <;> simp
    rw [this, mul_smul, ← he, ← mul_smul]
    have : ((1, (h⁻¹).1, (θ⁻¹).1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * (1, h.1, θ.1) = 1 := by
      ext <;> simp
    rw [this, one_smul]

end GlobalTheory.Mem.Col2.TopCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntMaxFinExt

theorem mem_maximalIdeal_iff_norm_lt_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) [IsLocalRing ↥(Loc.OL K)] (y : ↥(Loc.OL K)), y ∈ IsLocalRing.maximalIdeal ↥(Loc.OL K) ↔ ‖((y : ↥K.1) : PadicAlgCl l)‖ < 1 := by
  intro l _ K _ y
  have hle : ∀ z : ↥(Loc.OL K), ‖((z : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := fun z =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (z : ↥K.1)).1 z.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hlt
    have h1 : ‖((y : ↥K.1) : PadicAlgCl l)‖ = 1 := le_antisymm (hle y) (not_lt.1 hlt)
    have hy0 : (y : ↥K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    have hinv : ((y : ↥K.1)⁻¹ : ↥K.1) ∈ Loc.OL K := by
      rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
      rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
    apply hnu
    refine ⟨⟨y, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show (y : ↥K.1) * (y : ↥K.1)⁻¹ = 1
      exact mul_inv_cancel₀ hy0
    · apply Subtype.ext
      show (y : ↥K.1)⁻¹ * (y : ↥K.1) = 1
      exact inv_mul_cancel₀ hy0
  · intro hlt hu
    obtain ⟨u, rfl⟩ := hu
    have hm : ((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l)) * ((((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l) = 1 := by
      have := congrArg (fun z : ↥(Loc.OL K) => (((z : ↥K.1)) : PadicAlgCl l)) u.mul_inv
      exact this
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    have h2 := hle ((u⁻¹ : (↥(Loc.OL K))ˣ) : ↥(Loc.OL K))
    have h0 : 0 ≤ ‖((((u : ↥(Loc.OL K)) : ↥K.1) : PadicAlgCl l))‖ := norm_nonneg _
    nlinarith

end GlobalTheory.IntMaxFinExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximalIdeal_OL_iff_norm_lt_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) [IsLocalRing ↥(Loc.OL K)] (y : ↥(Loc.OL K)), y ∈ IsLocalRing.maximalIdeal ↥(Loc.OL K) ↔ ‖((y : ↥K.1) : PadicAlgCl l)‖ < 1 := by
  first | exact @GlobalTheory.IntMaxFinExt.mem_maximalIdeal_iff_norm_lt_one | exact GlobalTheory.IntMaxFinExt.mem_maximalIdeal_iff_norm_lt_one | (intros; apply GlobalTheory.IntMaxFinExt.mem_maximalIdeal_iff_norm_lt_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOf
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.IntOfFinExt

theorem mem_integer_iff_norm_le_one (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) :
    x ∈ (PadicAlgCl.valued l).v.integer ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  show ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem mem_intOf_iff (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (x : PadicAlgCl l) : x ∈ intOf l K ↔ x ∈ K ∧ ‖x‖ ≤ 1 := by
  unfold intOf
  rw [Subring.mem_inf, mem_integer_iff_norm_le_one]
  rfl

def toIntOf (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) : ↥(Loc.OL K) →+* ↥(intOf l K.1) :=
  RingHom.codRestrict ((K.1.val.toRingHom).comp (Loc.OL K).val.toRingHom) (intOf l K.1)
    (fun y => (mem_intOf_iff l K.1 _).2
      ⟨((y : ↥K.1)).2, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (y : ↥K.1)).1 y.2⟩)

theorem toIntOf_bijective (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) :
    Function.Bijective (toIntOf l K) := by
  constructor
  · intro a b h
    have h' : (((a : ↥K.1) : PadicAlgCl l)) = ((b : ↥K.1) : PadicAlgCl l) :=
      congrArg (fun w : ↥(intOf l K.1) => (w : PadicAlgCl l)) h
    exact Subtype.ext (Subtype.ext h')
  · intro z
    obtain ⟨hK, hn⟩ := (mem_intOf_iff l K.1 z).1 z.2
    refine ⟨⟨⟨(z : PadicAlgCl l), hK⟩,
      (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K ⟨(z : PadicAlgCl l), hK⟩).2 hn⟩, ?_⟩
    exact Subtype.ext rfl

theorem exists_ringEquiv_intOf : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l),
    ∃ e : ↥(Loc.OL K) ≃+* ↥(intOf l K.1), ∀ y, (e y : PadicAlgCl l) = ((y : ↥K.1) : PadicAlgCl l) :=
  fun l _ K => ⟨RingEquiv.ofBijective (toIntOf l K) (toIntOf_bijective l K), fun _ => rfl⟩

end GlobalTheory.IntOfFinExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOfStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_finExtIntegers_padicIntOf : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), ∃ e : ↥(Loc.OL K) ≃+* ↥(intOf l K.1), ∀ y, (e y : PadicAlgCl l) = ((y : ↥K.1) : PadicAlgCl l) := by
  first | exact @GlobalTheory.IntOfFinExt.exists_ringEquiv_intOf | exact GlobalTheory.IntOfFinExt.exists_ringEquiv_intOf | (intros; apply GlobalTheory.IntOfFinExt.exists_ringEquiv_intOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterAtQFiniteOrderAndTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterAtQFiniteOrderAndTrivial
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem rhoT_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (t x : GL (Fin n) (AfE F E)) (hx : rhoP F P x = 1) : rhoT F P t x = 1 := by
  show rhoP F P (MulAut.conj t⁻¹ x) = 1
  rw [MulAut.conj_apply, map_mul, map_mul, hx, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem topChi_finite_order_and_trivial : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1), ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧ ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 := by
  intro F E K _ _ _ _ _ _ _ n Q σ U t Θ d hd N hdN hΘ
  letI : IsOneApply (topU U t Θ d →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (topU U t Θ d →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  constructor
  · intro h
    choose m hm0 hm using h
    refine ⟨∏ P : Q, m P, Finset.prod_pos fun P _ => hm0 P, fun x => ?_⟩
    unfold topChi
    rw [MonoidHom.inv_apply, inv_pow, prod_apply, ← Finset.prod_pow, Finset.prod_eq_one, inv_one]
    intro P _
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ P)
    rw [hc, pow_mul, MonoidHom.comp_apply, ← map_pow, MonoidHom.comp_apply]
    have e : locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) (((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x) ^ m P = 1 :=
      hm P _
    rw [e, map_one, one_pow]
  · intro x hx
    unfold topChi
    rw [MonoidHom.inv_apply, prod_apply, Finset.prod_eq_one, inv_one]
    intro P _
    have e : ((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ (fun x => rhoT_mem x.2 P) x = 1 :=
      Subtype.ext (rhoT_eq_one P.1 t x.1 (hx P))
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_one, map_one]

end GlobalTheory.Mem.Col2.TopCh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterAtQFiniteOrderAndTrivialStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacterAtQ_finite_order_and_trivial : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1), ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧ ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 := by
  exact @GlobalTheory.Mem.Col2.TopCh.topChi_finite_order_and_trivial
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTwistLevelContainsPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTwistLevelContainsPrincipalCongruence
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

open GlobalTheory.TopStep
open GlobalTheory.Mem.Col2.PtExist (mat)

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_dep_eq_exp (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : ∃ N : ℕ, dep P c = WithZero.exp (-(N : ℤ)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, dep P c = WithZero.exp m := ⟨_, (WithZero.exp_log (dep_ne_zero c)).symm⟩
  have h1 : m ≤ 0 := by
    have := dep_le_one (P := P) c
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  refine ⟨(-m).toNat, ?_⟩
  rw [hm, Int.toNat_of_nonneg (by omega), neg_neg]

variable [StarRing E]

theorem sm_of_lqPrinc {P : HeightOneSpectrum (𝓞 E)} {N c : ℕ} (hd : dep P c = WithZero.exp (-(N : ℤ))) {g : Sp E n ≃ₗ[E] Sp E n}
    (h : lqPrinc P N g) : Sm Valued.v (dep P c) (ratM P g - 1) := by
  intro i j
  have e : (ratM P g - 1) i j = algebraMap E (P.adicCompletion E) ((LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) - 1) i j) := by
    have e1 : mat g i j = LinearMap.toMatrix' (g : Sp E n →ₗ[E] Sp E n) i j := by
      rw [LinearMap.toMatrix'_apply]
      rfl
    simp only [Matrix.sub_apply, map_sub, ratM, Matrix.map_apply, e1, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, valued_algebraMap, hd]
  exact h i j

end Loc

end GlobalTheory.Mem.Col2.TopCh

namespace GlobalTheory.Mem.Col2.TC

theorem levQ_top_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  intro B X I a
  choose N hN using fun P : I.Q a => exists_dep_eq_exp P.1 (topDep B.R (I.cst a).M + 1)
  refine ⟨N, fun P => (hN P).le, fun P g hg => ?_⟩
  have hk : g ∈ GlobalTheory.TopStep.prinCong (B.R.N B.R.m) P.1 (topDep B.R (I.cst a).M + 1) := mem_prinCong_of_sm g (sm_of_lqPrinc (hN P) hg)
  have e : (I.Tp a).levQ B.R.m = levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) := topLev_levQ_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  rw [e]
  exact ⟨prinCong_le_levCong _ _ _ hk, levCong_lam_prinCong _ _ _ hk⟩

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTwistLevelContainsPrincipalCongruenceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_twist_level_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι), ∃ N : I.Q a → ℕ, (∀ P : I.Q a, P.1.valuation B.host.E (((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)) ≤ WithZero.exp (-(N P : ℤ))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) → ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1 := by
  exact @GlobalTheory.Mem.Col2.TC.levQ_top_princ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeVISupIndep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.MtIndep

section rep
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isoRep_trans {W₁ W₂ W₃ : Type} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    [AddCommGroup W₃] [Module ℂ W₃] {S₁ : Submodule ℂ (GAf L n → W₁)} {S₂ : Submodule ℂ (GAf L n → W₂)}
    {S₃ : Submodule ℂ (GAf L n → W₃)} (h₁ : NG.IsoRep S₁ S₂) (h₂ : NG.IsoRep S₂ S₃) : NG.IsoRep S₁ S₃ := by
  obtain ⟨T, hT⟩ := h₁
  obtain ⟨U, hU⟩ := h₂
  exact ⟨T.trans U, fun h f f' e => hU h (T f) (T f') (hT h f f' e)⟩

theorem isoRep_symm {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ (GQ L n) W} {S₁ : Submodule ℂ (GAf L n → W)} {S₂ : Submodule ℂ (GAf L n → W')}
    (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) : NG.IsoRep S₂ S₁ := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun h g g' e => ?_⟩
  have hm : NG.rt L n h ((T.symm g : S₁) : GAf L n → W) ∈ S₁ := hs.stable h _ (T.symm g).2
  have key := hT h (T.symm g) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply] at key
  have hg : T ⟨_, hm⟩ = g' := Subtype.ext (key.trans e.symm)
  rw [← hg, LinearEquiv.symm_apply_apply]

theorem isoTyp_eq {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W}
    {S₁ S₂ : Submodule ℂ (GAf L n → W)} (hs : NG.IsSubrep ρ S₁) (h : NG.IsoRep S₁ S₂) :
    NG.isoTyp ρ S₁ = NG.isoTyp ρ S₂ := by
  unfold NG.isoTyp
  congr 1
  ext S'
  simp only [Set.mem_setOf_eq]
  exact and_congr_right fun _ => ⟨fun h' => isoRep_trans (isoRep_symm hs h) h', fun h' => isoRep_trans h h'⟩

end rep

section loc
variable {D : D7}

def BCd (X : LocNd (lay0 D)) (Y : LocAut X) (Pa : List (Part Y.naut.CG)) (loc : ∀ w, Y.naut.LP w)
    (sat : PlE D.host → Multiset ℂ) (inf : (D.host.E →+* ℂ) → Multiset ℂ) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ Y.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, Y.naut.CG a), p.d)).Nodup ∧
  rankIso X.nd Y.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc X.nd Y.naut Pa w = loc w) ∧
  (∀ w, ¬ IsSplitPl D.host w → Y.naut.unr (isoLoc X.nd Y.naut Pa w) ∧
    Y.naut.frobEig (isoLoc X.nd Y.naut Pa w) = ubc D.R.nV (sat w)) ∧
  ∀ τ, isoInf X.nd Y.naut Pa τ = inf τ

def Good (X : LocNd (lay0 D)) (Y : LocAut X) (σ' : D.ntypes.Par) (c : Y.naut.CG 1) (j : ℕ) (u : D.nbc.AU j) : Prop :=
  ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = D.ntypes.locPar σ' w) ∧
    BCd X Y (twistIso X.nd Y.naut (Sig ++ [⟨1, c, D.R.t⟩]) Y.naut.etaTinv) (fun w => D.nbc.locAU j u w)
      (D.nbc.satAU j u) (D.nbc.infW j (D.nbc.wtAU j u))

end loc

end GlobalTheory.HeightCounting.MtIndep

namespace GlobalTheory.HeightCounting.MtIndep

section loc2
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {X : LocNd (lay0 D)}
  {iq : ∀ i : X.nd.Loc, FractionRing (X.nd.O i) →+* Qbar (X.nd.l i)} {Y : LocAut X} {Cb : LocBC Y}

end loc2

end GlobalTheory.HeightCounting.MtIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ClsBij

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem ratAd_mem_ratPts (hc : CMData F E) (γ : UF E n) :
    ratAd F γ ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨ufGL E n γ, ?_, rfl⟩
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ

theorem exists_ratAd_eq (hc : CMData F E) {g : GL (Fin n) (AfE F E)}
    (hg : g ∈ ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ γ : UF E n, ratAd F γ = g := by
  obtain ⟨r, hr, rfl⟩ := hg
  refine ⟨ratEquiv hc n ⟨r, hr⟩, ?_⟩
  show Formalism.UG.bc _ (ufGL E n _) = _
  rw [GlobalTheory.Mem.Col2.RatMove.ufGL_eq hc, MulEquiv.symm_apply_apply]

end SlopeTestRemainingChoices

theorem classes_bijective : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (C : Type) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (s : C → DecoF E n ST SG Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' : GL (Fin n) (AfE F E)) (y : C → UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)), U ≤ UAd hc n → k' ∈ UAd hc n → (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → (∀ g ∈ UAd hc n, ∃ x ∈ U, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * k') p) → (∀ c, IsPtOf hc ((y c).1 * k') (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → Function.Bijective (fun c => (Quotient.mk'' (y c) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) (U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q C Λ Θ s U k' y hU hk' hlev hdense hpt hinj hsurj
  constructor
  · intro c c' hcc
    obtain ⟨γ, hγ, u, hu, he⟩ := (@DoubleCoset.eq _ _ _ _ (y c) (y c')).1 hcc
    have he' : (y c').1 = γ.1 * (y c).1 * u.1 := by rw [he]; rfl
    obtain ⟨δ, hδ⟩ := exists_ratAd_eq hc (Subgroup.mem_subgroupOf.1 hγ)
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q δ⁻¹ _ _ (hpt c')
    have e1 : ratAd F δ⁻¹ * ((y c').1 * k') = (y c).1 * u.1 * k' := by
      rw [he', ← hδ, ← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e1] at h1
    obtain ⟨h, θ, hhθ⟩ := (hlev (y c).1 u.1 (s c) _ (hpt c) h1).1 (Subgroup.mem_subgroupOf.1 hu)
    refine hinj c c' δ h θ ?_
    have e2 : ((δ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) =
        ((δ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) := by
      simp
    rw [e2, mul_smul, hhθ, smul_smul]
    have e3 : ((δ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) * ((δ⁻¹, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) = 1 := by
      simp
    rw [e3, one_smul]
  · intro q
    induction q using Quotient.inductionOn' with
    | h z =>
    obtain ⟨x, hx, p, hp⟩ := hdense z.1 z.2
    obtain ⟨c, γ, h, θ, hcp⟩ := hsurj p
    refine ⟨c, ?_⟩
    have h1 := GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd F E hc n ST SG Q γ⁻¹ _ _ hp
    have e1 : ((γ⁻¹, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p =
        ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c := by
      rw [← hcp, smul_smul]
      congr 1
      simp
    rw [e1] at h1
    have e2 : ratAd F γ⁻¹ * (z.1 * x * k') = (y c).1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x) * k' := by
      group
    rw [e2] at h1
    have hx' : (y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x ∈ U := (hlev (y c).1 _ (s c) _ (hpt c) h1).2 ⟨h, θ, rfl⟩
    let kk : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
      ⟨(y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹, hU (mul_mem hx' (inv_mem hx))⟩
    show DoubleCoset.mk _ _ (y c) = DoubleCoset.mk _ _ z
    refine (@DoubleCoset.eq _ _ _ _ (y c) z).2 ⟨z * kk⁻¹ * (y c)⁻¹, ?_, kk, Subgroup.mem_subgroupOf.2 (mul_mem hx' (inv_mem hx)), by group⟩
    rw [Subgroup.mem_subgroupOf]
    have e4 : ((z * kk⁻¹ * (y c)⁻¹ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (AfE F E))
        = ratAd F γ := by
      show z.1 * ((y c).1⁻¹ * ratAd F γ⁻¹ * z.1 * x * x⁻¹)⁻¹ * (y c).1⁻¹ = _
      rw [← GlobalTheory.Mem.Col2.TilX.ratAd_inv]
      group
    rw [e4]
    exact ratAd_mem_ratPts hc γ

end GlobalTheory.Mem.Col2.ClsBij
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosetsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedPointClasses_bijective_doubleCosets : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (C : Type) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (s : C → DecoF E n ST SG Q) (U : Subgroup (GL (Fin n) (AfE F E))) (k' : GL (Fin n) (AfE F E)) (y : C → UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)), U ≤ UAd hc n → k' ∈ UAd hc n → (∀ (g x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), IsPtOf hc (g * k') p → IsPtOf hc (g * x * k') p' → (x ∈ U ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p')) → (∀ g ∈ UAd hc n, ∃ x ∈ U, ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * x * k') p) → (∀ c, IsPtOf hc ((y c).1 * k') (s c)) → (∀ c c' (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = s c' → c = c') → (∀ p, ∃ c, ∃ (γ : UF E n) (h : Λ.grp) (θ : Θ.grp), ((γ, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • s c = p) → Function.Bijective (fun c => (Quotient.mk'' (y c) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) (U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))))) := by
  first | exact @GlobalTheory.Mem.Col2.ClsBij.classes_bijective | exact GlobalTheory.Mem.Col2.ClsBij.classes_bijective | (intros; apply GlobalTheory.Mem.Col2.ClsBij.classes_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFact
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationEqOfMemIff
open scoped Pointwise

namespace GlobalTheory.ValuationOfMemIff

theorem le_iff_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (x y : Ω) :
    A.valuation (σ x) ≤ A.valuation (σ y) ↔ A.valuation x ≤ A.valuation y := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hσy : σ y ≠ 0 := by simpa using hy
    have key : ∀ a b : Ω, b ≠ 0 → (A.valuation a ≤ A.valuation b ↔ a / b ∈ A) := by
      intro a b hb
      rw [← A.valuation_le_one_iff, map_div₀,
        div_le_one₀ (by simpa [pos_iff_ne_zero] using hb)]
    rw [key _ _ hσy, key _ _ hy, ← map_div₀, h]

theorem not_injective_pow {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (t : Ω) (ht : IsIntegral E t) :
    ¬ Function.Injective (fun k : ℕ => (σ ^ k) t) := by
  intro hinj

  have hsub : Set.range (fun k : ℕ => (σ ^ k) t) ⊆ (minpoly E t).rootSet Ω := by
    rintro _ ⟨k, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero ht, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    simpa [minpoly.aeval] using this
  exact Set.infinite_range_of_injective hinj (((minpoly E t).rootSet_finite Ω).subset hsub)

theorem valuation_eq_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (t : Ω)
    (ht : IsIntegral E t) : A.valuation (σ t) = A.valuation t := by
  have hsucc : ∀ k : ℕ, (σ ^ (k + 1)) t = σ ((σ ^ k) t) := fun k => by
    rw [pow_succ', AlgEquiv.mul_apply]

  have hlt : ∀ x y : Ω, A.valuation (σ x) < A.valuation (σ y) ↔ A.valuation x < A.valuation y := by
    intro x y
    rw [lt_iff_not_ge, lt_iff_not_ge, le_iff_of_mem_iff A σ h]
  have hinj : ∀ w : ℕ → _, (StrictMono w ∨ StrictAnti w) →
      (∀ k, w k = A.valuation ((σ ^ k) t)) → False := by
    intro w hw hwk
    apply not_injective_pow σ t ht
    intro a b hab
    have : w a = w b := by rw [hwk, hwk]; exact congrArg A.valuation hab
    rcases hw with hw | hw
    · exact hw.injective this
    · exact hw.injective this
  rcases lt_trichotomy (A.valuation (σ t)) (A.valuation t) with hc | hc | hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inr (strictAnti_nat_of_succ_lt ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih
  · exact hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inl (strictMono_nat_of_lt_succ ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih

theorem valuation_apply_eq : ∀ (E Ω : Type) [inst : Field E] [NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : Formalism.ConjugateSelfDual.G E Ω), Membership.mem (ReciprocityTheory.Gal.Dec A) σ → ∀ (t : Ω), Eq ((ValuationSubring.valuation A) (σ t)) ((ValuationSubring.valuation A) t) := by
  intro E Ω _ _ _ _ _ A σ hσ t
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact valuation_eq_of_mem_iff A σ (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hσ) t
    (Algebra.IsIntegral.isIntegral t)

end GlobalTheory.ValuationOfMemIff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem Dec_valuation_apply_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first
  | exact @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq
  | (apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationOfMemIff.valuation_apply_eq ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFactStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaDecomposition_fact : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first | exact @GlobalTheory.Dec_valuation_apply_eq | exact GlobalTheory.Dec_valuation_apply_eq | (intros; apply GlobalTheory.Dec_valuation_apply_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfTypeSpaceNeBotOfIsotypicPart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfTypeSpaceNeBotOfIsotypicPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MoveTyped

open Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem isSubrep_bot (ρ : Representation ℂ (GQ L n) W) :
    IsSubrep ρ (⊥ : Submodule ℂ (GAf L n → W)) :=
  ⟨bot_le, fun h f hf => by
    rw [Submodule.mem_bot] at hf ⊢
    subst hf
    exact map_zero _⟩

theorem isSubrep_sup {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊔ Y) :=
  ⟨sup_le hX.le hY.le, fun h f hf => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hX.stable h a ha) (hY.stable h b hb)⟩

theorem isSubrep_inf {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊓ Y) :=
  ⟨inf_le_right.trans hY.le, fun h f hf => ⟨hX.stable h f hf.1, hY.stable h f hf.2⟩⟩

theorem sup_typed_eq_bot {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {X Y : Submodule ℂ (GAf L n → W)} (hX : IsSubrep ρ X) (hXT : X ⊓ TypeSp ρ J χ = ⊥)
    (hY : IsIrrRep ρ Y) (hYT : Y ⊓ TypeSp ρ J χ = ⊥) : (X ⊔ Y) ⊓ TypeSp ρ J χ = ⊥ := by
  by_cases hXY : X ⊓ Y = ⊥
  · rw [eq_bot_iff]
    rintro v ⟨hv, hvT⟩
    have hvT' : v ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) v = ((χ κ : ℂˣ) : ℂ) • v := hvT
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have key : ∀ κ : J, rt L n (κ : GAf L n) a = ((χ κ : ℂˣ) : ℂ) • a ∧
        rt L n (κ : GAf L n) b = ((χ κ : ℂˣ) : ℂ) • b := by
      intro κ
      have e := hvT'.2 κ
      rw [map_add (f := _), smul_add] at e
      have hmem : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a ∈ X ⊓ Y := by
        refine ⟨Submodule.sub_mem _ (hX.stable _ a ha) (Submodule.smul_mem _ _ ha), ?_⟩
        have hab : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a =
            ((χ κ : ℂˣ) : ℂ) • b - rt L n (κ : GAf L n) b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        rw [hab]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) (hY.1.stable _ b hb)
      rw [hXY, Submodule.mem_bot, sub_eq_zero] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at e
      exact add_left_cancel e
    have ha0 : a ∈ X ⊓ TypeSp ρ J χ := ⟨ha, hX.le ha, fun κ => (key κ).1⟩
    have hb0 : b ∈ Y ⊓ TypeSp ρ J χ := ⟨hb, hY.1.le hb, fun κ => (key κ).2⟩
    rw [hXT, Submodule.mem_bot] at ha0
    rw [hYT, Submodule.mem_bot] at hb0
    simp [ha0, hb0]
  · have hle : X ⊓ Y = Y := (hY.2.2 _ (isSubrep_inf hX hY.1) inf_le_right).resolve_left hXY
    have hYX : Y ≤ X := hle ▸ inf_le_left
    rw [sup_eq_left.2 hYX, hXT]

theorem typed_eq_bot_of_iso {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {S S' : Submodule ℂ (GAf L n → W)} (hS : IsSubrep ρ S) (hiso : IsoRep S S')
    (h : S ⊓ TypeSp ρ J χ = ⊥) : S' ⊓ TypeSp ρ J χ = ⊥ := by
  obtain ⟨T, hT⟩ := hiso
  rw [eq_bot_iff]
  rintro u ⟨hu, huT⟩
  have huT' : u ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) u = ((χ κ : ℂˣ) : ℂ) • u := huT
  obtain ⟨f, hfu⟩ : ∃ f : S, T f = ⟨u, hu⟩ := ⟨T.symm _, T.apply_symm_apply _⟩
  have hf : ∀ κ : J, rt L n (κ : GAf L n) (f : GAf L n → W) = ((χ κ : ℂˣ) : ℂ) • (f : GAf L n → W) := by
    intro κ
    let f' : S := ⟨rt L n (κ : GAf L n) f, hS.stable _ _ f.2⟩
    have e := hT κ f f' rfl
    have hTT : T f' = T (((χ κ : ℂˣ) : ℂ) • f) := by
      apply Subtype.ext
      rw [e, map_smul, Submodule.coe_smul, hfu]
      exact huT'.2 κ
    have := congrArg Subtype.val (T.injective hTT)
    simpa [f'] using this
  have hfm : (f : GAf L n → W) ∈ S ⊓ TypeSp ρ J χ := ⟨f.2, hS.le f.2, hf⟩
  rw [h, Submodule.mem_bot] at hfm
  have hf0 : f = 0 := Subtype.ext hfm
  rw [hf0, map_zero] at hfu
  have := congrArg Subtype.val hfu
  simpa using this.symm

theorem typed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S →
    Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  intro L _ _ _ n W _ _ ρ J χ S hS hne h0
  apply hne
  have hfam : ∀ S' ∈ {S' | IsIrrRep ρ S' ∧ IsoRep S S'}, S' ⊓ TypeSp ρ J χ = ⊥ :=
    fun S' hS' => typed_eq_bot_of_iso hS hS'.2 h0
  have fin : ∀ s : Finset (Submodule ℂ (GAf L n → W)), (↑s : Set _) ⊆ {S' | IsIrrRep ρ S' ∧ IsoRep S S'} →
      IsSubrep ρ (⨆ i ∈ s, i) ∧ (⨆ i ∈ s, i) ⊓ TypeSp ρ J χ = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [isSubrep_bot]
    | insert a s ha ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨h1, h2⟩ := ih hs.2
      rw [Finset.iSup_insert, sup_comm]
      exact ⟨isSubrep_sup h1 hs.1.1.1, sup_typed_eq_bot h1 h2 hs.1.1 (hfam a hs.1)⟩
  rw [eq_bot_iff]
  rintro v ⟨hv, hvT⟩
  unfold isoTyp at hv
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hv
  have hb := (fin s hs).2
  rw [eq_bot_iff] at hb
  exact hb ⟨hvs, hvT⟩

end GlobalTheory.MoveTyped
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfTypeSpaceNeBotOfIsotypicPartStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_typeSpace_ne_bot_of_isotypicPart : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S → Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  first | exact @GlobalTheory.MoveTyped.typed_of_isoTyp | exact GlobalTheory.MoveTyped.typed_of_isoTyp | (intros; apply GlobalTheory.MoveTyped.typed_of_isoTyp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

namespace GlobalTheory.Mem.ColTie

theorem ipK_eq_card_mul_ipLev {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P) :
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  have h0 : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 := levelSumX W Ch sel mu P (mtildeOk W Ch sel mu hX P) (mtildeKOk W Ch sel mu hX) z.1 z'.1 z.2 z'.2
  unfold ipLev ipK
  rw [h1, mul_inv_cancel_left₀ h0]

end GlobalTheory.Mem.ColTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormClassSumPrincipalEqCardMulLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormClassSum_principal_eq_card_mul_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (z z' : MtildeV W Ch sel mu P),
    ipK W Ch sel mu P hX z z' = (Nat.card P.grp : X.K) * ipLev W Ch sel mu P hX z z' := by
  first | exact @GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | exact GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev | (intros; apply GlobalTheory.Mem.ColTie.ipK_eq_card_mul_ipLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEquivariantRealPlace
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.ConjEquivRealSee


set_option maxHeartbeats 1000000 in
theorem conjMap_update_real_see : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau R.θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  intro _ _ _ _ D G _ _ Pl0 T A Ks _ _ _ R F X h t hιE _ _ hinf _ hsee c hc Φ hΦ hrep τ g hg v w hw
  classical
  obtain ⟨hfin, -, hreal, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h R.θ hinf hιE
  have ht : t ∈ GfC (Yc D 0) := hsee.fin
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  obtain ⟨-, Rm, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  have hint : ∀ (x : X.B.I.Ginf) (z : X.B.Hs), Φ (X.B.σs x z) = X.B.R (x, 1) (Φ z) := by
    obtain ⟨B, hB, rfl⟩ := hΦ
    intro x z
    have hb : B (X.B.σs x z) = X.B.R (x, 1) (B z) := DFunLike.congr_fun (hB x) z
    show X.B.Re (B (X.B.σs x z)) = X.B.R (x, 1) (X.B.Re (B z))
    rw [hb]
    obtain ⟨-, hT⟩ := X.B.Re_spec
    apply ext_inner_left ℂ
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_left (X.B.R (x, 1)), hT, hT]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← Rm, ← ContinuousLinearMap.comp_apply (X.B.R (x, 1)), ← Rm]
    simp
  have hσ1 : ∀ v', X.B.σ v' 1 = 1 := fun v' => (X.ds v').2.2.1.1.1
  have hvec : GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w) = fun v' =>
      X.B.σ v' (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v')) (GlobalTheory.ConjRowMult.vecC X (MP R) c v v') := by
    rw [GlobalTheory.ConjRowMult.vecC_update]
    funext v'
    by_cases hv : v' = X.pl.symm τ
    · subst hv
      rw [Function.update_self, hw, hc τ g hg]
      unfold GlobalTheory.ConjRowMult.vecC
      rw [Equiv.piCongrLeft_apply_apply]
    · rw [Function.update_of_ne hv, ha1 v' hv,
        show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v')) = 1 from rfl, hσ1]
      rfl
  have hsig : X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w)) =
      X.B.σs ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1) (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have ea : iotaX X h (atTau R.θ (D.sp.Y 0) τ g) = ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1, 1) :=
    Prod.ext rfl ha2
  have hcomm : iotaX X h t⁻¹ * iotaX X h (atTau R.θ (D.sp.Y 0) τ g) =
      iotaX X h (atTau R.θ (D.sp.Y 0) τ g) * iotaX X h t⁻¹ := by
    have h1 : (iotaX X h t).1 = 1 := (hfin t).1 ht
    erw [map_inv]
    refine Prod.ext ?_ ?_
    · simp [h1]
    · simp [ha2]
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (iotaX X h (atTau R.θ (D.sp.Y 0) τ g))
  funext y
  show _ = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v (y * atTau R.θ (D.sp.Y 0) τ g)
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [hsig, hint, ← ea,
    GlobalTheory.ConjRowMult.contRepL_spec X hψ', GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  simp only [map_mul]
  rw [mul_assoc, hcomm, mul_assoc]

end GlobalTheory.ConjEquivRealSee

end
end
