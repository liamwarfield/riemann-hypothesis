module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective

@[expose] public section

section -- merged from Formalism.LocalToGlobal.NormalizedHeckeFactors.NormalizedHeckeData
noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2

structure NormalizedHeckeDataPlaceholder (D : D7) : Type

end Formalism.L2
end
end

section -- merged from Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions
open scoped NNReal

namespace Formalism.L2.TwC

section rings

variable (l : ℕ) [Fact l.Prime]

def intOf (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring (PadicAlgCl l) :=
  K.toSubalgebra.toSubring ⊓ (PadicAlgCl.valued l).v.integer

def clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring ℂ_[l] :=
  (F.toSubalgebra.toSubring.map (algebraMap (PadicAlgCl l) ℂ_[l])).topologicalClosure ⊓
    (PadicComplexInt l).toSubring

def Kt (K₀ L : Loc.FinExt l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  K₀.1 ⊔ L.1 ⊔ Loc.MaximalUnramifiedExtension l

def muK (k : ℕ) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] {x | x ^ (l ^ k) = 1}

end rings

section places

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hp' : ((p : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hp'
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 E)}
  rw [Ideal.dvd_span_singleton]
  exact hv

def pDC {R : Ranks} (H : Host R) (l : ℕ) : Finset (HeightOneSpectrum (𝓞 H.E)) :=
  (placesOver_finite' H.E (if l = H.pde then H.pde' else H.pde)
    (by split_ifs <;> first | exact H.pde'_prime.ne_zero | exact H.pde_prime.ne_zero)).toFinset

theorem coe_pDC {R : Ranks} (H : Host R) (l : ℕ) :
    (pDC H l : Set (HeightOneSpectrum (𝓞 H.E))) = placesOver H.E (if l = H.pde then H.pde' else H.pde) := by
  first
    | exact Set.Finite.coe_toFinset _
    | (simp [pDC]; done)

end places

end Formalism.L2.TwC
end
end

section -- merged from Formalism.LocalToGlobal.NormalizedHeckeFactors.RingSpecSidedEmbeddingFixedField
section -- merged from Formalism.LocalToGlobal.NormalizedHeckeFactors.ChiDefs
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

section hecke

variable {E : Type} [Field E] [NumberField E]

@[ext]
structure HC (E : Type) [Field E] [NumberField E] where
  χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ
  cont : Continuous χ
  triv : ∀ a : Eˣ, χ (Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom a) = 1

instance : Mul (HC E) where
  mul χ ψ := ⟨χ.χ * ψ.χ, χ.cont.mul ψ.cont, fun a => by rw [MonoidHom.mul_apply, χ.triv a, ψ.triv a, one_mul]⟩

instance : Inv (HC E) where
  inv χ := ⟨χ.χ⁻¹, χ.cont.inv, fun a => by rw [MonoidHom.inv_apply, χ.triv a, inv_one]⟩

instance : One (HC E) where
  one := ⟨1, continuous_const, fun _ => rfl⟩


open scoped Classical in
def locM (P : HeightOneSpectrum (𝓞 E)) : P.adicCompletion E →* AdeleRing (𝓞 E) E where
  toFun x := ((1 : InfiniteAdeleRing E),
    (RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletionIntegers E) P x :
      FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [RestrictedProduct.mulSingle_one]
    rfl
  map_mul' x y := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E) * 1, _ * _)
    rw [RestrictedProduct.mulSingle_mul, mul_one]
    rfl

def HC.At (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) (α : ℂ) : Prop :=
  (∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1) ∧
    ∀ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) →
      ((χ.χ (Units.map (locM P) ϖ) : ℂˣ) : ℂ) = α

theorem HC.At.mul {χ ψ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (h : χ.At P a) (h' : ψ.At P b) :
    (χ * ψ).At P (a * b) := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · change (χ.χ * ψ.χ) (Units.map (locM P) u) = 1
    rw [MonoidHom.mul_apply, h.1 u hu, h'.1 u hu, one_mul]
  · change (↑((χ.χ * ψ.χ) (Units.map (locM P) ϖ)) : ℂ) = a * b
    rw [MonoidHom.mul_apply, Units.val_mul, h.2 ϖ hϖ, h'.2 ϖ hϖ]

theorem HC.At.inv {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a : ℂ} (h : χ.At P a) : (χ⁻¹).At P a⁻¹ := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · change χ.χ⁻¹ (Units.map (locM P) u) = 1
    rw [MonoidHom.inv_apply, h.1 u hu, inv_one]
  · change (↑(χ.χ⁻¹ (Units.map (locM P) ϖ)) : ℂ) = a⁻¹
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h.2 ϖ hϖ]

theorem exists_unif (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hv : Valued.v (π : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [P.valuedAdicCompletion_eq_valuation' π, hπ]
  have h0 : (π : P.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ h0, hv⟩

theorem HC.At.unique {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (ha : χ.At P a) (hb : χ.At P b) : a = b := by
  obtain ⟨ϖ, hϖ⟩ := exists_unif P
  rw [← ha.2 ϖ hϖ, ← hb.2 ϖ hϖ]


open scoped Classical in
def locInf (v : InfinitePlace E) : v.Completion →* AdeleRing (𝓞 E) E where
  toFun x := ((Pi.mulSingle v x : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((Pi.mulSingle v (1 : v.Completion) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [Pi.mulSingle_one]
  map_mul' x y := by
    show ((Pi.mulSingle v (x * y) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((Pi.mulSingle v x : InfiniteAdeleRing E) * Pi.mulSingle v y, (1 : FiniteAdeleRing (𝓞 E) E) * 1)
    rw [Pi.mulSingle_mul, mul_one]

def HC.Unr (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1

def HC.IsUnitArg (χ : HC E) (τ : E →+* ℂ) : Prop :=
  ∀ f : (InfinitePlace.mk τ).Completion →+* ℂ, Continuous f → (∀ x : E, f (x : (InfinitePlace.mk τ).Completion) = τ x) →
    ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
      ((χ.χ (Units.map (locInf (InfinitePlace.mk τ)) z) : ℂˣ) : ℂ) = f z / (‖f z‖ : ℂ)

end hecke

section read

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def Read {A K L : Type} [CommRing A] [CommRing K] [CommRing L] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω)
    (φ : G E Ω →* Aˣ) (rd : A →+* K) (eL : L →+* K) (embC : L →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  ∃ B : Finset (HeightOneSpectrum (𝓞 E)), ∀ P ∉ B, ∃ α : ℂ, χ.At P α ∧ ∃ x : L,
    embC x = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ w ∧
    ∀ σ : G E Ω, IsFrob (F := E) (pl P) (normV P) σ → rd (φ σ : A) = eL x

abbrev ReadC {A : Type} [CommRing A] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (φ : G E Ω →* Aˣ)
    (rd : A →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  Read pl φ rd (RingHom.id ℂ) (RingHom.id ℂ) χ w


theorem normV_ne_zero (P : HeightOneSpectrum (𝓞 E)) : normV P ≠ 0 := by
  have h : normV P = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [h]
  exact fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem finite_placesOver (l : ℕ) [Fact l.Prime] :
    {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

end read

section rcg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

end rcg

end Formalism.L2.NC
end
end

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

def iotaC (D : D7) (i : D.nd.Loc) : D.nd.O i →+* ℂ :=
  ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

def complexEmbeddingRestrictedToSubfield (D : D7) : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom

structure NChiData (D : D7) where

  mu0 : ℕ → HC D.host.E

  etaT : HC D.host.E

  del : D.ntw.Tw → HC D.host.E

  psi : D.nd.Loc → HC D.host.E

  chiI : ∀ s, D.ntw.abelian₂ s → HC D.host.E

  embO : ∀ s, Bool → ↥D.LL0 →+* FractionRing (D.ntw.O s)

def NChiData.firstHeckeCharacter {D : D7} (K : NChiData D) (s : D.ntw.Tw) (j : ℕ) : HC D.host.E :=
  K.mu0 j * K.del s * (K.etaT)⁻¹

def NChiData.lamH {D : D7} (K : NChiData D) (s : D.ntw.Tw) (lam : D.ntw.abelian₂ s) : HC D.host.E :=
  K.mu0 (D.ntw.jL s lam) * K.del s * (K.chiI s lam)⁻¹

structure NormalizedCharacterCompatibility (D : D7) (K : NChiData D) : Prop where

  psi : ∀ a, ReadC D.nd.plOm.1 (D.ntw.psiL a) (iotaC D a) (K.psi a) 0

  del_fix : ∀ s s', D.ntw.pD s = D.ntw.pD s' → K.del s = K.del s'

  delta : ∀ s, Read D.nd.plOm.1 (D.ntw.delta s) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (D.ntw.emb0 s)
    (complexEmbeddingRestrictedToSubfield D) (K.del s) 0

  chi1 : ∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → Read D.nd.plOm.1 (D.ntw.chi1 s j b) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)))
    (if b then D.ntw.emb0 s else D.ntw.emb0b s) (complexEmbeddingRestrictedToSubfield D) (K.firstHeckeCharacter s j) (-(D.R.r : ℤ))

  ringSpec_sidedEmbedding_fixedField : ∀ s (b : Bool) (x : ↥D.LL0) (y : D.ntw.O0 s),
    algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) y = (if b then D.ntw.emb0 s else D.ntw.emb0b s) x →
    K.embO s b x = algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)) (algebraMap (D.ntw.O0 s) (D.ntw.O s) y)

  etaT_unr : ∀ P, K.etaT.Unr P

  etaT_inf : ∀ g : D.R.Psi, K.etaT.IsUnitArg (D.host.emb (g : D.R.GG))

  lamG : ∀ s lam, Read D.nd.plOm.1 (D.ntw.lamG s lam) (algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)))
    (K.embO s (D.ntw.sideL s lam)) (complexEmbeddingRestrictedToSubfield D) (K.lamH s lam) 0

section rcg

variable (D : D7)

end rcg

theorem frob_exists (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ σ : G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ :=
  exists_isFrob (D.nd.plOm.2 P)

end Formalism.L2.NC
end
end
