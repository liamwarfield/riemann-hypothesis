module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def IsEffectiveVertical (P : Ideal (MRing ι O)) (ϖ : O) (b : K → ℤ) (f g : MRing ι O) : Prop :=
  IsVerticalDivisor P ϖ b f g ∧ ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
    ∃ u v : MRing ι O, u ∉ W ∧ u * f - v * g ∈ P


open Classical in
def cutIdentity (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (c : K → ℕ)
    (s : MRing ι O) {d : ℕ} (L : Fin d → K → ℤ) : Prop :=
  by
    classical
    exact cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)

end Defs

section Lemmas

def DivCycleMul.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (x y : MRing ι R), P.IsPrime → x ∉ P → y ∉ P →
    divCycle P (x * y) = divCycle P x + divCycle P y

def DivCycleFiniteSupport.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (f : MRing ι R),
    (Function.support (divCycle P f)).Finite

def SupSpanMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (I : Ideal (MRing ι R))
    (x : MRing ι R) (e : K → ℕ), IsMultiHomogIdeal I → IsMultiHomog x e →
    IsMultiHomogIdeal (I ⊔ Ideal.span {x})

def MinimalPrimeMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (J W : Ideal (MRing ι R)), IsMultiHomogIdeal J → W ∈ J.minimalPrimes → IsMultiHomogIdeal W

def IntNumAddFirst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (G : Ideal (MRing ι F)), G.IsPrime → IsMultiHomogIdeal G →
    ringKrullDim (MRing ι F ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b₁ b₂ : K → ℤ) (L : Fin n → K → ℤ),
      intNum F G (Matrix.vecCons (b₁ + b₂) L) =
        intNum F G (Matrix.vecCons b₁ L) + intNum F G (Matrix.vecCons b₂ L)

def SpecialQuotDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι O)), (C ϖ : MRing ι O) ∈ W →
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
      ringKrullDim (MRing ι O ⧸ W)

def GenericDimBound.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1 ≤ ringKrullDim (MRing ι O ⧸ P)

def GenericFibProps.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    (genFib P).IsPrime ∧ IsMultiHomogIdeal (genFib P) ∧
    ∀ (s : MRing ι O) (c : K → ℕ), IsMultiHomog s c → s ∉ P →
      IsMultiHomog (MvPolynomial.map (algebraMap O (FractionRing O)) s) c ∧
        MvPolynomial.map (algebraMap O (FractionRing O)) s ∉ genFib P


open Classical in
def GenericCycleCorresp.Statement : Prop :=
  by
  classical
  exact ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (s : MRing ι O), P.IsPrime →
    P.comap (C : O →+* MRing ι O) = ⊥ → s ∉ P →
    ∀ n : Ideal (MRing ι (FractionRing O)) → ℤ,
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W)) (divCycle P s) =
        cycEval n (divCycle (genFib P) (MvPolynomial.map (algebraMap O (FractionRing O)) s))

def ConservationOfNumberLE.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsMultiProjPrime P →
    P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι O ⧸ P) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ a : Fin d → K → ℤ, cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a

def UniformiserCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P 0 (C ϖ) 1 c s L

def ShiftByUniformiser.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ (L : Fin d → K → ℤ) (n : ℕ),
      cutIdentity ϖ P b (C ϖ ^ n * f) g c s L → cutIdentity ϖ P 0 (C ϖ) 1 c s L →
        cutIdentity ϖ P b f g c s L

def EffectiveShift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (e : ℕ), IsModelOver P e →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∃ n : ℕ, IsEffectiveVertical P ϖ b (C ϖ ^ n * f) g

def EffectiveCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def Representative.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O), IsMultiProjPrime P →
    IsVerticalDivisor P ϖ b f g → ∀ T : Finset (Ideal (MRing ι O)),
    (∀ H ∈ T, IsMultiProjPrime H ∧ P ≤ H ∧ (C ϖ : MRing ι O) ∉ H ∧
      ∃ h : MRing ι O, h ∉ P ∧ H ∈ (P ⊔ Ideal.span {h}).minimalPrimes) →
    ∃ f₁ g₁ : MRing ι O, IsVerticalDivisor P ϖ b f₁ g₁ ∧ ratDiv P f₁ g₁ = ratDiv P f g ∧
      ∀ H ∈ T, IsVerticalDivisor H ϖ b f₁ g₁

end Lemmas

section Examples

theorem isMultiHomogIdeal_span_singleton {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*}
    [CommRing R] {x : MRing ι R} {e : K → ℕ} (hx : IsMultiHomog x e) :
    IsMultiHomogIdeal (Ideal.span {x}) := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra R (blockWeight ι)
  have h : (Ideal.span {x}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by
      rintro y rfl
      exact ⟨e, hx⟩)
  intro f hf b
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h hf b

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ker_map_residue_eq_span {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type*} :
    RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MvPolynomial σ O →+* _) =
      Ideal.span {C ϖ} := by
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
    Set.image_singleton]

theorem SpecialIdealCorresp.proof : SpecialIdealCorresp.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W hW hϖW
  obtain ⟨π, hπ⟩ : ∃ π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O),
      π = MvPolynomial.map (IsLocalRing.residue O) := ⟨_, rfl⟩
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => by rw [hπ]; rfl
  have hsurj : Function.Surjective π := hπ ▸ MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := hπ ▸ ker_map_residue_eq_span hϖ
  have hle : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → RingHom.ker π ≤ V := fun h => by
    rw [hker, Ideal.span_le, Set.singleton_subset_iff]; exact h
  have hcm : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → (V.map π).comap π = V := fun h => by
    rw [Ideal.comap_map_of_surjective' π hsurj, sup_eq_left.mpr (hle h)]
  simp only [hsp]
  refine ⟨Ideal.map_isPrime_of_surjective hsurj (hle hϖW), ?_, ?_, ?_⟩
  · have hJ : P ⊔ Ideal.span {C ϖ} = (P.map π).comap π := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker]
    rw [hJ, Ideal.comap_minimalPrimes_eq_of_surjective hsurj]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rwa [Ideal.map_comap_of_surjective π hsurj]
    · intro h
      exact ⟨_, h, hcm hϖW⟩
  · have hX : ∀ v, (X v : MRing ι O) ∈ W ↔ (X v : MRing ι (IsLocalRing.ResidueField O)) ∈ W.map π :=
      fun v => by
        conv_lhs => rw [← hcm hϖW]
        rw [Ideal.mem_comap, hπ, MvPolynomial.map_X]
    simp only [IsRelevant, hX]
  · intro W' _ hϖW' h
    rw [← hcm hϖW', ← hcm hϖW, h]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem DimStrictDrop.proof : DimStrictDrop.Statement.{u} := by
  intro A _ Q Q' _ _ hlt
  let q : PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    ⟨⟨Q, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q' : Set A)) :=
    ⟨⟨⟨Q', inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q : Set A)) := ⟨q⟩
  let f : PrimeSpectrum.zeroLocus (R := A) (Q' : Set A) → PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    fun x => ⟨x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (le_trans (show (Q : Set A) ⊆ Q' from hlt.le) ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩
  have hf : StrictMono f := fun a b h => h
  rw [ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  have hq : q < f l.head := by
    show Q < (l.head.1.asIdeal)
    exact lt_of_lt_of_le hlt ((PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2)
  refine le_trans ?_ (le_iSup _ ((l.map f hf).cons q hq))
  have hlen : ((l.map f hf).cons q hq).length = l.length + 1 := by
    simp [RelSeries.cons_length, LTSeries.map]
  rw [hlen]
  simp

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u

theorem isWeightedHomogeneous_map_of {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (f : R →+* S) (w : σ → M) {p : MvPolynomial σ R} {b : M}
    (hp : IsWeightedHomogeneous w p b) : IsWeightedHomogeneous w (MvPolynomial.map f p) b := by
  intro d hd
  rw [coeff_map] at hd
  apply hp
  intro h0
  exact hd (by rw [h0, map_zero])

theorem span_forms_of_isMultiHomogIdeal {K : Type} [DecidableEq K] {ι : K → Type}
    {R : Type*} [CommRing R] {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) :
    Ideal.span {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b} = P := by
  apply le_antisymm
  · rw [Ideal.span_le]
    exact fun f hf => hf.1
  · intro p hp
    rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) p,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]
    refine Ideal.sum_mem _ fun m _ => Ideal.subset_span ⟨hP p hp m, m, ?_⟩
    exact weightedHomogeneousComponent_isWeightedHomogeneous m p

theorem SpecialIdealMultiHomog.proof : SpecialIdealMultiHomog.Statement := by
  classical
  intro O _ _ _ K _ ι P hP
  have hspan : specialIdeal P = Ideal.span
      (MvPolynomial.map (IsLocalRing.residue O) ''
        {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b}) := by
    rw [specialIdeal, ← Ideal.map_span, span_forms_of_isMultiHomogIdeal hP]
  have hhom : (specialIdeal P).IsHomogeneous
      (weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι)) := by
    rw [hspan]
    apply Ideal.homogeneous_span
    rintro _ ⟨f, ⟨_, b, hb⟩, rfl⟩
    exact ⟨b, (mem_weightedHomogeneousSubmodule _ _ _ _).2
      (isWeightedHomogeneous_map_of _ _ hb)⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem _ _ hhom hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem length_localizedModule_eq_of_surjective {S T : Type*} [CommRing S] [CommRing T]
    (π : S →+* T) (hπ : Function.Surjective π) (Q : Ideal T) [Q.IsPrime] (W : Ideal S) [W.IsPrime]
    (hW : W = Q.comap π) (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
    (e : M ≃+ N) (he : ∀ (s : S) (x : M), e (s • x) = π s • e x) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) =
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) := by
  let φ : Localization.AtPrime W →+* Localization.AtPrime Q := Localization.localRingHom W Q π hW
  have hmem : ∀ s : S, s ∈ W.primeCompl ↔ π s ∈ Q.primeCompl := fun s => by
    subst hW; rfl
  have hφ : ∀ s : S, φ (algebraMap S _ s) = algebraMap T _ (π s) :=
    Localization.localRingHom_to_map W Q π hW
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl b
    obtain ⟨s, rfl⟩ := hπ t
    obtain ⟨v, hv⟩ := hπ u
    refine ⟨IsLocalization.mk' _ s (⟨v, (hmem v).2 (hv ▸ u.2)⟩ : W.primeCompl), ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hv
  let _ : Algebra (Localization.AtPrime W) (Localization.AtPrime Q) := φ.toAlgebra
  let _ : Module (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) := Module.compHom _ φ
  have _ : IsScalarTower (Localization.AtPrime W) (Localization.AtPrime Q)
      (LocalizedModule Q.primeCompl N) :=
    ⟨fun a b n => mul_smul (φ a) b n⟩
  let _ : Module S (LocalizedModule Q.primeCompl N) := Module.compHom _ (φ.comp (algebraMap S _))
  have _ : IsScalarTower S (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) :=
    ⟨fun s a n => by
      show φ (s • a) • n = φ (algebraMap S _ s) • (φ a • n)
      rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsmul : ∀ (s : S) (y : LocalizedModule Q.primeCompl N), s • y = π s • y := fun s y => by
    show φ (algebraMap S _ s) • y = _
    rw [hφ, algebraMap_smul]
  let g : M →ₗ[S] LocalizedModule Q.primeCompl N :=
    { toFun := fun x => LocalizedModule.mkLinearMap Q.primeCompl N (e x)
      map_add' := fun x y => by simp only [map_add (f := _)]
      map_smul' := fun s x => by
        rw [RingHom.id_apply, hsmul, he, LinearMap.map_smul] }
  have hg : IsLocalizedModule W.primeCompl g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · have hu : IsUnit (φ (algebraMap S _ (s : S))) :=
        (IsLocalization.map_units (Localization.AtPrime W) s).map φ
      rw [Module.End.isUnit_iff]
      refine ⟨fun y z h => ?_, fun y => ⟨((hu.unit⁻¹ : (Localization.AtPrime Q)ˣ) :
        Localization.AtPrime Q) • y, ?_⟩⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at h
        exact hu.smul_left_cancel.mp h
      · rw [Module.algebraMap_end_apply]
        show φ (algebraMap S _ (s : S)) • _ = y
        rw [← mul_smul, hu.mul_val_inv, one_smul]
    · induction y using LocalizedModule.induction_on with
      | h n t =>
      obtain ⟨s, hs⟩ := hπ t
      refine ⟨(e.symm n, ⟨s, (hmem s).2 (hs ▸ t.2)⟩), ?_⟩
      show s • LocalizedModule.mk n t = LocalizedModule.mk (e (e.symm n)) 1
      rw [hsmul, hs, AddEquiv.apply_symm_apply, LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel t n
    · have h' : LocalizedModule.mk (e x₁) (1 : Q.primeCompl) = LocalizedModule.mk (e x₂) 1 := h
      obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp h'
      obtain ⟨s, hs⟩ := hπ c
      refine ⟨⟨s, (hmem s).2 (hs ▸ c.2)⟩, e.injective ?_⟩
      show e (s • x₁) = e (s • x₂)
      rw [he, he, hs]
      simpa [Submonoid.smul_def] using hc
  let eA := (IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)
  rw [eA.length_eq]
  exact Module.length_eq_of_surjective hsurj

theorem SpecialMultAt.proof : SpecialMultAt.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W _ hW _
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hspec : ∀ I : Ideal (MRing ι O), specialIdeal I = I.map π := fun _ => rfl
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hcm : ∀ I : Ideal (MRing ι O), (specialIdeal I).comap π = I ⊔ Ideal.span {C ϖ} := by
    intro I
    rw [hspec, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hker]
  have hWc : W = (specialIdeal W).comap π := by
    rw [hcm]
    exact (sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hW))).symm
  let f : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk _).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
  have hkerf : RingHom.ker f = P ⊔ Ideal.span {C ϖ} := by
    rw [← hcm]
    ext x
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  let e := ((Ideal.quotEquivOfEq hkerf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))
  have hemk : ∀ z, e (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have he : ∀ (s : MRing ι O) (x : MRing ι O ⧸ (P ⊔ Ideal.span {C ϖ})),
      e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, hemk]
    simp [f]
    rw [← map_mul]
    rfl
  exact length_localizedModule_eq_of_surjective π hπ (specialIdeal W) W hWc _ _ e.toAddEquiv he

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace GenericDimGe

section Noetherian

variable {R : Type*} [CommRing R]

theorem map_mk_lt {p a b : Ideal R} (ha : p ≤ a) (hab : a < b) :
    a.map (Ideal.Quotient.mk p) < b.map (Ideal.Quotient.mk p) := by
  have key : ∀ c : Ideal R, p ≤ c →
      (c.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = c := by
    intro c hc
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hc
  refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
  rw [← key a ha, ← key b (ha.trans hab.le), h]

theorem one_lt_height_map {p a b : Ideal R} [p.IsPrime] [a.IsPrime] [b.IsPrime] (hpa : p < a)
    (hab : a < b) : 1 < (b.map (Ideal.Quotient.mk p)).height := by
  have hk : ∀ c : Ideal R, p ≤ c → RingHom.ker (Ideal.Quotient.mk p) ≤ c := fun c hc => by
    rw [Ideal.mk_ker]; exact hc
  have := Ideal.map_isPrime_of_surjective (I := p) Ideal.Quotient.mk_surjective (hk p le_rfl)
  have := Ideal.map_isPrime_of_surjective (I := a) Ideal.Quotient.mk_surjective (hk a hpa.le)
  have := Ideal.map_isPrime_of_surjective (I := b) Ideal.Quotient.mk_surjective
    (hk b (hpa.trans hab).le)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (map_mk_lt le_rfl hpa)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (map_mk_lt hpa.le hab)
  have h3 : (1 : ℕ∞) ≤ (a.map (Ideal.Quotient.mk p)).height := le_trans le_add_self h1
  have h4 : (1 : ℕ∞) + 1 ≤ (b.map (Ideal.Quotient.mk p)).height :=
    le_trans (add_le_add h3 le_rfl) h2
  exact lt_of_lt_of_le (by norm_num) h4

theorem exists_isPrime_between_not_mem [IsNoetherianRing R] {p q r : Ideal R} [p.IsPrime]
    [q.IsPrime] [r.IsPrime] (hpq : p < q) (hqr : q < r) {x : R} (hx : x ∉ p) :
    ∃ q' : Ideal R, q'.IsPrime ∧ p < q' ∧ q' < r ∧ x ∉ q' := by
  classical
  by_contra H
  push Not at H
  have hM : (p ⊔ Ideal.span {x}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R _
  let s : Finset (Ideal R) := insert p (hM.toFinset.filter (· < r))
  have hprime : ∀ t ∈ s, t.IsPrime := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · infer_instance
    · exact (hM.mem_toFinset.1 (Finset.mem_filter.1 ht).1).isPrime
  have hlt : ∀ t ∈ s, t < r := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hpq.trans hqr
    · exact (Finset.mem_filter.1 ht).2
  have hnot : ¬ ((r : Set R) ⊆ ⋃ t ∈ (↑s : Set (Ideal R)), ((fun t : Ideal R => t) t : Set R)) := by
    intro h
    obtain ⟨t, ht, hrt⟩ :=
      (Ideal.subset_union_prime (f := fun t : Ideal R => t) p p
        (fun t ht _ _ => hprime t ht)).1 h
    exact (hlt t ht).not_ge hrt
  obtain ⟨y, hyr, hy⟩ := Set.not_subset.1 hnot
  simp only [Set.mem_iUnion, not_exists] at hy
  have hyp : y ∉ p := fun h => hy p (Finset.mem_coe.2 (Finset.mem_insert_self _ _)) h
  have hyt : ∀ t ∈ (p ⊔ Ideal.span {x}).minimalPrimes, t < r → y ∉ t := fun t ht htr h =>
    hy t (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hM.mem_toFinset.2 ht, htr⟩))) h
  have hle : p ⊔ Ideal.span {y} ≤ r :=
    sup_le (hpq.trans hqr).le (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  obtain ⟨t0, ht0, ht0r⟩ := Ideal.exists_minimalPrimes_le hle
  have : t0.IsPrime := ht0.isPrime
  have hKrull := Ideal.map_height_le_one_of_mem_minimalPrimes ht0
  have hyt0 : y ∈ t0 := ht0.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  have hpt0 : p < t0 :=
    lt_of_le_of_ne (le_sup_left.trans ht0.1.2) fun h => hyp (by rw [h]; exact hyt0)
  have ht0r' : t0 < r := by
    refine lt_of_le_of_ne ht0r fun h => ?_
    have h2 := one_lt_height_map hpq hqr
    rw [← h] at h2
    exact absurd hKrull (not_le.2 h2)
  have hxt0 : x ∈ t0 := H t0 inferInstance hpt0 ht0r'
  have hle' : p ⊔ Ideal.span {x} ≤ t0 :=
    sup_le (le_sup_left.trans ht0.1.2) (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  obtain ⟨t', ht', ht't0⟩ := Ideal.exists_minimalPrimes_le hle'
  have : t'.IsPrime := ht'.isPrime
  have hxt' : x ∈ t' := ht'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  have hpt' : p < t' :=
    lt_of_le_of_ne (le_sup_left.trans ht'.1.2) fun h => hx (by rw [h]; exact hxt')
  have ht'eq : t' = t0 := by
    by_contra hne
    exact absurd hKrull (not_le.2 (one_lt_height_map hpt' (lt_of_le_of_ne ht't0 hne)))
  exact hyt t' ht' (ht'eq ▸ ht0r') (ht'eq ▸ hyt0)

end Noetherian

theorem exists_lt_of_le_height {α : Type*} [Preorder α] {a : α} {n : ℕ}
    (h : ((n + 1 : ℕ) : ℕ∞) ≤ Order.height a) : ∃ b < a, (n : ℕ∞) ≤ Order.height b := by
  obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height a h
  have hne : p.length ≠ 0 := by omega
  refine ⟨p.eraseLast.last, hlast ▸ p.eraseLast_last_rel_last hne, ?_⟩
  have := Order.length_le_height_last (p := p.eraseLast)
  simp only [RelSeries.eraseLast_length, hlen, Nat.add_sub_cancel] at this
  exact this

theorem comap_C_eq_bot {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {σ : Type*} {ϖ : O} (hϖ : Irreducible ϖ) (Q : Ideal (MvPolynomial σ O)) [Q.IsPrime]
    (h : (C ϖ : MvPolynomial σ O) ∉ Q) : Q.comap (C : O →+* MvPolynomial σ O) = ⊥ := by
  by_contra hne
  have : (Q.comap (C : O →+* MvPolynomial σ O)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hne
  have hm := IsLocalRing.eq_maximalIdeal this
  apply h
  have : ϖ ∈ Q.comap (C : O →+* MvPolynomial σ O) := by
    rw [hm]; exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  exact this

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let Z := PrimeSpectrum.zeroLocus (R := MRing ι O) (P : Set (MRing ι O))
  let Z' := PrimeSpectrum.zeroLocus (R := MRing ι (FractionRing O))
    (genFib P : Set (MRing ι (FractionRing O)))
  let U := {q : Z // q.1.asIdeal.comap (C : O →+* MRing ι O) = ⊥}
  have ltZ : ∀ a b : Z, a < b ↔ a.1.asIdeal < b.1.asIdeal := fun a b =>
    Subtype.coe_lt_coe.symm.trans (PrimeSpectrum.asIdeal_lt_asIdeal _ _).symm
  have ltU : ∀ a b : U, a < b ↔ a.1.1.asIdeal < b.1.1.asIdeal := fun a b =>
    Subtype.coe_lt_coe.symm.trans (ltZ _ _)
  have memZ : ∀ x : PrimeSpectrum (MRing ι O), x ∈ Z ↔ P ≤ x.asIdeal := fun x =>
    PrimeSpectrum.mem_zeroLocus _ _
  let P0 : Z := ⟨⟨P, hP⟩, (memZ _).2 le_rfl⟩
  let PU : U := ⟨P0, hPC⟩

  have hstep : ∀ n : ℕ, ∀ r : Z, ((n + 1 : ℕ) : ℕ∞) ≤ Order.height r →
      ∃ q : U, q.1.1.asIdeal < r.1.asIdeal ∧ (n : ℕ∞) ≤ Order.height q := by
    intro n
    induction n with
    | zero =>
      intro r hr
      obtain ⟨r0, hr0, -⟩ := exists_lt_of_le_height hr
      exact ⟨PU, lt_of_le_of_lt ((memZ _).1 r0.2) ((ltZ _ _).1 hr0), by simp⟩
    | succ n ih =>
      intro r hr
      obtain ⟨r', hr'r, hr'⟩ := exists_lt_of_le_height hr
      obtain ⟨q, hqr', hq⟩ := ih r' hr'
      have hx : (C ϖ : MRing ι O) ∉ q.1.1.asIdeal := fun h => hϖ.ne_zero (by
        have : ϖ ∈ q.1.1.asIdeal.comap (C : O →+* MRing ι O) := h
        rw [q.2] at this
        exact (Submodule.mem_bot _).1 this)
      obtain ⟨q', hq'p, hqq', hq'r, hq'x⟩ :=
        exists_isPrime_between_not_mem hqr' ((ltZ _ _).1 hr'r) hx
      let qZ : Z := ⟨⟨q', hq'p⟩, (memZ _).2 (((memZ _).1 q.1.2).trans hqq'.le)⟩
      let qU : U := ⟨qZ, comap_C_eq_bot hϖ q' hq'x⟩
      refine ⟨qU, hq'r, ?_⟩
      have hlt : q < qU := (ltU _ _).2 hqq'
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ Order.height q + 1 := add_le_add hq le_rfl
        _ ≤ Order.height qU := Order.height_add_one_le hlt
  have hbound : ∀ r : Z, Order.height r ≤ (⨆ q : U, Order.height q) + 1 := by
    intro r
    refine ENat.forall_natCast_le_iff_le.1 fun m hm => ?_
    cases m with
    | zero => simp
    | succ m =>
      obtain ⟨q, -, hq⟩ := hstep m r hm
      push_cast
      exact add_le_add (hq.trans (le_iSup (fun q : U => Order.height q) q)) le_rfl

  have hdisj : ∀ q : U, Disjoint (M : Set (MRing ι O)) (q.1.1.asIdeal : Set (MRing ι O)) := by
    intro q
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ q.1.1.asIdeal.comap (C : O →+* MRing ι O) := hmem
    rw [q.2] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  let Φ : U → Z' := fun q =>
    ⟨⟨q.1.1.asIdeal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))),
      IsLocalization.isPrime_of_isPrime_disjoint M _ _ q.1.1.2 (hdisj q)⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact Ideal.map_mono ((memZ _).1 q.1.2)⟩
  have hΦ : StrictMono Φ := by
    intro a b hab
    rw [ltU] at hab
    refine Subtype.coe_lt_coe.1 ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 ?_)
    refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
    have ha := IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O))
      a.1.1.2 (hdisj a)
    have hb := IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O))
      b.1.1.2 (hdisj b)
    rw [← ha, ← hb]
    exact congrArg (Ideal.comap _) h
  have : Nonempty Z := ⟨P0⟩
  have : Nonempty U := ⟨PU⟩
  calc Order.krullDim Z = ((⨆ r : Z, Order.height r : ℕ∞) : WithBot ℕ∞) :=
        Order.krullDim_eq_iSup_height_of_nonempty
    _ ≤ (((⨆ q : U, Order.height q) + 1 : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.2 (iSup_le hbound)
    _ = Order.krullDim U + 1 := by
        rw [Order.krullDim_eq_iSup_height_of_nonempty (α := U)]; rfl
    _ ≤ Order.krullDim Z' + 1 := add_le_add (Order.krullDim_le_of_strictMono Φ hΦ) le_rfl

end GenericDimGe

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventualValueFacts.proof : EventualValueFacts.Statement := by
  intro K f c s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨c, h⟩
    rw [eventualValue, dite_eq_left hex]
    obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
    exact hm1.symm.trans hm2
  · have ht : Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b + s, fun a ha => ?_⟩
      simpa using sub_le_sub_right ha s
    exact ht.eventually h

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsComponentDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def ComponentDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P →
      ∀ W : Ideal (MRing ι O), divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W →
        ringKrullDim (MRing ι O ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem component_mul_multiHomog {R : Type*} [CommRing R] {K : Type} [DecidableEq K]
    {ι : K → Type} (y f : MRing ι R) (b s : K → ℕ) (hf : IsMultiHomog f s) :
    weightedHomogeneousComponent (blockWeight ι) b y * f =
      weightedHomogeneousComponent (blockWeight ι) (b + s) (y * f) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · rfl
    · by_cases h2 : AddMonoidAlgebra.coeff f x.2 = 0
      · rw [h2, mul_zero, mul_zero]
      · exfalso
        apply hx1
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add (f := _), hw] at hd
        exact add_right_cancel hd
  · refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hx1
    · by_cases h2 : AddMonoidAlgebra.coeff f x.2 = 0
      · rw [h2, mul_zero]
      · exfalso
        apply hd
        have hw := hf h2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [← hx, map_add (f := _), hw, hx1]
    · rw [zero_mul]

theorem ColonMultiHomog.proof : ColonMultiHomog.Statement := by
  intro R _ K _ ι I f s hI hf y hy b
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy ⊢
  rw [component_mul_multiHomog y f b s hf]
  exact hI _ hy _

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem localizedQuotient_subsingleton_of_not_le (Q W : Ideal A) [W.IsPrime] (h : ¬ Q ≤ W) :
    Subsingleton (LocalizedModule W.primeCompl (A ⧸ Q)) := by
  obtain ⟨q, hqQ, hqW⟩ := Set.not_subset.mp h
  rw [LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨q, hqW, ?_⟩
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Q.mul_mem_right a hqQ

theorem localizedQuotient_mk_eq_zero (W : Ideal A) [W.IsPrime] (a : A) (s : W.primeCompl)
    (h : LocalizedModule.mk (Ideal.Quotient.mk W a) s = 0) : a ∈ W := by
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hu
  exact (‹W.IsPrime›.mem_or_mem hu).resolve_left u.2

theorem localizedQuotient_isSimpleModule (W : Ideal A) [W.IsPrime] :
    IsSimpleModule (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ W)) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨⟨LocalizedModule.mk (Ideal.Quotient.mk W 1) 1, 0, fun h => ?_⟩, ?_⟩
  · exact ‹W.IsPrime›.ne_top ((Ideal.eq_top_iff_one W).mpr (localizedQuotient_mk_eq_zero W 1 1 h))
  intro x hx z
  induction x using LocalizedModule.induction_on with | h m s => ?_
  induction z using LocalizedModule.induction_on with | h m' t => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m'
  have ha : a ∈ W.primeCompl := fun haW => hx (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haW, LocalizedModule.zero_mk])
  refine ⟨Localization.mk ((s : A) * b) (⟨a, ha⟩ * t), ?_⟩
  rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul]
  congr 1
  ring

end General

theorem MultAtPrimeAtMinimal.proof : MultAtPrimeAtMinimal.Statement := by
  intro R _ K ι J Q W _ _ hJQ hW
  unfold multAt
  by_cases hQW : Q ≤ W
  · have hEq : Q = W := le_antisymm hQW (hW.2 ⟨‹Q.IsPrime›, hJQ⟩ hQW)
    subst hEq
    rw [if_pos rfl, Module.length_eq_one_iff]
    exact localizedQuotient_isSimpleModule Q
  · have hne : Q ≠ W := fun h => hQW h.le
    rw [if_neg hne, Module.length_eq_zero_iff]
    exact localizedQuotient_subsingleton_of_not_le Q W hQW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTopDimMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem TopDimMinimal.proof (h1 : DimStrictDrop.Statement.{u}) : TopDimMinimal.Statement.{u} := by
  intro A _ J Q _ N hJQ hJ hQ
  by_contra hmin
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hWne : W ≠ Q := fun h => hmin (h ▸ hW)
  have hWlt : W < Q := lt_of_le_of_ne hWQ hWne
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := hW.1.2
  have h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W) := h1 A W Q hWlt
  have h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)
  have h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1 :=
    add_le_add (not_lt.mp hQ) le_rfl
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1 := Nat.cast_succ N
  exact lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
