module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
noncomputable section

namespace GlobalTheory.PRep

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

def eig (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) : Submodule k V where
  carrier := {v | ∀ h : H, ρ (h : G) v = (χ h : k) • v}
  add_mem' := by
    intro a b ha hb h
    rw [map_add (f := _), ha h, hb h, smul_add]
  zero_mem' := by intro h; simp
  smul_mem' := by
    intro c v hv h
    rw [map_smul, hv h, smul_comm]

def fixed (ρ : Representation k G V) (H : Subgroup G) : Submodule k V := eig ρ H 1

def twKer (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w | ∃ (n : N) (v : V), w = ρ (n : G) v - (ψ n : k) • v}

abbrev TwJacquet (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Type := V ⧸ twKer ρ N ψ

abbrev Jacquet (ρ : Representation k G V) (N : Subgroup G) : Type := TwJacquet ρ N 1

theorem twKer_le_comap (ρ : Representation k G V) (N : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    twKer ρ N 1 ≤ (twKer ρ N 1).comap (ρ g) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  have hn : g * (n : G) * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 hg n).1 n.2
  refine Submodule.subset_span ⟨⟨_, hn⟩, ρ g v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

def jacquet (ρ : Representation k G V) (N : Subgroup G) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) : Representation k M (Jacquet ρ N) where
  toFun m := (twKer ρ N 1).mapQ (twKer ρ N 1) (ρ (s m)) (twKer_le_comap ρ N _ (hs m))
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

def onFixed (ρ : Representation k G V) (N : Subgroup G) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) : Representation k M (fixed ρ N) where
  toFun m := (ρ (s m)).restrict (p := fixed ρ N) (q := fixed ρ N) (by
    intro v hv n
    have hn : (s m)⁻¹ * (n : G) * (s m)⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem (hs m)) n).1 n.2
    have h := hv ⟨_, hn⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h ⊢
    conv_rhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp only [map_mul]
    rfl

section Top
variable [TopologicalSpace G]

def IsSmooth (ρ : Representation k G V) : Prop := ∀ v : V, IsOpen {g : G | ρ g v = v}

def IsAdmissible (ρ : Representation k G V) : Prop :=
  IsSmooth ρ ∧ ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional k (fixed ρ K)

end Top

variable {W : Type} [AddCommGroup W] [Module k W]

def rightReg (k G W : Type) [Field k] [Group G] [AddCommGroup W] [Module k W] :
    Representation k G (G → W) where
  toFun g := LinearMap.funLeft k W (fun x => x * g)
  map_one' := by ext f x; simp [LinearMap.funLeft]
  map_mul' a b := by ext f x; simp [LinearMap.funLeft, mul_assoc]

def indSpace (H : Subgroup G) (σ : Representation k H W) : Submodule k (G → W) where
  carrier := {f | ∀ (h : H) (g : G), f (h * g) = σ h (f g)}
  add_mem' := by
    intro a b ha hb h g
    simp [ha h g, hb h g]
  zero_mem' := by intro h g; simp
  smul_mem' := by
    intro c f hf h g
    simp [hf h g]

def sub (ρ : Representation k G V) (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) :
    Representation k G U where
  toFun g := (ρ g).restrict (hU g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

def ind (H : Subgroup G) (σ : Representation k H W) : Representation k G (indSpace H σ) :=
  sub (rightReg k G W) (indSpace H σ) (by
    intro g f hf h x
    have := hf h (x * g)
    simpa [rightReg, LinearMap.funLeft, mul_assoc] using this)

section Top2
variable [TopologicalSpace G] [IsTopologicalGroup G]

def smoothPart (ρ : Representation k G V) : Submodule k V where
  carrier := {v | IsOpen {g : G | ρ g v = v}}
  add_mem' := by
    intro a b ha hb
    let T : Subgroup G :=
      { carrier := {g | ρ g (a + b) = a + b}
        mul_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *; rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]; simp }
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((ha.inter hb).mem_nhds (by simp)) ?_)
    rintro g ⟨h1, h2⟩
    show ρ g (a + b) = a + b
    rw [map_add (f := _), h1, h2]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    by_cases hc : c = 0
    · simp [hc]
    · have : {g : G | ρ g (c • v) = c • v} = {g : G | ρ g v = v} := by
        ext g; simp [smul_right_inj hc]
      show IsOpen {g : G | ρ g (c • v) = c • v}
      rw [this]; exact hv

theorem smoothPart_stable (ρ : Representation k G V) (g : G) (v : V) (hv : v ∈ smoothPart ρ) :
    ρ g v ∈ smoothPart ρ := by
  have : {x : G | ρ x (ρ g v) = ρ g v} = (fun x => g⁻¹ * x * g) ⁻¹' {x : G | ρ x v = v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
    constructor
    · intro h; rw [h, ← Module.End.mul_apply, ← map_mul]; simp
    · intro h
      have := congrArg (ρ g) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  show IsOpen {x : G | ρ x (ρ g v) = ρ g v}
  rw [this]
  exact IsOpen.preimage (by fun_prop) hv

def smoothRep (ρ : Representation k G V) : Representation k G (smoothPart ρ) :=
  sub ρ (smoothPart ρ) (smoothPart_stable ρ)

def smInd (H : Subgroup G) (σ : Representation k H W) :
    Representation k G (smoothPart (ind H σ)) := smoothRep (ind H σ)

def cIndSpace (H : Subgroup G) (σ : Representation k H W) : Submodule k (smoothPart (ind H σ)) where
  carrier := {f | ∃ C : Set G, IsCompact C ∧ ∀ g, f.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c}
  add_mem' := by
    rintro a b ⟨C, hC, ha⟩ ⟨D, hD, hb⟩
    refine ⟨C ∪ D, hC.union hD, fun g hg => ?_⟩
    by_cases h : a.1.1 g = 0
    · obtain ⟨h, hh, c, hc, e⟩ := hb g (by intro h'; apply hg; simp [h, h'])
      exact ⟨h, hh, c, Or.inr hc, e⟩
    · obtain ⟨h, hh, c, hc, e⟩ := ha g h
      exact ⟨h, hh, c, Or.inl hc, e⟩
  zero_mem' := ⟨∅, isCompact_empty, by simp⟩
  smul_mem' := by
    rintro c f ⟨C, hC, hf⟩
    exact ⟨C, hC, fun g hg => hf g (by intro h; apply hg; simp [h])⟩

def cInd (H : Subgroup G) (σ : Representation k H W) : Representation k G (cIndSpace H σ) :=
  sub (smInd H σ) (cIndSpace H σ) (by
    rintro g f ⟨C, hC, hf⟩
    refine ⟨(fun c => c * g⁻¹) '' C, hC.image (by fun_prop), fun x hx => ?_⟩
    obtain ⟨h, hh, c, hc, e⟩ := hf (x * g) hx
    exact ⟨h, hh, c * g⁻¹, ⟨c, hc, rfl⟩, by rw [← mul_assoc, ← e]; group⟩)

def IsSupercuspidal (ρ : Representation k G V) : Prop :=
  IsSmooth ρ ∧ ∀ (v : V) (l : Module.Dual k V), l ∈ smoothPart ρ.dual →
    ∃ C : Set G, IsCompact C ∧ ∀ g, l (ρ g v) ≠ 0 → ∃ z ∈ Subgroup.center G, ∃ c ∈ C, g = z * c

end Top2

end GlobalTheory.PRep
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

def SB (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨(IsLocallyConstant.const c).mul hf.1, hf.2.smul_left (f := fun _ => c)⟩

def IsSmoothRep {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop := ∀ v : V, IsOpen {g : G | ρ g v = v}

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def nabs (x : kˣ) : ℝ := (distribHaarChar k x : ℝ≥0)

def resCard : ℕ := Nat.card 𝓀[k]

def KO (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  (Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)).range

def KOne (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  ((Matrix.GeneralLinearGroup.map (n := n) (IsLocalRing.residue 𝒪[k])).ker).map
    (Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k))

variable {k}

def HasConductor (ψ : AddChar k Circle) (c : kˣ) : Prop :=
  ∀ x : k, (∀ y : k, valuation k y ≤ valuation k x → ψ y = 1) ↔ valuation k x ≤ valuation k (c : k)

def IsTame (μ : kˣ →* ℂˣ) : Prop := ∀ x : kˣ, valuation k ((x : k) - 1) < 1 → μ x = 1

def IsUnram (μ : kˣ →* ℂˣ) : Prop := ∀ x : kˣ, valuation k (x : k) = 1 → μ x = 1

def om {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) : Matrix b a k → ℂ := fun x =>
  (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det g) ^ ((Fintype.card b : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ) / 2) : ℝ) : ℂ) *
    Φ ((h⁻¹ : GL b k).val * x * g.val)

instance matrixMeasurableSpace {m n α : Type*} [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
  (MeasurableSpace.pi : MeasurableSpace (m → n → α))

variable [MeasurableSpace k] [BorelSpace k]

def IsUnitVol (ν : Measure k) : Prop := ν.IsAddHaarMeasure ∧ ν (𝒪[k] : Set k) = 1

def IsSelfDual (ψ : AddChar k Circle) (ν : Measure k) : Prop :=
  ν.IsAddHaarMeasure ∧ ∀ f ∈ SB k, ∫ y, (∫ x, f x * (ψ (x * y) : ℂ) ∂ν) ∂ν = f 0

def volM (ν : Measure k) (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n k) :=
  (Measure.pi fun _ : m => Measure.pi fun _ : n => ν : Measure (m → n → k))

def volGL (ν : Measure k) (n : Type*) [Fintype n] [DecidableEq n] : Measure (GL n k) :=
  ((volM ν n n).comap (fun g : GL n k => g.val)).withDensity fun g =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ)))

def ip (ν : Measure k) {m n : Type*} [Fintype m] [Fintype n] (Φ₁ Φ₂ : Matrix m n k → ℂ) : ℂ :=
  ∫ x, Φ₁ x * (starRingEnd ℂ) (Φ₂ x) ∂(volM ν m n)

end GlobalTheory.SplitWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

namespace GlobalTheory.Hk

def lev (N l : ℕ) : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 l

def uOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q))

def vOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ := f (ofComplex ((q : ℂ) * τ))

def IsDia (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : Prop :=
  ((σ 1 0 : ℤ) : ZMod (N * l)) = 0 ∧ ((σ 1 1 : ℤ) : ZMod N) = d

def dia (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ := f ∣[k] σ

def heckeT (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ :=
  uOp q f + ((q : ℂ) ^ (k - 1)) • vOp q (f ∣[k] σ)

def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

def pet (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ Γ, ∫ z in ModularGroup.fd, petersson k f g (γ.out⁻¹ • z)

def pmGrp (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Γ ∨ -γ ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have h : -a⁻¹ = (-a)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; simp
      rw [h]; exact Γ.inv_mem ha

theorem le_pmGrp (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmGrp Γ := fun _ h => Or.inl h

theorem neg_one_mem_pmGrp (Γ : Subgroup SL(2, ℤ)) : -1 ∈ pmGrp Γ :=
  Or.inr (by simpa using Γ.one_mem)

theorem pmGrp_eq_self {Γ : Subgroup SL(2, ℤ)} (h : -1 ∈ Γ) : pmGrp Γ = Γ := by
  apply le_antisymm _ (le_pmGrp Γ)
  rintro γ (hγ | hγ)
  · exact hγ
  · simpa using Γ.mul_mem h hγ

instance pmGrp_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (pmGrp Γ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pmGrp Γ)

theorem relIndex_pmGrp_of_notMem {Γ : Subgroup SL(2, ℤ)} (h : -1 ∉ Γ) :
    Γ.relIndex (pmGrp Γ) = 2 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨-1, neg_one_mem_pmGrp Γ⟩, ?_⟩
  rintro ⟨b, hb⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mul_neg, mul_one]
  have hne : ¬ (b ∈ Γ ∧ -b ∈ Γ) := fun ⟨h1, h2⟩ => h (by simpa using Γ.mul_mem h2 (Γ.inv_mem h1))
  rcases hb with hb | hb
  · exact Or.inr ⟨hb, fun h2 => hne ⟨hb, h2⟩⟩
  · exact Or.inl ⟨hb, fun h1 => hne ⟨h1, hb⟩⟩

theorem neg_one_notMem_lev {N : ℕ} (l : ℕ) (hN : 3 ≤ N) : -1 ∉ lev N l := by
  rintro ⟨h, -⟩
  have h1 := ((Gamma1_mem N _).1 h).1
  have h2 : (((-1 : ℤ) : ℤ) : ZMod N) = 1 := by simpa using h1
  have h3 : ((2 : ℕ) : ZMod N) = 0 := by
    push_cast at h2 ⊢
    linear_combination -h2
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd two_pos h3
  omega

def petProd (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ pmGrp Γ, ∫ z in ModularGroup.fd, petersson k g f (γ.out⁻¹ • z)

theorem petProd_smul_left (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    petProd Γ k (c • f) g = c * petProd Γ k f g := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← integral_const_mul]
  congr 1
  ext z
  simp [petersson]
  ring

theorem petProd_smul_right (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    petProd Γ k f (c • g) = (starRingEnd ℂ) c * petProd Γ k f g := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← integral_const_mul]
  congr 1
  ext z
  simp [petersson]
  ring

theorem petProd_level_one (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) {f g : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), f ∣[k] γ = f) (hg : ∀ γ : SL(2, ℤ), g ∣[k] γ = g) :
    petProd Γ k f g = ((pmGrp Γ).index : ℂ) * ∫ z in ModularGroup.fd, petersson k g f z := by
  unfold petProd
  haveI : Fintype (SL(2, ℤ) ⧸ pmGrp Γ) := Fintype.ofFinite _
  simp only [← petersson_slash_SL, hf, hg]
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Subgroup.index, Nat.card_eq_fintype_card]
  simp

end GlobalTheory.Hk
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
noncomputable section

open Polynomial Matrix
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

abbrev mat (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ)

def slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  ∑ i ∈ Finset.range (w + 1),
    (LinearMap.toSpanSingleton ℂ ℂ[X]
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i))).comp (lcoeff ℂ i)

def Z1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) where
  carrier := {z | (∀ γ, z γ ∈ degreeLT ℂ (w + 1)) ∧
    ∀ γ δ : Γ, z (γ * δ) = slP w (mat δ) (z γ) + z δ}
  add_mem' := by
    rintro z z' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => Submodule.add_mem _ (h1 γ) (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add (f := _)]
    abel
  zero_mem' := ⟨fun _ => Submodule.zero_mem _, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c z ⟨h1, h2⟩
    refine ⟨fun γ => Submodule.smul_mem _ c (h1 γ), fun γ δ => ?_⟩
    simp only [Pi.smul_apply, h2, map_smul, smul_add]

def B1 (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Submodule ℂ (Γ → ℂ[X]) :=
  LinearMap.range ((LinearMap.pi fun γ : Γ => slP w (mat γ) - LinearMap.id).comp (degreeLT ℂ (w + 1)).subtype)

def IsDCReps (Γ : Subgroup SL(2, ℤ)) (α : Matrix (Fin 2) (Fin 2) ℤ) {ι : Type} (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    Prop :=
  (∀ i, ∃ γ₁ γ₂ : Γ, δ i = mat γ₁ * α * mat γ₂) ∧
    ∀ γ₁ γ₂ : Γ, ∃! i, ∃ γ : Γ, mat γ₁ * α * mat γ₂ = mat γ * δ i


open Classical in
def hk (Γ : Subgroup SL(2, ℤ)) (w : ℕ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) :
    (Γ → ℂ[X]) →ₗ[ℂ] (Γ → ℂ[X]) :=
  by
    classical
    exact LinearMap.pi fun γ : Γ =>
      if h : ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i) then
        ∑ i, (slP w (δ (h.choose i))).comp (LinearMap.proj (h.choose_spec i).choose)
      else 0

def dg (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, 0; 0, b]

def Lev (N l : ℕ) : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l

def IsDiam (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) : Prop :=
  σ ∈ CongruenceSubgroup.Gamma0 (N * l) ∧ ((mat σ 1 1 : ℤ) : ZMod N) = d

def tqFam (q : ℕ) (σ : SL(2, ℤ)) : Fin (q + 1) → Matrix (Fin 2) (Fin 2) ℤ := fun i =>
  if (i : ℕ) < q then !![1, (i : ℤ); 0, (q : ℤ)] else mat σ * dg q 1

def ulFam (l : ℕ) : Fin l → Matrix (Fin 2) (Fin 2) ℤ := fun j => !![1, (j : ℤ); 0, (l : ℤ)]

def TqZ (Γ : Subgroup SL(2, ℤ)) (w q : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (tqFam q σ)

def UlZ (Γ : Subgroup SL(2, ℤ)) (w l : ℕ) : Module.End ℂ (Γ → ℂ[X]) := hk Γ w (ulFam l)

def DdZ (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (σ : SL(2, ℤ)) : Module.End ℂ (Γ → ℂ[X]) :=
  hk Γ w (fun _ : Unit => mat σ)

def toGL (g : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : g.det = 0 then 1 else
    Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix g)
      (by rw [← RingHom.map_det]; simpa using h)


open scoped ModularForm in
def hkF (k : ℤ) {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ∑ i, f ∣[k] toGL (δ i)

def TqF (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (tqFam q σ) f

def UlF (k : ℤ) (l : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ := hkF k (ulFam l) f

def DdF (k : ℤ) (σ : SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  hkF k (fun _ : Unit => mat σ) f

def eichler (w : ℕ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ[X] :=
  ∑ j ∈ Finset.range (w + 1),
    C ((w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) * X ^ j

def per (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : UpperHalfPlane → ℂ) : Γ → ℂ[X] := fun γ =>
  slP w (mat γ) (eichler w f ((γ : SL(2, ℤ)) • UpperHalfPlane.I))

def cj {Γ : Type} (z : Γ → ℂ[X]) : Γ → ℂ[X] := fun γ => (z γ).map (starRingEnd ℂ)

end GlobalTheory.HeckeFamilyMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
noncomputable section

namespace GlobalTheory.AlmostEt

open scoped NNReal

variable {L : Type*} [Field L]

def ApproxRoot (p : ℕ) (v : Valuation L ℝ≥0) (F : Subfield L) : Prop :=
  ∃ θ : ℝ≥0, θ < 1 ∧ ∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u

variable {G : Type*} [Group G] [MulSemiringAction G L]

abbrev Fix (L : Type*) [Field L] {G : Type*} [Group G] [MulSemiringAction G L] (N : Subgroup G) :
    Subfield L := FixedPoints.subfield N L

def Moves (v : Valuation L ℝ≥0) (F : Subfield L) (σ : G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ x ∈ F, v x ≤ 1 ∧ r < v (σ • x - x)

structure IsSep (v : Valuation L ℝ≥0) (N : Subgroup G) {n : ℕ} (a b : Fin n → L) (c : L) : Prop where
  a_mem : ∀ i, a i ∈ Fix L N
  b_mem : ∀ i, b i ∈ Fix L N
  c_mem : c ∈ Fix L N
  a_le : ∀ i, v (a i) ≤ 1
  b_le : ∀ i, v (b i) ≤ 1
  c_le : v c ≤ 1
  sum_in : ∀ σ : G, σ ∈ N → ∑ i, a i * σ • b i = c
  sum_out : ∀ σ : G, σ ∉ N → ∑ i, a i * σ • b i = 0

def AlmostSep (v : Valuation L ℝ≥0) (N : Subgroup G) : Prop :=
  ∀ r : ℝ≥0, r < 1 → ∃ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c ∧ r < v c

def cosetTrace (N : Subgroup G) [Fintype (G ⧸ N)] (x : L) : L := ∑ q : G ⧸ N, q.out • x

end GlobalTheory.AlmostEt
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
noncomputable section

open Polynomial

namespace GlobalTheory.NeedB

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

def kum {N : ℕ} (ζ θ : Ω) (g : Ω ≃ₐ[K] Ω) : ZMod N :=
  open Classical in
  if h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ then h.choose else 0

def Inert (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, B.valuation x ≤ 1 → B.valuation (g x - x) < 1

def Over (R : Subring K) (B : ValuationSubring Ω) : Prop :=
  ∀ x ∈ R, algebraMap K Ω x ∈ B

def RY (R : Subring K) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (Subgroup.normalClosure {g | ∃ B : ValuationSubring Ω, Over R B ∧ Inert B g}).topologicalClosure

def ThmA : Prop :=
  ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
      a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ α (g * h) = kum ζ α g + kum ζ α h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ α) ∧
      (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ β (g * h) = kum ζ β g + kum ζ β h) ∧
      IsLocallyConstant (kum (K := K) (N := N) ζ β) ∧
      ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧
        (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) ∧
        ∀ B : ValuationSubring Ω, Over (FunctionField.ringOfIntegers k K).toSubring B → ∀ g, Inert B g → η g = 0

def IsFirstChernClassOfLineBundle (K : Type*) [Field K] : Prop :=
  ∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n →
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0

def Tsen : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K] [FiniteDimensional (RatFunc k) K], IsFirstChernClassOfLineBundle K

def ClDiv : Prop :=
  ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 0 < N →
    ∀ c : ClassGroup (FunctionField.ringOfIntegers k K), ∃ d, c = d ^ N

theorem kum_choose_spec {N : ℕ} {ζ θ : Ω} {g : Ω ≃ₐ[K] Ω} (h : ∃ i : ZMod N, g θ = ζ ^ i.val * θ) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  classical
  unfold kum
  rw [dite_eq_left h]
  exact h.choose_spec

theorem kum_eq_of {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) {g : Ω ≃ₐ[K] Ω}
    (i : ZMod N) (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i := by
  have hs := kum_choose_spec (N := N) ⟨i, hi⟩
  rw [hi] at hs
  have h2 : ζ ^ i.val = ζ ^ (kum (N := N) ζ θ g).val := mul_right_cancel₀ hθ hs
  exact (ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)).symm

theorem kum_one {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) :
    kum (N := N) ζ θ (1 : Ω ≃ₐ[K] Ω) = 0 :=
  kum_eq_of hζ hθ 0 (by simp)

theorem inert_one (B : ValuationSubring Ω) : Inert B (1 : Ω ≃ₐ[K] Ω) := by
  intro x _
  simp

theorem mem_RY_of_inert (R : Subring K) {B : ValuationSubring Ω} (hB : Over R B) {g : Ω ≃ₐ[K] Ω} (hg : Inert B g) :
    g ∈ RY R :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨B, hB, hg⟩)

theorem over_top (R : Subring K) : Over R (⊤ : ValuationSubring Ω) := fun _ _ => trivial

end GlobalTheory.NeedB
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
noncomputable section

open scoped Matrix

namespace GlobalTheory.KA

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]

def ShCoc {X : Type*} [Monoid X] (ρ : Γ → Matrix (Fin 2) (Fin 2) R) (κ : Γ →* X) (Y : Γ → X → Fin 2 → R) : Prop :=
  ∀ s t x, Y (s * t) x = Y s x + ρ s *ᵥ Y t (x * κ s)

def push {X X' : Type*} [Fintype X'] [DecidableEq X] {M : Type*} [AddCommMonoid M] (π : X' → X) (Y : Γ → X' → M) :
    Γ → X → M :=
  fun s x => ∑ x' ∈ Finset.univ.filter (fun x' => π x' = x), Y s x'

def spec {X : Type*} [Fintype X] (η : X → R) (Y : Γ → X → Fin 2 → R) : Γ → Fin 2 → R :=
  fun s => ∑ x, η x • Y s x

end GlobalTheory.KA

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.Integral
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def frc (M : ℕ) (a : ℤ) : ℚ := ((a % (M : ℤ) : ℤ) : ℚ) / M

def const0 (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) : K :=
  if j = 1 then
    (if (M : ℤ) ∣ a₁ then (1 / 2 : K) * (1 + ζ ^ a₂) / (1 - ζ ^ a₂) else ((1 / 2 - frc M a₁ : ℚ) : K))
  else -(((Polynomial.bernoulli j).eval (frc M a₁) / j : ℚ) : K)

def coefPos (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  ∑ d ∈ n.divisors,
    ((if ((n / d : ℕ) : ℤ) ≡ a₁ [ZMOD M] then (((n / d : ℕ) : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0) -
     (if (-((n / d : ℕ) : ℤ)) ≡ a₁ [ZMOD M] then (-(((n / d : ℕ) : K) / M)) ^ (j - 1) * ζ ^ (-(a₂ * d)) else 0))

def eisF (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  if n = 0 then const0 j M ζ a₁ a₂ else coefPos j M ζ a₁ a₂ n

def smF (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  (c : K) ^ 2 * eisF j M ζ a₁ a₂ n - (c : K) ^ ((2 : ℤ) - j) * eisF j M ζ (c * a₁) (c * a₂) n

def cmul (f g : ℕ → K) (n : ℕ) : K := ∑ i ∈ range (n + 1), f i * g (n - i)

def up (p : ℕ) (f : ℕ → K) (n : ℕ) : K := f (p * n)

def vp (p : ℕ) (f : ℕ → K) (n : ℕ) : K := if p ∣ n then f (n / p) else 0

def rowIdx (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (y : ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * y)

def unitSet (p n : ℕ) [NeZero p] : Finset (GL (Fin 2) (ZMod (p ^ n))) :=
  Finset.univ.filter fun γ => ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧
    ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val

def gaussS (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (ζm : K) : K :=
  ∑ a : ZMod (p ^ m), ψ a * ζm ^ a.val

def ffPos (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ d) && ¬ p ∣ (n / d) then
    (ψ ((n / d : ℕ) : ZMod (p ^ m)) * ((n / d : ℕ) : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d) -
     ψ (-((n / d : ℕ) : ZMod (p ^ m))) * (-((n / d : ℕ) : K)) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (-(x * t * d)))
    else 0

def eePos (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ (n / d)) && ¬ p ∣ d then
    (ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d) -
     ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) * (ζ ^ (p ^ m)) ^ (-(t * d)))
    else 0

def toQ (M : ℕ) (f : ℕ → K) (n : ℕ) : K := f (M * n)

def Integral (M : ℕ) (f : ℕ → K) : Prop := ∀ n, ¬ M ∣ n → f n = 0

end GlobalTheory.KummerEisensteinGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def ee (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

def cthFac (c : ℕ) (q t : ℂ) (m : ℕ) : ℂ :=
  (1 - q ^ m * t) ^ (c ^ 2) * (1 - q ^ m * t⁻¹) ^ (c ^ 2) / ((1 - q ^ m * t ^ c) * (1 - q ^ m * (t ^ c)⁻¹))

def cth (c : ℕ) (q t : ℂ) : ℂ :=
  q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (1 - t) ^ (c ^ 2) / (1 - t ^ c) *
    ∏' m : ℕ, cthFac c q t (m + 1)

def pt (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (x 0 : ℂ) * (τ : ℂ) + (x 1 : ℂ)

def sg (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := cth c (ee τ) (ee (pt x τ))


open Classical in
def f0 (j : ℕ) (x : Fin 2 → ℚ) : ℂ :=
  if j = 1 then (if Int.fract (x 0) = 0 then (1 / 2) * (1 + ee (x 1)) / (1 - ee (x 1)) else 1 / 2 - ((Int.fract (x 0) : ℚ) : ℂ))
  else -((((Polynomial.bernoulli j).eval (Int.fract (x 0)) : ℚ)) : ℂ) / j


open Classical in
def fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) (p : ℤ × ℤ) : ℂ :=
  if 0 < (x 0 + p.1) * p.2 then
    (Int.sign p.2 : ℂ) * ((x 0 + p.1 : ℚ) : ℂ) ^ (j - 1) * ee (((x 0 + p.1 : ℚ) : ℂ) * p.2 * (τ : ℂ)) * ee ((x 1 : ℂ) * p.2)
  else 0

def F (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := f0 j x + ∑' p : ℤ × ℤ, fTerm j x τ p

def cF (c j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (c : ℂ) ^ 2 * F j x τ - (c : ℂ) ^ (2 - (j : ℤ)) * F j (c • x) τ

def admitted (c : ℕ) (x : Fin 2 → ℚ) : Prop :=
  1 < c ∧ Nat.Coprime c 6 ∧ ¬ ((c : ℚ) * x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c : ℚ) * x 1 ∈ Set.range ((↑) : ℤ → ℚ))

end GlobalTheory.Sieg
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.KZ

def Hs : Set ℂ := {z | 0 < z.im}

abbrev Mero : Type := Filter.Germ (Filter.codiscreteWithin Hs) ℂ

abbrev GQ : Type := ↥(Matrix.GLPos (Fin 2) ℚ)

def ent (g : GQ) (i j : Fin 2) : ℚ := ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j

def mob (g : GQ) (z : ℂ) : ℂ :=
  ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))

def ofSL : SL(2, ℤ) →* GQ :=
  Matrix.SpecialLinearGroup.toGLPos.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ))

def en (γ : SL(2, ℤ)) (i j : Fin 2) : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) i j

def toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) : GQ :=
  if h : 0 < m.det then
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (m.map (Int.castRingHom ℚ))
        (by
          have e := RingHom.map_det (Int.castRingHom ℚ) m
          simp only [RingHom.mapMatrix_apply] at e
          rw [← e, eq_intCast]; exact_mod_cast h.ne'),
      by
        show 0 < Matrix.det (m.map (Int.castRingHom ℚ))
        have e := RingHom.map_det (Int.castRingHom ℚ) m
        simp only [RingHom.mapMatrix_apply] at e
        rw [← e, eq_intCast]; exact_mod_cast h⟩
  else 1

def eOm {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (x : ℚ) : Ω :=
  Function.invFun ε (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)))

structure Tower (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) where

  K : Type
  [fld : Field K]
  [alg : Algebra Ω K]

  exp : K →ₐ[Ω] HahnSeries ℚ Ω

  sl : GQ → (K ≃ₐ[Ω] K)

  sl_one : ∀ f, sl 1 f = f

  sl_mul : ∀ g h f, sl (g * h) f = sl h (sl g f)

  gal : (Ω ≃ₐ[ℚ] Ω) → (K ≃+* K)

  gal_exp : ∀ s f r, (exp (gal s f)).coeff r = s ((exp f).coeff r)

  an : K →+* Mero

  an_c : ∀ c : Ω, an (algebraMap Ω K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)

  an_sl : ∀ (g : GQ) (f : K) (φ : ℂ → ℂ), an f = (φ : Mero) → an (sl g f) = ((fun z => φ (mob g z)) : Mero)

  an_mero : ∀ f : K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
    an f * (b : Mero) = (a : Mero)

  an_exp : ∀ f : K, ∃ (φ : ℂ → ℂ) (C : ℝ), an f = (φ : Mero) ∧ ∀ z : ℂ, C < z.im →
    HasSum (fun r : ℚ => ε ((exp f).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ z)

  level : ∀ f : K, ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, sl (ofSL γ) f = f

  exp_upper : ∀ (g : GQ), ent g 1 0 = 0 → ∀ (f : K) (r : ℚ),
    (exp (sl g f)).coeff (r * ent g 0 0 / ent g 1 1) = eOm ε (r * ent g 0 1 / ent g 1 1) * (exp f).coeff r

  recip : ∀ (M : ℕ) (f : K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, sl (ofSL γ) f = f) →
    ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ),
      ((en γ' 0 0 : ZMod M) = en γ 0 0 ∧ (en γ' 0 1 : ZMod M) = d * en γ 0 1 ∧
        (d : ZMod M) * en γ' 1 0 = en γ 1 0 ∧ (en γ' 1 1 : ZMod M) = en γ 1 1) →
      gal s (sl (ofSL γ) f) = sl (ofSL γ') (gal s f)

  jK : K

  j_inv : ∀ γ : SL(2, ℤ), sl (ofSL γ) jK = jK

  j_exp : (exp jK).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (exp jK).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (exp jK).coeff r = n

  j_hol : ∃ φ : ℂ → ℂ, an jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs

  alg_j : ∀ f : K, IsAlgebraic (IntermediateField.adjoin Ω {jK}) f

  bdd : ∀ f : K, ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (exp f).coeff r)

  sat : ∀ (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) →
    (∃ P : Polynomial K, P ≠ 0 ∧ P.eval₂ an (((a / b : ℂ → ℂ)) : Mero) = 0) →
    ∃ f : K, an f * (b : Mero) = (a : Mero)

  mem_q : ∀ (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) →
    (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) →
    ∃ f : K, an f = (a : Mero)

attribute [instance] Tower.fld Tower.alg

end GlobalTheory.KZ
end
end
