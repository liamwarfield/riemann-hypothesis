module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AdjointDiagonalRepPreservesWeightPiece
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjStable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocComplY

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
noncomputable section

namespace UpperTheory.V.Loc

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing

structure Dat3 (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] where
  η : GQ l →* ℤˣ
  Ψ : GQ l →* Oˣ
  τ : GQ l →* Oˣ
  e : ℕ
  Kv : FinExt l
  odd : l ≠ 2
  e_pos : 1 ≤ e
  η_ker : ∀ g, η g = 1 ↔ g ∈ GK Kv
  η_unr : ∀ g ∈ Iq l, η g = 1
  τ_open : IsOpen (τ.ker : Set (GQ l))
  Ψ_cont : AdicCont (maximalIdeal O) fun g => (Ψ g : O)
  Ψ_I : ∀ g ∈ Iq l, Ψ g = cycA l l O g ^ e * τ g

def hodge0 (e : ℕ) (i : ℤ) : ℕ := if i = -(e : ℤ) ∨ i = 0 ∨ i = e then 1 else 0

namespace Dat3

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)

def HL : Subgroup (GQ l) := D.η.ker ⊓ D.τ.ker

def rz (A : Type) [CommRing A] [Algebra O A] : GQ l →* GG (m := 3) (R := A) :=
  (GG.map (algebraMap O A)).comp (r0 D.η D.Ψ)

section Types

variable {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]

def IsType (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ ρ : ↥(GK D.Kv) →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧
    PotCrysType D.Kv (colRep ρ) 3 (hodge0 D.e)
      fun γ => algebraMap O B ((D.τ γ : O) + 1 + (((D.τ γ)⁻¹ : Oˣ) : O))

def IsLCr (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ ρ : ↥D.HL →* GL (Fin 3) B, (∀ g, ρ g = (r g).left) ∧ IsCr D.HL.subtype (colRep ρ)

variable {E : Type} [CommRing E] [Algebra O E] (π : B →+* E)

structure InDcrAt (r₁ : GQ l →* GG (m := 3) (R := E))
    (r : GQ l →* GG (m := 3) (R := B)) : Prop where
  mult : HasMult D.η r
  red : (GG.map π).comp r = r₁
  cont : ∀ a b, QCont l fun g => (r g).mat a b
  cr : D.IsLCr r

abbrev InDcr (r : GQ l →* GG (m := 3) (R := B)) : Prop := D.InDcrAt π (D.rz E) r

structure InDtri (r : GQ l →* GG (m := 3) (R := B)) : Prop extends D.InDcrAt π (D.rz E) r where
  tri : ∀ g a b, wt a b < 0 → (r g).mat a b = 0

def InDord (r : GQ l →* GG (m := 3) (R := B)) : Prop :=
  ∃ (u : GQ l →* GG (m := 3) (R := B)) (n : GL (Fin 3) B), D.InDtri π u ∧ CongOne (RingHom.ker π) n ∧
    (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) B) - 1) a b = 0) ∧ r = conjBy n u

end Types

abbrev Univ : Type 1 := U3.Univ (GCond.noCondition O D.η D.Ψ)

section Ord

open Polynomial

def IsInertiaInfiniteCyclotomic (s : GQ l) : Prop := s ∈ D.HL ∧ s ∈ Iq l ∧ ¬ IsOfFinOrder (cyc l l s)

def IsFr (σ : GQ l) : Prop :=
  (∃ h : σ ∈ D.HL, ((Iq l).comap D.HL.subtype ⊔ Subgroup.zpowers (⟨σ, h⟩ : ↥D.HL)).topologicalClosure = ⊤) ∧
    ∃ (σ₀ : GQ l) (m : ℕ), IsFrob σ₀ ∧ 1 ≤ m ∧ (σ₀ ^ m)⁻¹ * σ ∈ Iq l

def s0 : GQ l := Classical.epsilon (IsInertiaInfiniteCyclotomic D)

def fr : GQ l := Classical.epsilon (IsFr D)

def cc (a : Fin 3) : O :=
  (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 1) (s0 D)) *
    (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D) - UpperTheory.V.UnitaryThreeInertia.psi D.Ψ (a + 2) (s0 D))

section Eq

variable {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C))

def sh (a : Fin 3) (s : GQ l) : Matrix (Fin 3) (Fin 3) C :=
  (r s).mat - Matrix.scalar _ (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s))

def ordIdeal : Ideal C :=
  Ideal.span ({x | ∃ s ∈ D.HL ⊓ Iq l, ∃ i : ℕ, x = ((r s).mat.charpoly -
      ∏ a, (X - Polynomial.C (algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a s)))).coeff i} ∪
    {x | ∃ s : Fin 3 → GQ l, (∀ a, s a ∈ D.HL ⊓ Iq l) ∧ ∃ i j,
      x = (sh D r 0 (s 0) * sh D r 1 (s 1) * sh D r 2 (s 2)) i j})

def tr (a : Fin 3) : C := (sh D r (a + 1) (s0 D) * sh D r (a + 2) (s0 D) * (r (fr D)).mat).trace

def dd (a : Fin 3) : C :=
  algebraMap O C (cc D (a + 1)) * tr D r a - algebraMap O C ((cycA l l O (fr D) : Oˣ) * cc D a) * tr D r (a + 1)

def del : C := (l : C) * dd D r 0 * dd D r 1

end Eq

end Ord

variable (U : D.Univ)

def IY : Ideal U.R where
  carrier := {a | ∃ n : ℕ, del D U.r.hom ^ n * a ∈ ordIdeal D U.r.hom}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have e : del D U.r.hom ^ (m + n) * (a + b) = del D U.r.hom ^ n * (del D U.r.hom ^ m * a) +
        del D U.r.hom ^ m * (del D U.r.hom ^ n * b) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)
  smul_mem' := by
    rintro c a ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ hn

def Icr : Ideal U.R := (IY D U).radical

def primesAt0 : Set (Ideal U.R) :=
  {P | P ∈ (D.Icr U).minimalPrimes ∧ ∀ x : U.R →ₐ[O] O, push x U.r.hom = r0 D.η D.Ψ → P ≤ RingHom.ker x}

def It : Ideal U.R := sInf (D.primesAt0 U)

abbrev Rt : Type := U.R ⧸ D.It U

def On {C : Type} [CommRing C] [Algebra O C] (r : GQ l →* GG (m := 3) (R := C)) : Prop :=
  ∃ f : U.R →ₐ[O] C, push f U.r.hom = r ∧ D.It U ≤ RingHom.ker f

def PtsCr (J : Ideal U.R) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B),
    J ≤ RingHom.ker f → D.IsLCr (push f U.r.hom)

def CrPts (J : Ideal U.R) : Prop :=
  ∀ (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E), (∀ a, π a = 0 → IsNilpotent a) → ∀ f : U.R →ₐ[O] B,
    D.InDcr (π : B →+* E) (push f U.r.hom) → J ≤ RingHom.ker f

end Dat3

structure IsCompl {O R E σ : Type} [CommRing O] [CommRing R] [Algebra O R] [Field E] [Algebra O E]
    (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries σ E) : Prop where
  ker : RingHom.ker φ = I
  const : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)
  dense : ∀ (N : ℕ) (f : MvPowerSeries σ E), ∃ (a : R) (c : O), c ≠ 0 ∧
    c • f - φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N
  inj : ∀ (N : ℕ) (a : R), φ a ∈ maximalIdeal (MvPowerSeries σ E) ^ N →
    ∃ c : O, c ≠ 0 ∧ c • a ∈ RingHom.ker x ^ N ⊔ I

def DualDef {G E : Type} [Group G] [CommRing E] (r : G →* GG (m := 3) (R := E))
    (γ : G → Matrix (Fin 3) (Fin 3) E) (r' : G →* GG (m := 3) (R := DualNumber E)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ ∀ a b, (r' g).mat a b = ⟨(r g).mat a b, (γ g * (r g).mat) a b⟩

end UpperTheory.V.Loc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
noncomputable section

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {Ω : Type} [Field Ω] [CharZero Ω] {v : ℕ} [Fact v.Prime]

def placeJ (j : Ω →+* Om v) : ValuationSubring Ω := (Valued.v : Valuation (Om v) NNReal).valuationSubring.comap j

variable [IsAlgClosure ℚ Ω]

def iota (j : Ω →+* Om v) : GQ v →* G ℚ Ω :=
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Om v) Ω).comp
    { toFun := fun σ => σ.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem iota_spec (j : Ω →+* Om v) (σ : GQ v) (y : Ω) : j (iota j σ y) = σ (j y) := by
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) Ω y

theorem exists_emb : Nonempty (Ω →+* Om v) := ⟨(IsAlgClosed.lift (R := ℚ) (S := Ω) (M := Om v)).toRingHom⟩

end UpperTheory.V.Loc
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OpenFix
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.GQ :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Gal(UpperTheory.Reformulated.B.Qi42.Om l/ℚ_[l])

theorem UpperTheory.Reformulated.B.Qi42.open_fix :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] (H : Subgroup (UpperTheory.Reformulated.B.Qi42.GQ v)),
      IsOpen (↑H : Set (UpperTheory.Reformulated.B.Qi42.GQ v)) → (IntermediateField.fixedField H).fixingSubgroup = H := by
  intro v inst H hH
  haveI : IsGalois ℚ_[v] (PadicAlgCl v) := IsAlgClosure.isGalois ℚ_[v] (PadicAlgCl v)
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem open_fix {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    (IntermediateField.fixedField H).fixingSubgroup = H :=
  _root_.UpperTheory.Reformulated.B.Qi42.open_fix H hH

private theorem open_index {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    H.index = finrank ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, open_fix H hH]

private theorem open_fin {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) (hH : IsOpen (H : Set (GQ v))) :
    FiniteDimensional ℚ_[v] ↥(IntermediateField.fixedField H) := by
  rw [← InfiniteGalois.isOpen_iff_finite, open_fix H hH]
  exact hH

private theorem fixed_sup {v : ℕ} [Fact v.Prime] (H : Subgroup (GQ v)) :
    IntermediateField.fixedField (H ⊔ Iq v) = IntermediateField.fixedField H ⊓ MaximalUnramifiedExtension v := by
  have h1 : IntermediateField.fixedField (Iq v) = MaximalUnramifiedExtension v := InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v)
  rw [← h1]
  apply le_antisymm
  · exact le_inf (IntermediateField.fixedField_le le_sup_left) (IntermediateField.fixedField_le le_sup_right)
  · rw [IntermediateField.le_iff_le]
    refine sup_le ?_ ?_
    · rw [← IntermediateField.le_iff_le]; exact inf_le_left
    · rw [← IntermediateField.le_iff_le]; exact inf_le_right

theorem UpperTheory.V.Loc.openField :
    ∀ {v : ℕ} [Fact v.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ), ∃ (K : FinExt v) (e : G ≃* ↥(GK K)), Continuous e ∧ Continuous e.symm ∧ (GK K).subtype.comp e.toMonoidHom = φ ∧ φ.range = GK K ∧ φ.range.index = finrank ℚ_[v] ↥K.1 ∧ (φ.range ⊔ Iq v).index = finrank ℚ_[v] ↥(K0 K) := by
  intro v _ G _ _ _ φ hφ
  have hH : IsOpen (φ.range : Set (GQ v)) := by
    rw [MonoidHom.coe_range]; exact hφ.isOpen_range
  let K : FinExt v := ⟨IntermediateField.fixedField φ.range, open_fin _ hH⟩
  have hK : φ.range = GK K := (open_fix _ hH).symm
  let e : G ≃* ↥(GK K) := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hK)
  have he : ∀ g, ((e g : ↥(GK K)) : GQ v) = φ g := fun g => rfl
  refine ⟨K, e, ?_, ?_, ?_, hK, open_index _ hH, ?_⟩
  · exact continuous_induced_rng.2 hφ.continuous
  · rw [hφ.isInducing.continuous_iff]
    have : φ ∘ e.symm = Subtype.val := by
      funext x
      rw [Function.comp_apply, ← he, MulEquiv.apply_symm_apply]
    rw [this]
    exact continuous_subtype_val
  · ext1 g
    exact he g
  · rw [open_index _ (Subgroup.isOpen_mono le_sup_left hH), fixed_sup]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

variable {l : ℕ} [Fact l.Prime]

private theorem iqb_unit (x : integralClosure ℤ_[l] (PadicAlgCl l)) (h : ‖(x : PadicAlgCl l)‖ = 1) : IsUnit x := by
  have h0 : (x : PadicAlgCl l) ≠ 0 := by
    intro e; rw [e, norm_zero] at h; exact zero_ne_one h
  refine IsUnit.of_mul_eq_one ⟨(x : PadicAlgCl l)⁻¹, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ?_⟩
    (Subtype.ext (mul_inv_cancel₀ h0))
  rw [norm_inv, h, inv_one]

private theorem iqb_local : IsLocalRing (integralClosure ℤ_[l] (PadicAlgCl l)) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have hx : ‖(x : PadicAlgCl l)‖ ≤ 1 := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 x.2
  rcases hx.eq_or_lt with h | h
  · exact Or.inl (iqb_unit x h)
  · refine Or.inr (iqb_unit _ ?_)
    have : ‖(1 : PadicAlgCl l)‖ ≠ ‖-(x : PadicAlgCl l)‖ := by rw [norm_one, norm_neg]; exact h.ne'
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this
    rw [norm_one, norm_neg, max_eq_left hx] at h2
    simpa [sub_eq_add_neg] using h2

private theorem iqb_frob : ∃ g : GQ l, IsFrob g := by
  haveI := iqb_local (l := l)
  have e : IsLocalRing.ResidueField ℤ_[l] ≃+* ZMod l := PadicInt.residueField
  obtain ⟨g, hg⟩ := GlobalTheory.exists_arithFrobenius_absGalois ℤ_[l] ℚ_[l] (Finite.of_equiv _ e.symm.toEquiv) (PadicAlgCl l)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨y, hy, hm⟩ := hg ⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod] at hm
  have hle := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
    (y - (⟨x, (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 hx⟩ : integralClosure ℤ_[l] (PadicAlgCl l)) ^ l).2
  have hne := mt (iqb_unit _) hm
  have := lt_of_le_of_ne hle hne
  simpa [hy] using this

private theorem iqb_norm (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := KStar.IdealValuations.norm_aut_and_roots.1 g x

private theorem iqb_sub {x y : Om l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by rwa [norm_neg]))

private theorem iqb_mem (g : GQ l) : g ∈ Iq l ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖g x - x‖ < 1 := by
  rw [Iq, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact iqb_sub (by rwa [iqb_norm]) hlt
    · obtain ⟨m, ζ, hm, hζ, hxζ⟩ := KStar.IdealValuations.exists_root_congr heq
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
      have h1 : g ζ = ζ := hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
      have h2 : g x - x = g (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
      rw [h2]
      exact iqb_sub (by rwa [iqb_norm]) hxζ
  · intro hg x hx
    have hle : MaximalUnramifiedExtension l ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      rw [MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
      rintro ζ ⟨m, hm0, hm, hζ⟩
      have hn : ‖ζ‖ = 1 := by
        have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζ, norm_one]
        exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0.ne').mp h1
      have h1 : g ζ = ζ := KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hζ, map_one]) hζ
        (hg ζ hn.le)
      have h2 : Subgroup.zpowers g ≤ MulAction.stabilizer (GQ l) ζ :=
        (Subgroup.zpowers_le (G := GQ l)).2 h1
      exact (IntermediateField.mem_fixedField_iff _ _).2 fun f hf => h2 hf
    exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) g (Subgroup.mem_zpowers g)

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.iqBasic :
    ∀ (v : ℕ) [Fact v.Prime], (Iq v).Normal ∧ IsClosed (Iq v : Set (GQ v)) ∧ (∀ g : GQ v, g ∈ Iq v ↔ ∀ x : Om v, ‖x‖ ≤ 1 → ‖g x - x‖ < 1) ∧ (∃ σ : GQ v, IsFrob σ) ∧ ∀ σ σ' : GQ v, IsFrob σ → (IsFrob σ' ↔ σ⁻¹ * σ' ∈ Iq v) := by
  intro v _
  refine ⟨⟨fun n hn g => ?_⟩, ?_, iqb_mem, iqb_frob, fun σ σ' hσ => ?_⟩
  · rw [iqb_mem] at hn ⊢
    intro x hx
    have h := hn (g⁻¹ x) (by rwa [iqb_norm])
    have e : (g * n * g⁻¹) x - x = g (n (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹ x, mul_inv_cancel,
        AlgEquiv.one_apply]
    rwa [e, iqb_norm]
  · have : IsGalois ℚ_[v] (Om v) := {}
    exact InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension v)
  · have e : ∀ x : Om v, ‖(σ⁻¹ * σ') x - x‖ = ‖σ' x - σ x‖ := fun x => by
      rw [← iqb_norm σ, map_sub, ← AlgEquiv.mul_apply, mul_inv_cancel_left]
    rw [iqb_mem]
    simp only [e]
    constructor
    · intro h x hx
      have h2 : σ' x - σ x = (σ' x - x ^ v) - (σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (hσ x hx)
    · intro h x hx
      have h2 : σ' x - x ^ v = (σ' x - σ x) - -(σ x - x ^ v) := by ring
      rw [h2]
      exact iqb_sub (h x hx) (by rw [norm_neg]; exact hσ x hx)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem idx_GK {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (Om l)) :
    K.fixingSubgroup.index = finrank ℚ_[l] K :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K).symm

private theorem sup_Iq {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    GK K ⊔ Iq l = (K0 K).fixingSubgroup := by
  haveI := K.2
  have ho : IsOpen ((GK K ⊔ Iq l : Subgroup (GQ l)) : Set (GQ l)) :=
    Subgroup.isOpen_mono le_sup_left (IntermediateField.fixingSubgroup_isOpen K.1)
  have hc := Subgroup.isClosed_of_isOpen _ ho
  have h1 := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ_[l]) (K := Om l) ⟨GK K ⊔ Iq l, hc⟩
  have h2 : IntermediateField.fixedField (GK K ⊔ Iq l) = K0 K := by
    apply le_antisymm
    · refine le_inf ?_ ?_
      · rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
        exact IntermediateField.fixedField_le le_sup_left
      · rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l)]
        exact IntermediateField.fixedField_le le_sup_right
    · rw [IntermediateField.le_iff_le]
      exact sup_le (IntermediateField.fixingSubgroup_le inf_le_left)
        (IntermediateField.fixingSubgroup_le inf_le_right)
  rw [← h2]
  exact h1.symm

theorem UpperTheory.V.Loc.isCrIff :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (ρ : Representation A ↥(GK K) V), (IsCr (GK K).subtype ρ ↔ Crys K ρ) ∧ (IsDr (GK K).subtype ρ ↔ DeRham K ρ) := by
  intro l _ K A _ _ V _ _ _ _ ρ
  have hC : Dcr (GK K).subtype (resCoef ℚ_[l] ρ) = Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Dcr Dcris
    refine iInf_congr fun g => ?_
    have : actC (GK K).subtype (resCoef ℚ_[l] ρ) g = actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actC actVB
      congr 1
      ext b
      exact ((PP l).PD_actB K g b).symm
    rw [this]
  have hD : Ddr (GK K).subtype (resCoef ℚ_[l] ρ) = DdR ((PP l).PD K) (resCoef ℚ_[l] ρ) := by
    unfold Ddr DdR
    refine iInf_congr fun g => ?_
    have : actD (GK K).subtype (resCoef ℚ_[l] ρ) g = actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g := by
      unfold actD actVdR
      congr 1
      ext b
      exact ((PP l).PD_actdR K g b).symm
    rw [this]
  constructor
  · unfold IsCr Crys IsCrys
    rw [hC, Subgroup.range_subtype, sup_Iq, idx_GK]
  · unfold IsDr DeRham IsDR
    rw [hD, Subgroup.range_subtype, show (GK K).index = finrank ℚ_[l] K.1 from idx_GK K.1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.z1fMap :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {A' : Type} [CommRing A'] [Algebra ℚ_[l] A'] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A' V'] (ρ : Representation A G V) (ρ' : Representation A' G V'), (ContAction ρ → ReciprocityTheory.Gal.B1 ρ ≤ UpperTheory.V.Loc.finiteCocycles φ ρ) ∧ ∀ f : V →ₗ[ℚ_[l]] V', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∀ c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ, (fun g => f (c g)) ∈ UpperTheory.V.Loc.finiteCocycles φ ρ' := by
  intro l _ G _ _ φ A _ _ A' _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ ρ ρ'
  refine ⟨fun hρ => ?_, fun f hf c hc => ?_⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨⟨?_, fun g h => ?_⟩, v ⊗ₜ[ℚ_[l]] (1 : Bcr l), fun g => ?_⟩
    · have h1 : Continuous fun g : G => ρ g v :=
        Continuous.comp (g := fun p : G × V => ρ p.1 p.2) (f := fun g : G => (g, v)) hρ (by fun_prop)
      exact h1.sub continuous_const
    · simp [ReciprocityTheory.Gal.d0]
    · simp [ReciprocityTheory.Gal.d0, actC, sub_tmul]
  · obtain ⟨⟨hc, hcc⟩, x, hx⟩ := hc
    have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
    refine ⟨⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Bcr l) f x, fun g => ?_⟩
    · simp only [hcc g h, map_add (f := _), hf]
    · have key : ∀ y : V ⊗[ℚ_[l]] Bcr l, LinearMap.rTensor (Bcr l) f (actC φ ρ g y) =
          actC φ ρ' g (LinearMap.rTensor (Bcr l) f y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [actC, hf]
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem cf_norm_root {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : n ≠ 0) {x : Om v} (hx : x ^ n = 1) :
    ‖x‖ = 1 := by
  have h := congrArg norm hx
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h

private theorem cf_root_one {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : ¬ v ∣ n) {x : Om v} (hx : x ^ n = 1)
    (h : ‖x - 1‖ < 1) : x = 1 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero v)
  by_contra hne
  have hx1 := cf_norm_root hn0 hx
  have hs : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have := mul_geom_sum x n
    rw [hx, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hp : ∀ i : ℕ, ‖x ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : x ^ (i + 1) - 1 = x * (x ^ i - 1) + (x - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rwa [norm_mul, hx1, one_mul]
  have hq : ∀ k : ℕ, ‖∑ i ∈ Finset.range k, x ^ i - (k : Om v)‖ < 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ∑ i ∈ Finset.range (k + 1), x ^ i - ((k + 1 : ℕ) : Om v) =
          (∑ i ∈ Finset.range k, x ^ i - (k : Om v)) + (x ^ k - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hp k))
  have h1 := hq n
  rw [hs, zero_sub, norm_neg] at h1
  have h2 : ((n : ℕ) : Om v) = algebraMap ℚ_[v] (Om v) (n : ℚ_[v]) := by simp
  rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
  exact hn h1

private theorem cf_root_eq {v : ℕ} [Fact v.Prime] {n : ℕ} (hn : ¬ v ∣ n) {x y : Om v} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (h : ‖x - y‖ < 1) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero v)
  have hy1 := cf_norm_root hn0 hy
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  have h1 : x / y = 1 := by
    refine cf_root_one hn (by rw [div_pow, hx, hy, div_one]) ?_
    rw [div_sub_one hy0, norm_div, hy1, div_one]
    exact h
  exact (div_eq_one_iff_eq hy0).1 h1

private theorem cf_toZModPow (v l : ℕ) [Fact v.Prime] [Fact l.Prime] (g : GQ v) (m a : ℕ)
    (h : ∀ ζ : Om v, IsPrimitiveRoot ζ (l ^ m) → g ζ = ζ ^ a) :
    PadicInt.toZModPow m ((cyc v l g : ℤ_[l]ˣ) : ℤ_[l]) = (a : ZMod (l ^ m)) := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om v) (l ^ m)
  have hs := cyclotomicCharacter.spec l (n := m)
    (MulSemiringAction.toRingAut (GQ v) (Om v) g) ζ hζ.pow_eq_one
  set c : ℤ_[l] := ((cyc v l g : ℤ_[l]ˣ) : ℤ_[l]) with hc
  have hs' : g ζ = ζ ^ (PadicInt.toZModPow m c).val := hs
  have h3 := hs'.symm.trans (h ζ hζ)
  have h4 : (PadicInt.toZModPow m c).val ≡ a [MOD l ^ m] := by
    have := (hζ.isOfFinOrder (NeZero.ne _)).pow_eq_pow_iff_modEq.mp h3
    rwa [← hζ.eq_orderOf] at this
  rw [← (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4, ZMod.natCast_zmod_val]

private theorem cf_chi (l : ℕ) [Fact l.Prime] (P : LocPrime l) (g : GQ l) :
    ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : l.Prime := Fact.out
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) -
      (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)
    obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ.pow_eq_one
    have h4 := cf_toZModPow l l g m a (fun ξ hξ => by
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
      rw [map_pow, hga, ← pow_mul, ← pow_mul, mul_comm])
    set c : ℤ_[l] := ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) with hc
    have h5 : PadicInt.toZModPow m ((a : ℤ_[l]) - c) = 0 := by
      rw [map_sub, map_natCast, h4, sub_self]
    have h6 : ‖(a : ℤ_[l]) - c‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow]
      exact h5
    have h7 : ‖(a : ℚ_[l]) - (c : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have : (((a : ℤ_[l]) - c : ℤ_[l]) : ℚ_[l]) = (a : ℚ_[l]) - (c : ℚ_[l]) := by push_cast; rfl
      rw [← this]; exact h6
    have h8 := IsUltrametricDist.norm_add_le_max (((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) ((a : ℚ_[l]) - c)
    rw [sub_add_sub_cancel] at h8
    exact h8.trans (max_le ha h7)
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have hlt : ((l : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  refine ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt) fun m => ?_
  have := key m
  rwa [zpow_neg, zpow_natCast, ← inv_pow] at this

theorem UpperTheory.V.Loc.cycFacts :
    ∀ (v l : ℕ) [Fact v.Prime] [Fact l.Prime], Continuous (cyc v l) ∧
      (v ≠ l → (∀ g ∈ Iq v, cyc v l g = 1) ∧
        ∀ σ : GQ v, UpperTheory.V.Loc.IsFrob σ → ((cyc v l σ : ℤ_[l]ˣ) : ℤ_[l]) = (v : ℤ_[l])) ∧
      ∀ g : GQ l, (((PP l).χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  intro v l _ _
  have hl : l.Prime := Fact.out
  have hv : v.Prime := Fact.out
  refine ⟨cyclotomicCharacter.continuous l ℚ_[v] (Om v), fun hvl => ?_, cf_chi l (PP l)⟩
  have hnd : ∀ m : ℕ, ¬ v ∣ l ^ m := fun m h =>
    hvl ((Nat.prime_dvd_prime_iff_eq hv hl).1 (hv.dvd_of_dvd_pow h))
  refine ⟨fun g hg => ?_, fun σ hσ => ?_⟩
  · apply Units.ext
    refine PadicInt.ext_of_toZModPow.1 fun m => ?_
    rw [cf_toZModPow v l g m 1 (fun ζ hζ => ?_)]
    · simp
    · rw [pow_one]
      have hm : ζ ∈ MaximalUnramifiedExtension v :=
        IntermediateField.subset_adjoin _ _ ⟨l ^ m, pow_pos hl.pos m, hnd m, hζ.pow_eq_one⟩
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hm
  · refine PadicInt.ext_of_toZModPow.1 fun m => ?_
    rw [cf_toZModPow v l σ m v (fun ζ hζ => ?_)]
    · simp
    · have h1 := cf_norm_root (pow_ne_zero m hl.ne_zero) hζ.pow_eq_one
      refine cf_root_eq (hnd m) ?_ ?_ (hσ ζ h1.le)
      · rw [← map_pow, hζ.pow_eq_one, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fDescAvg
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem z1fDesc_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

theorem UpperTheory.V.Loc.z1fDesc :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V) (H : Subgroup G) [H.Normal] [H.FiniteIndex], ∀ c ∈ Z1 ρ, (c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ ↔ (fun h : H => c h) ∈ UpperTheory.V.Loc.finiteCocycles (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)) := by
  intro l _ G _ _ _ φ A _ _ V _ _ _ _ _ _ _ _ _ ρ H _ _ c hc
  constructor
  · rintro ⟨-, x, hx⟩
    exact ⟨⟨hc.1.comp continuous_subtype_val, fun g h => hc.2 g h⟩, x, fun h => hx h⟩
  · rintro ⟨-, x, hx⟩
    refine ⟨hc, ?_⟩
    refine z1fDesc_avg (k := ℚ_[l]) (fun g => (actC φ ρ g).restrictScalars ℚ_[l]) ?_
      (fun g => c g ⊗ₜ[ℚ_[l]] (1 : Bcr l)) ?_ H x (fun h hh => hx ⟨h, hh⟩)
    · intro g h w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [actC]
      | add u v hu hv => simp only [map_add (f := _), hu, hv]
    · intro g h
      simp [actC, hc.2 g h, add_tmul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem fd_pow_root {K : Type*} [Field K] {m n : ℕ} {y : K} (h : y ^ m = 1) :
    (y ^ n) ^ m = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

private theorem fd_level {v : ℕ} [Fact v.Prime] {x : Om v} (hx : x ∈ MaximalUnramifiedExtension v) :
    ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g x = h x := by
  have hv : v.Prime := Fact.out
  have key : ∀ {a b : Om v},
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g a = h a) →
      (∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) → g b = h b) →
      ∃ m : ℕ, ¬ v ∣ m ∧ ∀ g h : GQ v, (∀ y : Om v, y ^ m = 1 → g y = h y) →
        g a = h a ∧ g b = h b := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, fun h => (hv.dvd_mul.mp h).elim hm hn, fun g h hgh => ⟨ha g h fun y hy => ?_,
      hb g h fun y hy => ?_⟩⟩
    · exact hgh y (by rw [pow_mul, hy, one_pow])
    · exact hgh y (by rw [mul_comm, pow_mul, hy, one_pow])
  unfold MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, -, hm, hx⟩ := hx
    exact ⟨m, hm, fun g h hgh => hgh x hx⟩
  | algebraMap x =>
    exact ⟨1, hv.not_dvd_one, fun g h _ => by rw [AlgEquiv.commutes, AlgEquiv.commutes]⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_add (f := _), map_add (f := _), (h g k hgk).1, (h g k hgk).2]⟩
  | inv x _ hx =>
    obtain ⟨m, hm, h⟩ := hx
    exact ⟨m, hm, fun g k hgk => by rw [map_inv₀, map_inv₀, h g k hgk]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm, h⟩ := key hx hy
    exact ⟨m, hm, fun g k hgk => by rw [map_mul, map_mul, (h g k hgk).1, (h g k hgk).2]⟩

private theorem fd_frob {v : ℕ} [Fact v.Prime] {σ : GQ v}
    (hσ : UpperTheory.V.Loc.IsFrob (v := v) σ) {m : ℕ} (hm : ¬ v ∣ m)
    (j : ℕ) (y : Om v) (hy : y ^ m = 1) : (σ ^ j) y = y ^ v ^ j := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have h1 : σ y = y ^ v := by
    have hn : ‖y‖ ^ m = 1 := by rw [← norm_pow, hy, norm_one]
    have hn' := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp hn
    exact KStar.IdealValuations.norm_aut_and_roots.2 m _ _ hm (by rw [← map_pow, hy, map_one])
      (fd_pow_root hy) (hσ y hn'.le)
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1, ← pow_mul, pow_succ']

theorem UpperTheory.V.Loc.frobDense :
    ∀ {v : ℕ} [Fact v.Prime] (σ : GQ v), UpperTheory.V.Loc.IsFrob (v := v) σ →
      (Iq v ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤ := by
  intro v _ σ hσ
  let H : ClosedSubgroup (GQ v) :=
    ⟨(Iq v ⊔ Subgroup.zpowers σ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
  have hH := InfiniteGalois.fixingSubgroup_fixedField H
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ (H : Subgroup (GQ v)) := Subgroup.le_topologicalClosure _
  refine eq_top_iff.mpr fun g _ => ?_
  change g ∈ (H : Subgroup (GQ v))
  rw [← hH, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hxK : x ∈ MaximalUnramifiedExtension v := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension v), IntermediateField.mem_fixedField_iff]
    exact fun f hf => hx f (hle (Subgroup.mem_sup_left hf))
  obtain ⟨m, hm, h⟩ := fd_level hxK
  obtain ⟨j, hj⟩ := KStar.IdealValuations.exists_pow_of_aut g hm
  rw [h g (σ ^ j) fun y hy => by rw [hj y hy, fd_frob hσ hm j y hy]]
  exact hx _ (hle (Subgroup.mem_sup_right (Subgroup.npow_mem_zpowers σ j)))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemIK
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.memIK :
    ∀ {v : ℕ} [Fact v.Prime] (K : FinExt v) (g : ↥(GK K)), g ∈ IK K ↔ (g : GQ v) ∈ Iq v := by
  intro l _ K g
  refine ⟨fun hg => (Subgroup.closure_le ((MaximalUnramifiedExtension l).fixingSubgroup.comap (GK K).subtype)).2 (fun σ hσ => ?_) hg,
    fun hg => Subgroup.subset_closure (GlobalTheory.FrobGen.norm_sub_lt hg)⟩
  change (σ : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
  rintro x ⟨n, hn, hln, hx⟩
  have key : (σ : GQ l) x = x := GlobalTheory.Pst.eq_of_pow_eq_one_of_norm_sub_lt hln (by rw [← map_pow, hx, map_one]) hx
    (hσ x (GlobalTheory.Pst.norm_eq_one_of_pow_eq_one hn hx).le)
  rintro ⟨_, n, rfl⟩
  exact MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy _ (σ : GQ l) from key) n
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrField
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem finrank_key {Q E M V : Type} [Field Q] [Field E] [Algebra Q E] [FiniteDimensional Q E]
    [AddCommGroup M] [Module E M] [Module Q M] [IsScalarTower Q E M]
    [AddCommGroup V] [Module E V] [Module Q V] [IsScalarTower Q E V]
    (D : Submodule E M) (D' : Submodule Q M) (h : ∀ x, x ∈ D' ↔ x ∈ D) (n : ℕ) :
    finrank Q ↥D' = n * finrank Q V ↔ finrank E ↥D = n * finrank E V := by
  have e : D' = D.restrictScalars Q := by
    ext x
    exact h x
  have h1 : finrank Q ↥D' = finrank Q E * finrank E ↥D := by
    rw [Module.finrank_mul_finrank, e]
    rfl
  have h2 : finrank Q V = finrank Q E * finrank E V := (Module.finrank_mul_finrank Q E V).symm
  have hp : 0 < finrank Q E := Module.finrank_pos
  rw [h1, h2, mul_left_comm]
  exact Nat.mul_right_inj hp.ne'

theorem UpperTheory.V.Loc.isCrField :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E ↥(GK K) V), (Crys K ρ ↔ IsCrys ((PP l).PD K) ρ) ∧ (DeRham K ρ ↔ IsDR ((PP l).PD K) ρ) ∧ UpperTheory.V.Loc.finiteCocycles (GK K).subtype ρ = Formalism.WeaklyAdmissibleFiltrations.finiteCocycles ((PP l).PD K) ρ := by
  intro l _ K E _ _ _ V _ _ _ _ _ _ _ _ _ ρ
  have hB : ∀ g x, actVB ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVB ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hD : ∀ g x, actVdR ((PP l).PD K) (resCoef ℚ_[l] ρ) g x = actVdR ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hC : ∀ g x, actC (GK K).subtype ρ g x = actVB ((PP l).PD K) ρ g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ g v ⊗ₜ[ℚ_[l]] (PP l).actQ (g : GQ l) b = ρ g v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB g b
      rw [(PP l).PD_actB]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨?_, ?_, ?_⟩
  · refine finrank_key (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.Dcris ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _
    simp only [Formalism.WeaklyAdmissibleFiltrations.Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hB]
  · refine finrank_key (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) ρ) (Formalism.WeaklyAdmissibleFiltrations.DdR ((PP l).PD K) (resCoef ℚ_[l] ρ)) (fun x => ?_) _
    simp only [Formalism.WeaklyAdmissibleFiltrations.DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hD]
  · ext c
    change (c ∈ ReciprocityTheory.Gal.Z1 ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actC (GK K).subtype ρ g x - x) ↔
      (c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[ℚ_[l]] Bcr l, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bcr l) = actVB ((PP l).PD K) ρ g x - x)
    simp only [hC]
    exact Iff.rfl
end
