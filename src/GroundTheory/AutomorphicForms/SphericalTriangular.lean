module

public import GroundTheory.AutomorphicForms.CompactFormulaCountable
public import GroundTheory.AutomorphicForms.InductionParabolic

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.SphericalSatake
section -- merged from GroundTheory.AutomorphicForms.SphericalPrincipal
noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra
open scoped ValuativeRel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def IsUnramified (χ : levi F n (id : Fin n → Fin n) →* ℂ) : Prop :=
  ∀ t : levi F n (id : Fin n → Fin n), (t : GL (Fin n) F) ∈ integralGL F n → χ t = 1

def charRep (χ : levi F n (id : Fin n → Fin n) →* ℂ) :
    Representation ℂ (levi F n (id : Fin n → Fin n)) ℂ :=
  twist χ (Representation.trivial ℂ _ ℂ)

@[simp]
theorem charRep_apply (χ : levi F n (id : Fin n → Fin n) →* ℂ) (t : levi F n (id : Fin n → Fin n))
    (z : ℂ) : charRep χ t z = χ t * z := by
  simp [charRep]


variable (F n) in
abbrev principalSeriesSpace (χ : levi F n (id : Fin n → Fin n) →* ℂ) :
    Submodule ℂ (GL (Fin n) F → ℂ) :=
  parabolicIndSpace F n (id : Fin n → Fin n) (charRep χ)


variable (F n) in
abbrev principalSeries (χ : levi F n (id : Fin n → Fin n) →* ℂ) :
    Representation ℂ (GL (Fin n) F) (principalSeriesSpace F n χ) :=
  parabolicInd F n (id : Fin n → Fin n) (charRep χ)

def borelChar (χ : levi F n (id : Fin n → Fin n) →* ℂ) : blockUpper F n (id : Fin n → Fin n) →* ℂ where
  toFun p := sqrtModular F n id p * χ (leviProj F n id p)
  map_one' := by simp
  map_mul' p q := by
    simp only [map_mul]
    ring

theorem borelChar_apply (χ : levi F n (id : Fin n → Fin n) →* ℂ)
    (p : blockUpper F n (id : Fin n → Fin n)) :
    borelChar χ p = sqrtModular F n id p * χ (leviProj F n id p) := rfl

theorem mem_principalSeriesSpace {χ : levi F n (id : Fin n → Fin n) →* ℂ} {f : GL (Fin n) F → ℂ} :
    f ∈ principalSeriesSpace F n χ ↔
      (∀ p : blockUpper F n (id : Fin n → Fin n), ∀ g, f (p * g) = borelChar χ p * f g) ∧
        ∃ K : Subgroup (GL (Fin n) F), IsOpen (K : Set (GL (Fin n) F)) ∧
          ∀ k ∈ K, ∀ g, f (g * k) = f g := by
  rw [mem_parabolicIndSpace]
  simp only [charRep_apply, smul_eq_mul, borelChar_apply, mul_assoc]

theorem leviProj_mem_integralGL {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) :
    ((leviProj F n id p : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) ∈ integralGL F n := by
  rw [mem_integralGL_iff] at hp ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [leviProj_apply]
    split_ifs
    · exact hp.1 i j
    · exact (𝒪[F]).zero_mem
  · have : ((leviProj F n id p : levi F n (id : Fin n → Fin n)) : GL (Fin n) F)⁻¹ =
        ((leviProj F n id p⁻¹ : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) := by
      rw [map_inv, Subgroup.coe_inv]
    rw [this, leviProj_apply]
    split_ifs
    · exact hp.2 i j
    · exact (𝒪[F]).zero_mem

variable {χ : levi F n (id : Fin n → Fin n) →* ℂ}

theorem borelChar_eq_one (hχ : IsUnramified χ) {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : borelChar χ p = 1 := by
  rw [borelChar_apply, hχ _ (leviProj_mem_integralGL hp), mul_one]
  show ((NNReal.sqrt (Measure.modularCharacter p) : ℝ) : ℂ) = 1
  rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
  simp

theorem borelChar_eq_of_mul_eq (hχ : IsUnramified χ) {b b' : blockUpper F n (id : Fin n → Fin n)}
    {k k' : GL (Fin n) F} (hk : k ∈ integralGL F n) (hk' : k' ∈ integralGL F n)
    (h : (b : GL (Fin n) F) * k = b' * k') : borelChar χ b = borelChar χ b' := by
  have hm : ((b'⁻¹ * b : blockUpper F n (id : Fin n → Fin n)) : GL (Fin n) F) ∈ integralGL F n := by
    have : ((b'⁻¹ * b : blockUpper F n (id : Fin n → Fin n)) : GL (Fin n) F) = k' * k⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h,
        mul_inv_cancel_right]
    rw [this]
    exact mul_mem hk' (inv_mem hk)
  have := borelChar_eq_one hχ hm
  rw [map_mul, map_inv] at this
  have hne : borelChar χ b' ≠ 0 := by
    intro h0
    have h1 : borelChar χ (b'⁻¹ * b') = 1 := by rw [inv_mul_cancel, map_one]
    rw [map_mul, h0, mul_zero] at h1
    exact zero_ne_one h1
  calc borelChar χ b = borelChar χ b' * ((borelChar χ b')⁻¹ * borelChar χ b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = borelChar χ b' := by rw [this, mul_one]

theorem exists_borel_mul (g : GL (Fin n) F) :
    ∃ p : blockUpper F n (id : Fin n → Fin n), ∃ k ∈ integralGL F n, g = (p : GL (Fin n) F) * k := by
  obtain ⟨p, hp, k, hk, h⟩ := exists_blockUpper_mul_integralGL F n (β := (id : Fin n → Fin n))
    monotone_id g
  exact ⟨⟨p, hp⟩, k, hk, h⟩


variable (χ) in
def sphericalFun (g : GL (Fin n) F) : ℂ :=
  borelChar χ (exists_borel_mul g).choose

theorem sphericalFun_mul (hχ : IsUnramified χ) (b : blockUpper F n (id : Fin n → Fin n))
    {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    sphericalFun χ ((b : GL (Fin n) F) * k) = borelChar χ b := by
  obtain ⟨k', hk', h⟩ := (exists_borel_mul ((b : GL (Fin n) F) * k)).choose_spec
  exact borelChar_eq_of_mul_eq hχ hk' hk h.symm

theorem sphericalFun_borel (hχ : IsUnramified χ) (b : blockUpper F n (id : Fin n → Fin n)) :
    sphericalFun χ (b : GL (Fin n) F) = borelChar χ b := by
  simpa using sphericalFun_mul hχ b (integralGL F n).one_mem

theorem sphericalFun_one (hχ : IsUnramified χ) : sphericalFun χ 1 = 1 := by
  simpa using sphericalFun_borel hχ 1

theorem sphericalFun_mem (hχ : IsUnramified χ) : sphericalFun χ ∈ principalSeriesSpace F n χ := by
  rw [mem_principalSeriesSpace]
  refine ⟨fun p g => ?_, integralGL F n, isOpen_integralGL F n, fun k hk g => ?_⟩
  · obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
    rw [← mul_assoc, ← Subgroup.coe_mul, sphericalFun_mul hχ _ hk, sphericalFun_mul hχ _ hk,
      map_mul]
  · obtain ⟨b, k', hk', rfl⟩ := exists_borel_mul g
    rw [mul_assoc, sphericalFun_mul hχ _ (mul_mem hk' hk), sphericalFun_mul hχ _ hk']

def sphericalVector (hχ : IsUnramified χ) : principalSeriesSpace F n χ :=
  ⟨sphericalFun χ, sphericalFun_mem hχ⟩

@[simp]
theorem coe_sphericalVector (hχ : IsUnramified χ) :
    ((sphericalVector hχ : principalSeriesSpace F n χ) : GL (Fin n) F → ℂ) = sphericalFun χ := rfl

theorem sphericalVector_mem_fixedVectors (hχ : IsUnramified χ) :
    sphericalVector hχ ∈ fixedVectors (principalSeries F n χ) (integralGL F n) := by
  intro k hk
  refine Subtype.ext (funext fun g => ?_)
  rw [coe_indRep_apply]
  obtain ⟨b, k', hk', rfl⟩ := exists_borel_mul g
  simp only [coe_sphericalVector]
  rw [mul_assoc, sphericalFun_mul hχ _ (mul_mem hk' hk), sphericalFun_mul hχ _ hk']

theorem sphericalVector_ne_zero (hχ : IsUnramified χ) : sphericalVector hχ ≠ 0 := by
  intro h
  have := congrFun (congrArg Subtype.val h) 1
  simp only [coe_sphericalVector, Submodule.coe_zero, Pi.zero_apply] at this
  rw [sphericalFun_one hχ] at this
  exact one_ne_zero this

theorem eq_smul_sphericalVector (hχ : IsUnramified χ) {f : principalSeriesSpace F n χ}
    (hf : f ∈ fixedVectors (principalSeries F n χ) (integralGL F n)) :
    f = (f : GL (Fin n) F → ℂ) 1 • sphericalVector hχ := by
  have hmem := (mem_principalSeriesSpace.1 f.2).1
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
  have hfk : (f : GL (Fin n) F → ℂ) ((b : GL (Fin n) F) * k) = (f : GL (Fin n) F → ℂ) b := by
    have := congrFun (congrArg Subtype.val (hf k hk)) (b : GL (Fin n) F)
    rw [coe_indRep_apply] at this
    exact this
  rw [Submodule.coe_smul, Pi.smul_apply, coe_sphericalVector, sphericalFun_mul hχ _ hk, hfk,
    smul_eq_mul]
  have := hmem b 1
  rw [mul_one] at this
  rw [this, mul_comm]

theorem fixedVectors_eq_span (hχ : IsUnramified χ) :
    fixedVectors (principalSeries F n χ) (integralGL F n) = ℂ ∙ sphericalVector hχ := by
  refine le_antisymm (fun f hf => ?_) ?_
  · rw [Submodule.mem_span_singleton]
    exact ⟨_, (eq_smul_sphericalVector hχ hf).symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact sphericalVector_mem_fixedVectors hχ

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]


variable (μ) in
abbrev SphericalHecke : Type _ :=
  HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n) (isOpen_integralGL F n)


variable (μ χ) in
def sphericalEigen (h : SphericalHecke μ (F := F) (n := n)) : ℂ :=
  ∫ g, (h : HeckeAlgebra μ) g * sphericalFun χ g ∂μ

theorem heckeAct_sphericalVector (hχ : IsUnramified χ) (h : SphericalHecke μ (F := F) (n := n)) :
    heckeAct μ (principalSeries F n χ) (h : HeckeAlgebra μ) (sphericalVector hχ) =
      sphericalEigen χ μ h • sphericalVector hχ := by
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n)) (charRep χ)
  have hmem : heckeAct μ (principalSeries F n χ) (h : HeckeAlgebra μ) (sphericalVector hχ) ∈
      fixedVectors (principalSeries F n χ) (integralGL F n) :=
    heckeAct_mem_fixedVectors (h : HeckeAlgebra μ).mem
      (fun _ hk x => HeckeAlgebraLevel.apply_mul_left _ _ h hk x) (hs _)
  rw [eq_smul_sphericalVector hχ hmem]
  congr 1
  have := dual_heckeAct μ (h : HeckeAlgebra μ).mem (hs (sphericalVector hχ))
    (evalOne (blockUpper F n (id : Fin n → Fin n)) (inflateTwist F n id (charRep χ)))
  simp only [evalOne_apply, coe_indRep_apply, one_mul, coe_sphericalVector] at this
  exact this


variable (μ) in
def sphericalCharacter (hχ : IsUnramified χ) : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] ℂ :=
  have hs := isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n)) (charRep χ)
  have hne := sphericalVector_ne_zero hχ
  have key : ∀ a b : ℂ, a • sphericalVector hχ = b • sphericalVector hχ → a = b :=
    fun a b hab => smul_left_injective ℂ hne hab
  { toFun := sphericalEigen χ μ
    map_one' := key _ _ (by
      rw [← heckeAct_sphericalVector, one_smul, HeckeAlgebraLevel.val_one]
      exact heckeAct_idem_of_mem _ _ (sphericalVector_mem_fixedVectors hχ))
    map_mul' := fun a b => key _ _ (by
      rw [← heckeAct_sphericalVector, HeckeAlgebraLevel.val_mul, heckeAct_mul _ _ (hs _),
        heckeAct_sphericalVector, heckeAct_smul_right (a : HeckeAlgebra μ).mem _ (hs _),
        heckeAct_sphericalVector, smul_smul, mul_comm])
    map_zero' := key _ _ (by
      rw [← heckeAct_sphericalVector, HeckeAlgebraLevel.val_zero, coe_zero, zero_smul]
      exact heckeAct_zero_left (hs _))
    map_add' := fun a b => key _ _ (by
      rw [← heckeAct_sphericalVector, HeckeAlgebraLevel.val_add, coe_add,
        heckeAct_add_left (a : HeckeAlgebra μ).mem (b : HeckeAlgebra μ).mem (hs _),
        heckeAct_sphericalVector, heckeAct_sphericalVector, add_smul])
    commutes' := fun c => key _ _ (by
      rw [← heckeAct_sphericalVector, Algebra.algebraMap_eq_smul_one, HeckeAlgebraLevel.val_smul,
        HeckeAlgebra.coe_smul, heckeAct_smul_left c (HeckeAlgebra.mem _) (hs _), HeckeAlgebraLevel.val_one,
        heckeAct_idem_of_mem _ _ (sphericalVector_mem_fixedVectors hχ)]
      rfl) }

theorem sphericalCharacter_apply (hχ : IsUnramified χ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalCharacter μ hχ h = sphericalEigen χ μ h := rfl

end Spherical

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped ValuativeRel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem torusPow_add (l l' : Fin n → ℤ) :
    torusPow F n (l + l') = torusPow F n l * torusPow F n l' := by
  rw [torusPow, torusPow, torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem torusPow_zero : torusPow F n 0 = 1 := by
  rw [torusPow, ← map_one (diagGL F n)]
  congr 1
  funext i
  simp

theorem diagGL_mul_comm (a b : Fin n → Fˣ) : diagGL F n a * diagGL F n b = diagGL F n b * diagGL F n a := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem iwasawaExponent_one : iwasawaExponent F n (1 : GL (Fin n) F) = 0 := by
  simpa [torusPow_zero] using
    iwasawaExponent_eq F n (unipotent F n).one_mem (integralGL F n).one_mem (l := (0 : Fin n → ℤ))

theorem exists_diagGL_eq_torusPow_mul (d : Fin n → Fˣ) :
    ∃ l : Fin n → ℤ, ∃ e : Fin n → (𝒪[F])ˣ,
      diagGL F n d = torusPow F n l * diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i) := by
  choose l e he using fun i => exists_zpow_mul_unit F (d i).ne_zero
  refine ⟨l, e, ?_⟩
  rw [torusPow, ← map_mul]
  congr 1
  funext i
  ext
  simp [he i, Units.val_zpow_eq_zpow_val, Units.coe_map]

def diagUnits {b : GL (Fin n) F} (hb : b ∈ Iwasawa.borel F n) : Fin n → Fˣ :=
  fun i => Units.mk0 (b i i) (apply_self_ne_zero_of_mem_borel F n hb i)

theorem mul_inv_diagUnits_mem_unipotent {b : GL (Fin n) F} (hb : b ∈ Iwasawa.borel F n) :
    b * (diagGL F n (diagUnits hb))⁻¹ ∈ unipotent F n := by
  have hDinv : (diagGL F n (diagUnits hb))⁻¹ ∈ Iwasawa.borel F n :=
    (Iwasawa.borel F n).inv_mem (diagGL_mem_borel F n _)
  refine ⟨(Iwasawa.borel F n).mul_mem hb hDinv, fun i => ?_⟩
  rw [mul_apply_self_of_mem_borel F n hb hDinv, ← map_inv, coe_diagGL, diagonal_apply_eq]
  simp [diagUnits, apply_self_ne_zero_of_mem_borel F n hb i]

theorem iwasawaExponent_mul_of_mem_borel {b : GL (Fin n) F} (hb : b ∈ Iwasawa.borel F n)
    (g : GL (Fin n) F) :
    iwasawaExponent F n (b * g) = iwasawaExponent F n b + iwasawaExponent F n g := by
  obtain ⟨l, e, hde⟩ := exists_diagGL_eq_torusPow_mul (diagUnits hb)
  set D := diagGL F n (diagUnits hb)
  set E : GL (Fin n) F := diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i)
  have hE : E ∈ integralGL F n := diagGL_map_mem_integralGL F n e
  have hu := mul_inv_diagUnits_mem_unipotent hb
  have key : ∀ g : GL (Fin n) F, iwasawaExponent F n (b * g) = l + iwasawaExponent F n g := by
    intro g
    obtain ⟨u', hu', k', hk', hg⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
    set lg := iwasawaExponent F n g with hlg
    have hcomm : E * torusPow F n lg = torusPow F n lg * E :=
      diagGL_mul_comm _ _
    have hD : D⁻¹ * torusPow F n l = E⁻¹ := by
      rw [hde, _root_.mul_inv_rev, inv_mul_cancel_right]
    have : b * g = (b * D⁻¹ * (D * u' * D⁻¹)) * torusPow F n (l + lg) * (E * k') := by
      rw [torusPow_add]
      conv_lhs => rw [hg]
      calc b * (u' * torusPow F n lg * k')
          = b * u' * (E⁻¹ * (E * torusPow F n lg)) * k' := by group
        _ = b * u' * (E⁻¹ * (torusPow F n lg * E)) * k' := by rw [hcomm]
        _ = b * u' * ((D⁻¹ * torusPow F n l) * (torusPow F n lg * E)) * k' := by
            rw [hD]
        _ = _ := by group
    rw [this]
    refine iwasawaExponent_eq F n ((unipotent F n).mul_mem hu ?_) ((integralGL F n).mul_mem hE hk')
    exact diagGL_mul_mul_inv_mem_unipotent F n hu' _
  have hb1 := key 1
  rw [mul_one, iwasawaExponent_one, add_zero] at hb1
  rw [key, hb1]

def unramifiedChar (w : Fin n → ℂˣ) : levi F n (id : Fin n → Fin n) →* ℂ where
  toFun t := monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t)
  map_one' := by simp [iwasawaExponent_one]
  map_mul' t t' := by
    have ht : (t : GL (Fin n) F) ∈ Iwasawa.borel F n := levi_le_blockUpper t.2
    simp only [Subgroup.coe_mul, iwasawaExponent_mul_of_mem_borel ht, monomialChar_add, map_mul]
    ring

theorem invSqrtModular_eq_one {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : invSqrtModular F n id p = 1 := by
  have h := sqrtModular_mul_invSqrtModular p
  have hs : sqrtModular F n id p = 1 := by
    show ((NNReal.sqrt (Measure.modularCharacter p) : ℝ) : ℂ) = 1
    rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
    simp
  rwa [hs, one_mul] at h

theorem isUnramified_unramifiedChar (w : Fin n → ℂˣ) : IsUnramified (unramifiedChar (F := F) w) := by
  intro t ht
  show monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t) = 1
  have h0 : iwasawaExponent F n (t : GL (Fin n) F) = 0 := by
    simpa [iwasawaExponent_one] using iwasawaExponent_mul_of_mem_integralGL F n 1 ht
  rw [h0, monomialChar_zero, invSqrtModular_eq_one ht, one_mul]

theorem iwasawaExponent_leviProj (b : blockUpper F n (id : Fin n → Fin n)) :
    iwasawaExponent F n ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      iwasawaExponent F n (b : GL (Fin n) F) := by
  have hb : (b : GL (Fin n) F) ∈ Iwasawa.borel F n := b.2
  have hD : ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      diagGL F n (diagUnits hb) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_diagGL, leviProj_apply]
    by_cases hij : i = j
    · subst hij
      simp [diagUnits]
    · simp [hij, diagonal_apply_ne _ hij]
  rw [hD]
  conv_rhs => rw [show (b : GL (Fin n) F) = (b * (diagGL F n (diagUnits hb))⁻¹) *
    diagGL F n (diagUnits hb) by group]
  rw [iwasawaExponent_mul_of_mem_unipotent F n (mul_inv_diagUnits_mem_unipotent hb)]

theorem borelChar_unramifiedChar (w : Fin n → ℂˣ) (b : blockUpper F n (id : Fin n → Fin n)) :
    borelChar (unramifiedChar w) b = monomialChar (iwasawaExponent F n (b : GL (Fin n) F)) w := by
  rw [borelChar_apply]
  change sqrtModular F n id b * (monomialChar (iwasawaExponent F n
    ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F)) w *
      invSqrtModular F n id (leviIncl (leviProj F n id b))) = _
  rw [iwasawaExponent_leviProj]
  have : invSqrtModular F n id (leviIncl (leviProj F n id b)) = invSqrtModular F n id b := by
    show (sqrtModular F n id (leviIncl (leviProj F n id b)))⁻¹ = (sqrtModular F n id b)⁻¹
    rw [sqrtModular_leviProj]
  rw [this, mul_left_comm, sqrtModular_mul_invSqrtModular, mul_one]

theorem sphericalFun_unramifiedChar (w : Fin n → ℂˣ) (g : GL (Fin n) F) :
    sphericalFun (unramifiedChar w) g = monomialChar (iwasawaExponent F n g) w := by
  obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
  rw [sphericalFun_mul (isUnramified_unramifiedChar w) b hk, borelChar_unramifiedChar,
    iwasawaExponent_mul_of_mem_integralGL F n _ hk]


variable (F n) in
def integralOpen : OpenSubgroup (GL (Fin n) F) := ⟨integralGL F n, isOpen_integralGL F n⟩

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

def cosetSupport (h : SphericalHecke μ (F := F) (n := n)) :
    Finset (GL (Fin n) F ⧸ integralGL F n) :=
  (finite_image_mk_tsupport (integralOpen F n) (h : HeckeAlgebra μ).mem.2).toFinset

theorem apply_out_eq_zero {h : SphericalHecke μ (F := F) (n := n)}
    {x : GL (Fin n) F ⧸ integralGL F n} (hx : x ∉ cosetSupport h) :
    (h : HeckeAlgebra μ) x.out = 0 := by
  by_contra h0
  exact hx ((Set.Finite.mem_toFinset _).mpr ⟨x.out, subset_tsupport _ h0, QuotientGroup.out_eq' x⟩)

theorem sphericalEigen_unramifiedChar (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalEigen (unramifiedChar w) μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h, (h : HeckeAlgebra μ) x.out *
        monomialChar (iwasawaExponent F n x.out) w := by
  have hf : HasCompactSupport fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g :=
    (h : HeckeAlgebra μ).mem.2.mul_right
  have hK : ∀ g, ∀ k ∈ integralOpen F n,
      (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) (g * k) =
        (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) g := by
    intro g k hk
    simp only [sphericalFun_unramifiedChar, iwasawaExponent_mul_of_mem_integralGL F n g hk]
    rw [(HeckeAlgebraLevel.val_mem _ _ h k hk g).2]
  rw [sphericalEigen, integral_eq_smul_finsum_coset μ (integralOpen F n)
    (isCompact_integralGL F n) hf hK, Complex.real_smul]
  congr 1
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n,
    (h : HeckeAlgebra μ) x.out * sphericalFun (unramifiedChar w) x.out) = _
  rw [finsum_eq_sum_of_support_subset (s := cosetSupport h)]
  · simp only [sphericalFun_unramifiedChar]
  · intro x hx
    by_contra hxs
    exact hx (by simp [apply_out_eq_zero hxs])


variable (μ) in
def satake (h : SphericalHecke μ (F := F) (n := n)) : LaurentRing n :=
  (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
    ∑ x ∈ cosetSupport h, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out)

theorem satake_eq_sum (h : SphericalHecke μ (F := F) (n := n))
    (S : Finset (GL (Fin n) F ⧸ integralGL F n)) (hS : ∀ x ∉ S, (h : HeckeAlgebra μ) x.out = 0) :
    satake μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ x ∈ S, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out) := by
  classical
  rw [satake]
  congr 1
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun x _ hx => by
      rw [apply_out_eq_zero hx, AddMonoidAlgebra.single_zero]]
  exact (Finset.sum_subset (Finset.subset_union_right (s₁ := cosetSupport h)) fun x _ hx => by
      rw [hS x hx, AddMonoidAlgebra.single_zero]).symm

theorem evalAt_satake (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt w (satake μ h) = sphericalCharacter μ (isUnramified_unramifiedChar w) h := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sphericalCharacter_apply, satake, map_smul, map_sum, sphericalEigen_unramifiedChar,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [evalAt_single]


variable (μ) in
def satakeHom : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] LaurentRing n where
  toFun := satake μ
  map_one' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_one]
  map_mul' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_mul]
  map_zero' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_zero]
  map_add' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_add (f := _)]
  commutes' c := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, AlgHom.commutes]

theorem satakeHom_apply (h : SphericalHecke μ (F := F) (n := n)) : satakeHom μ h = satake μ h := rfl

theorem evalAt_comp_satakeHom (w : Fin n → ℂˣ) :
    (evalAt w).comp (satakeHom μ) = sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) :=
  AlgHom.ext fun h => evalAt_satake w h

end Spherical

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}


variable (F) in
def Bdd (t : ℤ) (x : F) : Prop := valuation F x ≤ valuation F (uniformizer F : F) ^ t

theorem valuation_uniformizer_pos : 0 < valuation F (uniformizer F : F) :=
  zero_lt_iff.2 (valuation_uniformizer_ne_zero F)

theorem bdd_zero (t : ℤ) : Bdd F t 0 := by
  simp [Bdd]

theorem Bdd.add {t : ℤ} {x y : F} (hx : Bdd F t x) (hy : Bdd F t y) : Bdd F t (x + y) :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem Bdd.neg {t : ℤ} {x : F} (hx : Bdd F t x) : Bdd F t (-x) := by
  rwa [Bdd, Valuation.map_neg]

theorem bdd_sum {ι : Type*} (s : Finset ι) {t : ℤ} {f : ι → F} (h : ∀ i ∈ s, Bdd F t (f i)) :
    Bdd F t (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bdd_zero t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Bdd.mul {s t : ℤ} {x y : F} (hx : Bdd F s x) (hy : Bdd F t y) : Bdd F (s + t) (x * y) := by
  rw [Bdd, map_mul, zpow_add₀ (valuation_uniformizer_ne_zero F)]
  exact mul_le_mul' hx hy

theorem bdd_prod {ι : Type*} (s : Finset ι) {t : ι → ℤ} {f : ι → F} (h : ∀ i ∈ s, Bdd F (t i) (f i)) :
    Bdd F (∑ i ∈ s, t i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bdd]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem bdd_of_mem {x : F} (hx : x ∈ 𝒪[F]) : Bdd F 0 x := by
  rw [Bdd, zpow_zero]
  exact hx

theorem Bdd.mono {s t : ℤ} {x : F} (hx : Bdd F t x) (h : s ≤ t) : Bdd F s x :=
  hx.trans (zpow_le_zpow_right_of_le_one₀ valuation_uniformizer_pos
    (valuation_uniformizer_lt_one F).le h)

theorem bdd_zpow (t : ℤ) : Bdd F t ((uniformizer F : F) ^ t) := by
  rw [Bdd, map_zpow₀]

theorem le_of_bdd_zpow {s t : ℤ} (h : Bdd F t ((uniformizer F : F) ^ s)) : t ≤ s := by
  rwa [Bdd, map_zpow₀, zpow_le_zpow_iff_right_of_lt_one₀ valuation_uniformizer_pos
    (valuation_uniformizer_lt_one F)] at h

theorem mem_of_bdd {x : F} (h : Bdd F 0 x) : x ∈ 𝒪[F] := by
  rw [Bdd, zpow_zero] at h
  exact h

theorem det_mem_of_forall_mem {m : ℕ} {M : Matrix (Fin m) (Fin m) F} (hM : ∀ i j, M i j ∈ 𝒪[F]) :
    M.det ∈ 𝒪[F] := by
  let N : Matrix (Fin m) (Fin m) 𝒪[F] := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have : M = N.map (𝒪[F]).subtype := by
    ext i j
    rfl
  have h := RingHom.map_det (𝒪[F]).subtype N
  rw [RingHom.mapMatrix_apply] at h
  rw [this, ← h]
  exact (N.det).2

def tailEmb {m : ℕ} (hm : m ≤ n) (j : Fin m) : Fin n := ⟨n - m + j, by omega⟩

theorem tailEmb_injective {m : ℕ} (hm : m ≤ n) : Function.Injective (tailEmb hm) := by
  intro i j h
  have := congrArg Fin.val h
  simp only [tailEmb] at this
  exact Fin.ext (by omega)

def tailSum (ν : Fin n → ℤ) {m : ℕ} (hm : m ≤ n) : ℤ := ∑ j : Fin m, ν (tailEmb hm j)

theorem tailSum_le_sum {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n) (S : Finset (Fin n))
    (hS : S.card = m) : tailSum ν hm ≤ ∑ i ∈ S, ν i := by
  classical
  set T := Finset.univ.image (tailEmb hm)
  have hT : T.card = m := by
    rw [Finset.card_image_of_injective _ (tailEmb_injective hm), Finset.card_univ, Fintype.card_fin]
  have hsumT : tailSum ν hm = ∑ i ∈ T, ν i := by
    rw [Finset.sum_image fun a _ b _ h => tailEmb_injective hm h]
    rfl
  have hmemT : ∀ y ∈ T, n - m ≤ y.val := by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    simp [tailEmb]
  have hnotT : ∀ x, x ∉ T → x.val < n - m := by
    intro x hx
    by_contra h
    exact hx (Finset.mem_image.2 ⟨⟨x.val - (n - m), by omega⟩, Finset.mem_univ _,
      Fin.ext (by simp [tailEmb]; omega)⟩)
  have e1 := Finset.sum_sdiff (f := ν) (Finset.inter_subset_left (s₁ := S) (s₂ := T))
  have e2 := Finset.sum_sdiff (f := ν) (Finset.inter_subset_left (s₁ := T) (s₂ := S))
  rw [Finset.sdiff_inter_self_left] at e1 e2
  rw [Finset.inter_comm T S] at e2
  rw [hsumT, ← e1, ← e2]
  suffices key : ∑ i ∈ T \ S, ν i ≤ ∑ i ∈ S \ T, ν i by linarith
  have hcard : (T \ S).card = (S \ T).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm, hS, hT]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have : S = ∅ := Finset.card_eq_zero.1 hS
    have : T = ∅ := Finset.card_eq_zero.1 hT
    simp [*]
  · set c := ν ⟨n - m, by omega⟩
    calc ∑ i ∈ T \ S, ν i ≤ (T \ S).card • c :=
          Finset.sum_le_card_nsmul _ _ _ fun y hy =>
            hν (show (⟨n - m, by omega⟩ : Fin n) ≤ y from hmemT y (Finset.mem_sdiff.1 hy).1)
      _ = (S \ T).card • c := by rw [hcard]
      _ ≤ ∑ i ∈ S \ T, ν i :=
          Finset.card_nsmul_le_sum _ _ _ fun x hx =>
            hν (show x ≤ (⟨n - m, by omega⟩ : Fin n) from
              (Fin.le_def.2 (hnotT x (Finset.mem_sdiff.1 hx).2).le))

theorem bdd_det_submatrix {A B : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    (hB : ∀ i j, B i j ∈ 𝒪[F]) {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n)
    (r c : Fin m → Fin n) :
    Bdd F (tailSum ν hm)
      ((A * diagonal (fun i => (uniformizer F : F) ^ ν i) * B).submatrix r c).det := by
  classical
  set d : Fin n → F := fun i => (uniformizer F : F) ^ ν i
  set vec : Fin n → Fin m → F := fun l a => A (r a) l
  have hT : ((A * diagonal d * B).submatrix r c)ᵀ =
      fun j => ∑ l, (d l * B l (c j)) • vec l := by
    funext j a
    simp only [transpose_apply, submatrix_apply, Matrix.mul_apply, mul_diagonal, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, vec]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (∑ x, A (r a) x * diagonal d x l) = A (r a) l * d l by simp [diagonal_apply]]
    ring
  rw [← det_transpose, hT]
  change Bdd F _ ((detRowAlternating : (Fin m → F) [⋀^Fin m]→ₗ[F] F).toMultilinearMap
    (fun j => ∑ l, (d l * B l (c j)) • vec l))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MultilinearMap.map_sum]
  refine bdd_sum _ fun p _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  by_cases hp : Function.Injective p
  · have h1 : Bdd F (∑ j, ν (p j)) (∏ j, d (p j) * B (p j) (c j)) := by
      have := bdd_prod (Finset.univ : Finset (Fin m)) (t := fun j => ν (p j) + 0)
        (f := fun j => d (p j) * B (p j) (c j)) fun j _ => (bdd_zpow _).mul (bdd_of_mem (hB _ _))
      simpa using this
    have h2 : Bdd F 0 ((detRowAlternating : (Fin m → F) [⋀^Fin m]→ₗ[F] F).toMultilinearMap
        fun j => vec (p j)) := by
      refine bdd_of_mem ?_
      change (Matrix.of fun j a => A (r a) (p j)).det ∈ 𝒪[F]
      exact det_mem_of_forall_mem fun _ _ => hA _ _
    have h3 : tailSum ν hm ≤ ∑ j, ν (p j) := by
      have := tailSum_le_sum hν hm (Finset.univ.image p)
        (by rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin])
      rwa [Finset.sum_image fun a _ b _ h => hp h] at this
    simpa using (h1.mul h2).mono (by simpa using h3)
  · have : (detRowAlternating : (Fin m → F) [⋀^Fin m]→ₗ[F] F).toMultilinearMap
        (fun j => vec (p j)) = 0 := by
      rw [AlternatingMap.coe_multilinearMap]
      refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun hinj => hp fun i j hij => ?_
      exact hinj (by simp only [hij])
    rw [this, mul_zero]
    exact bdd_zero _

theorem prod_zpow_uniformizer {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, (uniformizer F : F) ^ f i = (uniformizer F : F) ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
      zpow_add₀ (Cartan.uniformizer_ne_zero F)]


variable (F n) in
def cartanType (g : GL (Fin n) F) : Fin n → ℤ :=
  (Cartan.existsUnique_mem_doubleCoset F n g).exists.choose

theorem cartanType_spec (g : GL (Fin n) F) :
    Cartan.IsDominant (cartanType F n g) ∧
      g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n (cartanType F n g))
        (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) :=
  (Cartan.existsUnique_mem_doubleCoset F n g).exists.choose_spec

theorem cartanType_eq {g : GL (Fin n) F} {μ : Fin n → ℤ} (hμ : Cartan.IsDominant μ)
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n μ)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    cartanType F n g = μ :=
  (Cartan.existsUnique_mem_doubleCoset F n g).unique (cartanType_spec g) ⟨hμ, hg⟩

theorem diagPow_eq_torusPow (μ : Fin n → ℤ) : Cartan.diagPow F n μ = torusPow F n μ :=
  Units.ext (by rw [Cartan.coe_diagPow, coe_torusPow])

theorem det_submatrix_tailEmb {u : GL (Fin n) F} (hu : u ∈ unipotent F n) (l : Fin n → ℤ) {m : ℕ}
    (hm : m ≤ n) :
    (((u * torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (tailEmb hm)
      (tailEmb hm)).det = (uniformizer F : F) ^ tailSum l hm := by
  have hB : u * torusPow F n l ∈ Iwasawa.borel F n := (Iwasawa.borel F n).mul_mem hu.1 (torusPow_mem_borel F n l)
  have hmono : StrictMono (tailEmb hm) := fun i j hij => by
    simp only [tailEmb, Fin.lt_def] at hij ⊢
    omega
  have hup : (((u * torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (tailEmb hm)
      (tailEmb hm)).IsUpperTriangular := fun i j hij => hB (hmono hij)
  rw [det_of_isUpperTriangular hup, tailSum, ← prod_zpow_uniformizer]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [submatrix_apply, Units.val_mul, coe_torusPow, mul_diagonal]
  have := hu.2 (tailEmb hm j)
  rw [this, one_mul]

theorem valuation_det_eq_one {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    valuation F (k : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h1 := det_mem_of_forall_mem ((mem_integralGL_iff F n).1 hk).1
  have h2 := det_mem_of_forall_mem ((mem_integralGL_iff F n).1 hk).2
  have hu : IsUnit (⟨_, h1⟩ : 𝒪[F]) := IsUnit.of_mul_eq_one (⟨_, h2⟩ : 𝒪[F]) (Subtype.ext (by
    simp only [MulMemClass.mk_mul_mk, OneMemClass.coe_one]
    rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]))
  exact (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.1 hu

theorem tailSum_le_iwasawaExponent {ν : Fin n → ℤ} (hν : Cartan.IsDominant ν) {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) {m : ℕ} (hm : m ≤ n) :
    tailSum ν hm ≤ tailSum (iwasawaExponent F n g) hm := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 hg
  obtain ⟨u, hu, k, hk, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F n
    (k₁ * Cartan.diagPow F n ν * k₂)
  set l := iwasawaExponent F n (k₁ * Cartan.diagPow F n ν * k₂)
  have heq : u * torusPow F n l = k₁ * Cartan.diagPow F n ν * (k₂ * k⁻¹) := by
    rw [← mul_assoc, he, mul_inv_cancel_right]
  have hb := bdd_det_submatrix (((mem_integralGL_iff F n).1 hk₁).1)
    (((mem_integralGL_iff F n).1 ((integralGL F n).mul_mem hk₂ ((integralGL F n).inv_mem hk))).1)
    hν hm (tailEmb hm) (tailEmb hm)
  rw [← Cartan.coe_diagPow, ← Units.val_mul, ← Units.val_mul, ← heq,
    det_submatrix_tailEmb hu] at hb
  exact le_of_bdd_zpow hb

theorem sum_iwasawaExponent {ν : Fin n → ℤ} {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    ∑ i, iwasawaExponent F n g i = ∑ i, ν i := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 hg
  obtain ⟨u, hu, k, hk, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F n
    (k₁ * Cartan.diagPow F n ν * k₂)
  set l := iwasawaExponent F n (k₁ * Cartan.diagPow F n ν * k₂)
  have hdet := congrArg (fun g : GL (Fin n) F => valuation F (g : Matrix (Fin n) (Fin n) F).det) he
  simp only [Units.val_mul, det_mul, map_mul, valuation_det_eq_one hk₁, valuation_det_eq_one hk₂,
    valuation_det_eq_one hk, one_mul, mul_one, coe_torusPow, Cartan.coe_diagPow, det_diagonal,
    prod_zpow_uniformizer, map_zpow₀] at hdet
  have hu1 : valuation F (u : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [det_of_isUpperTriangular (hu.1 : (u : Matrix (Fin n) (Fin n) F).BlockTriangular id)]
    simp [hu.2]
  rw [hu1, one_mul] at hdet
  have hp := valuation_uniformizer_pos (F := F)
  have h1 := valuation_uniformizer_lt_one F
  exact le_antisymm ((zpow_le_zpow_iff_right_of_lt_one₀ hp h1).1 hdet.le)
    ((zpow_le_zpow_iff_right_of_lt_one₀ hp h1).1 hdet.ge)

theorem tailSum_succ (l : Fin n → ℤ) {m : ℕ} (hm : m + 1 ≤ n) :
    tailSum l hm = l ⟨n - (m + 1), by omega⟩ + tailSum l (Nat.le_of_succ_le hm) := by
  rw [tailSum, Fin.sum_univ_succ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [tailEmb, Fin.val_succ, Fin.ext_iff]
  omega

theorem eq_of_tailSum_eq {l l' : Fin n → ℤ} (h : ∀ m (hm : m ≤ n), tailSum l hm = tailSum l' hm) :
    l = l' := by
  funext i
  have hm : n - 1 - i.val + 1 ≤ n := by omega
  have e1 := tailSum_succ l hm
  have e2 := tailSum_succ l' hm
  rw [h, h (n - 1 - i.val)] at e1
  have hi : (⟨n - (n - 1 - i.val + 1), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
  rw [hi] at e1 e2
  linarith

def ell (l : Fin n → ℤ) : ℤ := ∑ m : Fin (n + 1), tailSum l (Nat.lt_succ_iff.1 m.2)

theorem ell_le_iwasawaExponent {ν : Fin n → ℤ} (hν : Cartan.IsDominant ν) {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    ell ν ≤ ell (iwasawaExponent F n g) ∧
      (ell ν = ell (iwasawaExponent F n g) → iwasawaExponent F n g = ν) := by
  have hle : ∀ m ∈ (Finset.univ : Finset (Fin (n + 1))),
      tailSum ν (Nat.lt_succ_iff.1 m.2) ≤ tailSum (iwasawaExponent F n g) (Nat.lt_succ_iff.1 m.2) :=
    fun m _ => tailSum_le_iwasawaExponent hν hg _
  refine ⟨Finset.sum_le_sum hle, fun he => ?_⟩
  have := (Finset.sum_eq_sum_iff_of_le hle).1 he
  refine (eq_of_tailSum_eq fun m hm => ?_).symm
  exact this ⟨m, Nat.lt_succ_of_le hm⟩ (Finset.mem_univ _)

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem apply_eq_apply_cartanType (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (h : HeckeAlgebra μ) g = (h : HeckeAlgebra μ) (Cartan.diagPow F n (cartanType F n g)) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := (Cartan.mem_doubleCoset_diagPow F n).1 (cartanType_spec g).2
  conv_lhs => rw [hg]
  rw [(HeckeAlgebraLevel.val_mem _ _ h k₂ hk₂ _).2, HeckeAlgebraLevel.apply_mul_left _ _ h hk₁]

theorem apply_out (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    (h : HeckeAlgebra μ) (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out =
      (h : HeckeAlgebra μ) g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) g
  rw [hk, (HeckeAlgebraLevel.val_mem _ _ h k k.2 g).2]

theorem iwasawaExponent_out (g : GL (Fin n) F) :
    iwasawaExponent F n (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out =
      iwasawaExponent F n g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) g
  rw [hk, iwasawaExponent_mul_of_mem_integralGL F n g k.2]

theorem satake_coeff (h : SphericalHecke μ (F := F) (n := n)) (l : Fin n → ℤ) :
    (satake μ h).coeff l = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h,
        if iwasawaExponent F n x.out = l then (h : HeckeAlgebra μ) x.out else 0 := by
  classical
  rw [satake, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem satakeHom_injective : Function.Injective (satakeHom μ (F := F) (n := n)) := by
  classical
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro h h0
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, (h : HeckeAlgebra μ) g ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (HeckeAlgebraLevel.ext _ _ (HeckeAlgebra.ext fun x => by
      rw [hall x, HeckeAlgebraLevel.val_zero, HeckeAlgebra.coe_zero, Pi.zero_apply]))
  set D := (cosetSupport h).filter fun x => (h : HeckeAlgebra μ) x.out ≠ 0
  have hD : (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n) ∈ D := by
    have hv : (h : HeckeAlgebra μ) (QuotientGroup.mk g : GL (Fin n) F ⧸ integralGL F n).out ≠ 0 := by
      rw [apply_out]
      exact hg
    exact Finset.mem_filter.2 ⟨by by_contra hx; exact hv (apply_out_eq_zero hx), hv⟩
  obtain ⟨x₀, hx₀, hmin⟩ := D.exists_min_image (fun x => ell (cartanType F n x.out)) ⟨_, hD⟩
  set μ₀ := cartanType F n x₀.out
  set c := (h : HeckeAlgebra μ) (Cartan.diagPow F n μ₀)
  have hc : c ≠ 0 := by
    have := (Finset.mem_filter.1 hx₀).2
    rwa [apply_eq_apply_cartanType] at this
  have hclaim : ∀ x ∈ cosetSupport h,
      (if iwasawaExponent F n x.out = μ₀ then (h : HeckeAlgebra μ) x.out else 0) =
        if iwasawaExponent F n x.out = μ₀ ∧ (h : HeckeAlgebra μ) x.out ≠ 0 then c else 0 := by
    intro x hx
    by_cases hxz : (h : HeckeAlgebra μ) x.out = 0
    · simp [hxz]
    by_cases hi : iwasawaExponent F n x.out = μ₀
    · rw [if_pos hi, if_pos ⟨hi, hxz⟩]
      have h1 := hmin x (Finset.mem_filter.2 ⟨hx, hxz⟩)
      have h2 := ell_le_iwasawaExponent (cartanType_spec x.out).1 (cartanType_spec x.out).2
      rw [hi] at h2
      have heq : cartanType F n x.out = μ₀ := (h2.2 (le_antisymm h2.1 h1)).symm
      rw [apply_eq_apply_cartanType, heq]
    · rw [if_neg hi, if_neg fun h' => hi h'.1]
  have hcoeff := congrArg (fun p : LaurentRing n => p.coeff μ₀) h0
  simp only [satakeHom_apply, satake_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply] at hcoeff
  rw [Finset.sum_congr rfl hclaim, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hcoeff
  have hmem : (QuotientGroup.mk (Cartan.diagPow F n μ₀) : GL (Fin n) F ⧸ integralGL F n) ∈
      (cosetSupport h).filter (fun x => iwasawaExponent F n x.out = μ₀ ∧
        (h : HeckeAlgebra μ) x.out ≠ 0) := by
    have hv : (h : HeckeAlgebra μ)
        (QuotientGroup.mk (Cartan.diagPow F n μ₀) : GL (Fin n) F ⧸ integralGL F n).out ≠ 0 := by
      rw [apply_out]
      exact hc
    refine Finset.mem_filter.2 ⟨?_, ?_, hv⟩
    · by_contra hx
      exact hv (apply_out_eq_zero hx)
    · rw [iwasawaExponent_out, diagPow_eq_torusPow, iwasawaExponent_torusPow]
  have hcard := Finset.card_ne_zero.2 ⟨_, hmem⟩
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  rcases mul_eq_zero.1 hcoeff with h1 | h1
  · exact hK h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hcard (by exact_mod_cast h2)
    · exact hc h2

end Spherical

end GroundTheory.Automorphic
