module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR

open CatCoh

universe v u v' u' v'' u''

section Complex

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

theorem semiHom_mp {T T' : C} (φ : T ⟶ T') : SemiHom (RingHom.id R) (mp F φ : F.obj T →+* F.obj T') := by
  intro r b
  simp

def p1 {T T' : C} (φ : T ⟶ T') : Ω[F.obj T⁄R] →ₗ[R] Ω[F.obj T'⁄R] := (semiHom_mp F φ).m1

def pOm (j : ℕ) {T T' : C} (φ : T ⟶ T') : Om R (F.obj T) j →ₗ[R] Om R (F.obj T') j :=
  (semiHom_mp F φ).mOm j

section
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')

theorem p1_D (b : F.obj T) : p1 F φ (D R _ b) = D R _ (mp F φ b) := by
  unfold p1
  exact (semiHom_mp F φ).m1_D b

theorem oneFormsMapOfFunctorMorphism_smul (b : F.obj T) (ω : Ω[F.obj T⁄R]) : p1 F φ (b • ω) = mp F φ b • p1 F φ ω := by
  unfold p1
  exact (semiHom_mp F φ).oneFormMap_smul_semilinear b ω

theorem pOm_smul {j : ℕ} (b : F.obj T) (x : Om R (F.obj T) j) :
    pOm F j φ (b • x) = mp F φ b • pOm F j φ x := by
  unfold pOm
  exact (semiHom_mp F φ).mOm_smul b x

theorem oneFormsMapOfFunctorMorphism_comp (ω : Ω[F.obj T⁄R]) : p1 F (φ ≫ ψ) ω = p1 F ψ (p1 F φ ω) := by
  unfold p1
  exact ((semiHom_mp F φ).oneFormMap_comp_oneFormMap (semiHom_mp F ψ) (semiHom_mp F (φ ≫ ψ))
    (fun b ↦ (mp_comp F φ ψ b).symm) ω).symm

theorem oneFormsMapOfFunctorMorphism_id (ω : Ω[F.obj T⁄R]) : p1 F (𝟙 T) ω = ω := by
  unfold p1
  exact (semiHom_mp F (𝟙 T)).oneFormMap_eq_self_of_id (fun b ↦ mp_id F T b) ω

theorem pOm_comp {j : ℕ} (x : Om R (F.obj T) j) : pOm F j (φ ≫ ψ) x = pOm F j ψ (pOm F j φ x) := by
  unfold pOm
  exact ((semiHom_mp F φ).mOm_mOm (semiHom_mp F ψ) (semiHom_mp F (φ ≫ ψ))
    (fun b ↦ (mp_comp F φ ψ b).symm) x).symm

theorem pOm_id {j : ℕ} (x : Om R (F.obj T) j) : pOm F j (𝟙 T) x = x := by
  unfold pOm
  exact (semiHom_mp F (𝟙 T)).mOm_id (fun b ↦ mp_id F T b) x

theorem pOm_dOm {j : ℕ} (x : Om R (F.obj T) j) :
    pOm F (j + 1) φ (dOm R _ j x) = dOm R _ j (pOm F j φ x) := by
  unfold pOm
  exact (semiHom_mp F φ).mOm_dOm x

theorem pOm_dOne (ω : Ω[F.obj T⁄R]) : pOm F 2 φ (dOne R _ ω) = dOne R _ (p1 F φ ω) := by
  unfold pOm p1
  exact (semiHom_mp F φ).mOm_dOne ω

theorem pOm_dTwo (x : Om R (F.obj T) 2) : pOm F 3 φ (dTwo R _ x) = dTwo R _ (pOm F 2 φ x) := by
  unfold pOm
  exact (semiHom_mp F φ).mOm_dTwo x

theorem pOm_wedge (a b : Ω[F.obj T⁄R]) :
    pOm F 2 φ (wedge R _ a b) = wedge R _ (p1 F φ a) (p1 F φ b) := by
  unfold pOm p1
  exact (semiHom_mp F φ).mOm_wedge a b

end

abbrev C3 := ∀ (T T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T'''

abbrev A0 := ∀ T : C, Ω[F.obj T⁄R]

abbrev A1 := ∀ (T T' : C) (_ : T ⟶ T'), Ω[F.obj T'⁄R]

abbrev A2 := ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T''⁄R]

abbrev W0 (j : ℕ) := ∀ T : C, Om R (F.obj T) j

abbrev W1 (j : ℕ) := ∀ (T T' : C) (_ : T ⟶ T'), Om R (F.obj T') j

abbrev Tot0 := C0 F

abbrev Tot1 := C1 F × A0 F

abbrev Tot2 := C2 F × A1 F × W0 F 2

abbrev Tot3 := C3 F × A2 F × W1 F 2 × W0 F 3

def dTot0 : Tot0 F →ₗ[R] Tot1 F where
  toFun g := (d0 F g, fun T ↦ D R _ (g T))
  map_add' g g' := Prod.ext (map_add _ _ _) (funext fun T ↦ by simp)
  map_smul' r g := Prod.ext (map_smul _ _ _) (funext fun T ↦ by simp)

def dTot1 : Tot1 F →ₗ[R] Tot2 F where
  toFun c := (d1 F c.1, fun T T' φ ↦ c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ),
    fun T ↦ dOne R _ (c.2 T))
  map_add' c c' := Prod.ext (map_add _ _ _) (Prod.ext (by funext T T' φ; simp; abel)
    (funext fun T ↦ by simp))
  map_smul' r c := Prod.ext (map_smul _ _ _) (Prod.ext (by funext T T' φ; simp [smul_sub])
    (funext fun T ↦ by simp))

def dTot2 : Tot2 F →ₗ[R] Tot3 F where
  toFun c := (fun T T' T'' T''' φ ψ χ ↦ c.1 T' T'' T''' ψ χ - c.1 T T'' T''' (φ ≫ ψ) χ +
      c.1 T T' T''' φ (ψ ≫ χ) - mp F χ (c.1 T T' T'' φ ψ),
    fun T T' T'' φ ψ ↦ p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
      D R _ (c.1 T T' T'' φ ψ),
    fun T T' φ ↦ c.2.2 T' - pOm F 2 φ (c.2.2 T) - dOne R _ (c.2.1 T T' φ),
    fun T ↦ dTwo R _ (c.2.2 T))
  map_add' c c' := Prod.ext (by funext T T' T'' T''' φ ψ χ; simp; abel)
    (Prod.ext (by funext T T' T'' φ ψ; simp; abel) (Prod.ext (by funext T T' φ; simp; abel)
    (funext fun T ↦ by simp)))
  map_smul' r c := Prod.ext (by funext T T' T'' T''' φ ψ χ; simp [smul_sub])
    (Prod.ext (by funext T T' T'' φ ψ; simp [smul_sub]) (Prod.ext (by funext T T' φ; simp [smul_sub])
    (funext fun T ↦ by simp)))

section
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')

theorem dTot0_f (g : Tot0 F) : (dTot0 F g).1 T T' φ = g T' - mp F φ (g T) := rfl

theorem dTot0_ω (g : Tot0 F) (T : C) : (dTot0 F g).2 T = D R _ (g T) := rfl

theorem cechDeRhamTotalDifferentialOne_functionPart (c : Tot1 F) :
    (dTot1 F c).1 T T' T'' φ ψ = mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ := rfl

theorem dTot1_a (c : Tot1 F) :
    (dTot1 F c).2.1 T T' φ = c.2 T' - p1 F φ (c.2 T) - D R _ (c.1 T T' φ) := rfl

theorem dTot1_η (c : Tot1 F) (T : C) : (dTot1 F c).2.2 T = dOne R _ (c.2 T) := rfl

end


variable {F} in
theorem Tot1.ext {c c' : Tot1 F} (h1 : ∀ T T' φ, c.1 T T' φ = c'.1 T T' φ) (h2 : ∀ T, c.2 T = c'.2 T) :
    c = c' := by
  refine Prod.ext ?_ ?_
  · funext T T' φ
    exact h1 T T' φ
  · funext T
    exact h2 T


variable {F} in
theorem Tot2.ext {c c' : Tot2 F} (h1 : ∀ T T' T'' φ ψ, c.1 T T' T'' φ ψ = c'.1 T T' T'' φ ψ)
    (h2 : ∀ T T' φ, c.2.1 T T' φ = c'.2.1 T T' φ) (h3 : ∀ T, c.2.2 T = c'.2.2 T) : c = c' := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    exact h1 T T' T'' φ ψ
  · funext T T' φ
    exact h2 T T' φ
  · funext T
    exact h3 T

def cechDeRhamTotalCocyclesOne : Submodule R (Tot1 F) := LinearMap.ker (dTot1 F)

def cechDeRhamTotalCocyclesTwo : Submodule R (Tot2 F) := LinearMap.ker (dTot2 F)

variable {F}

theorem mem_cechDeRhamTotalCocyclesOne_iff {c : Tot1 F} : c ∈ cechDeRhamTotalCocyclesOne F ↔ c.1 ∈ Z1 F ∧
    (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), c.2 T' = p1 F φ (c.2 T) + D R _ (c.1 T T' φ)) ∧
    ∀ T, dOne R _ (c.2 T) = 0 := by
  rw [cechDeRhamTotalCocyclesOne, LinearMap.mem_ker, commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · have e : (dTot1 F c).2.1 T T' φ = 0 := congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) h) T) T') φ
      rw [dTot1_a, sub_sub, sub_eq_zero] at e
      exact e
    · have e : (dTot1 F c).2.2 T = 0 := congrFun (congrArg (fun x ↦ x.2.2) h) T
      rw [dTot1_η] at e
      exact e
  · rintro ⟨h1, h2, h3⟩
    refine Prod.ext h1 (Prod.ext ?_ ?_)
    · funext T T' φ
      show (dTot1 F c).2.1 T T' φ = 0
      rw [dTot1_a, h2 φ]
      abel
    · funext T
      exact h3 T

theorem mem_cechDeRhamTotalCocyclesTwo_iff {c : Tot2 F} : c ∈ cechDeRhamTotalCocyclesTwo F ↔ c.1 ∈ Z2 F ∧
    (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), c.2.1 T T'' (φ ≫ ψ) =
      p1 F ψ (c.2.1 T T' φ) + c.2.1 T' T'' ψ + D R _ (c.1 T T' T'' φ ψ)) ∧
    (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), c.2.2 T' = pOm F 2 φ (c.2.2 T) + dOne R _ (c.2.1 T T' φ)) ∧
    ∀ T, dTwo R _ (c.2.2 T) = 0 := by
  rw [cechDeRhamTotalCocyclesTwo, LinearMap.mem_ker]
  constructor
  · intro h
    refine ⟨?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · intro T T' T'' T''' φ ψ χ
      have e : c.1 T' T'' T''' ψ χ - c.1 T T'' T''' (φ ≫ ψ) χ + c.1 T T' T''' φ (ψ ≫ χ) -
          mp F χ (c.1 T T' T'' φ ψ) = 0 :=
        congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun
          (congrArg Prod.fst h) T) T') T'') T''') φ) ψ) χ
      linear_combination -e
    · have e : p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ) = 0 :=
        congrFun (congrFun (congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) h) T) T') T'') φ) ψ
      have e' : c.2.1 T T'' (φ ≫ ψ) - (p1 F ψ (c.2.1 T T' φ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ)) = -(p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ)) := by abel
      rw [e, neg_zero, sub_eq_zero] at e'
      exact e'
    · have e : c.2.2 T' - pOm F 2 φ (c.2.2 T) - dOne R _ (c.2.1 T T' φ) = 0 :=
        congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.2.1) h) T) T') φ
      rw [sub_sub, sub_eq_zero] at e
      exact e
    · exact congrFun (congrArg (fun x ↦ x.2.2.2) h) T
  · rintro ⟨h1, h2, h3, h4⟩
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext T T' T'' T''' φ ψ χ
      show c.1 T' T'' T''' ψ χ - c.1 T T'' T''' (φ ≫ ψ) χ + c.1 T T' T''' φ (ψ ≫ χ) -
          mp F χ (c.1 T T' T'' φ ψ) = 0
      have e := h1 φ ψ χ
      linear_combination -e
    · funext T T' T'' φ ψ
      show p1 F ψ (c.2.1 T T' φ) - c.2.1 T T'' (φ ≫ ψ) + c.2.1 T' T'' ψ +
          D R _ (c.1 T T' T'' φ ψ) = 0
      rw [h2 φ ψ]
      abel
    · funext T T' φ
      show c.2.2 T' - pOm F 2 φ (c.2.2 T) - dOne R _ (c.2.1 T T' φ) = 0
      rw [h3 φ]
      abel
    · funext T
      exact h4 T

section
variable {T T' T'' T''' : C}

theorem cechDeRhamTotalCocyclesOne.comp (c : cechDeRhamTotalCocyclesOne F) (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    c.1.1 T T'' (φ ≫ ψ) = mp F ψ (c.1.1 T T' φ) + c.1.1 T' T'' ψ := Z1.comp ⟨c.1.1, (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).1⟩ φ ψ

theorem cechDeRhamTotalCocyclesOne.conn (c : cechDeRhamTotalCocyclesOne F) (φ : T ⟶ T') : c.1.2 T' = p1 F φ (c.1.2 T) + D R _ (c.1.1 T T' φ) := (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).2.1 φ

theorem cechDeRhamTotalCocyclesOne.closed (c : cechDeRhamTotalCocyclesOne F) (T : C) : dOne R _ (c.1.2 T) = 0 := (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).2.2 T

theorem cechDeRhamTotalCocyclesTwo.comp (c : cechDeRhamTotalCocyclesTwo F) (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    mp F χ (c.1.1 T T' T'' φ ψ) + c.1.1 T T'' T''' (φ ≫ ψ) χ =
      c.1.1 T T' T''' φ (ψ ≫ χ) + c.1.1 T' T'' T''' ψ χ := by
  have h := (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1
  exact h φ ψ χ

theorem cechDeRhamTotalCocyclesTwo.one (c : cechDeRhamTotalCocyclesTwo F) (φ : T ⟶ T') (ψ : T' ⟶ T'') : c.1.2.1 T T'' (φ ≫ ψ) =
    p1 F ψ (c.1.2.1 T T' φ) + c.1.2.1 T' T'' ψ + D R _ (c.1.1 T T' T'' φ ψ) := (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).2.1 φ ψ

theorem cechDeRhamTotalCocyclesTwo.two (c : cechDeRhamTotalCocyclesTwo F) (φ : T ⟶ T') :
    c.1.2.2 T' = pOm F 2 φ (c.1.2.2 T) + dOne R _ (c.1.2.1 T T' φ) := (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).2.2.1 φ

theorem cechDeRhamTotalCocyclesTwo.closed (c : cechDeRhamTotalCocyclesTwo F) (T : C) : dTwo R _ (c.1.2.2 T) = 0 := (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).2.2.2 T

end

variable (F)

theorem dTot0_mem (g : Tot0 F) : dTot0 F g ∈ cechDeRhamTotalCocyclesOne F := by
  rw [mem_cechDeRhamTotalCocyclesOne_iff]
  refine ⟨commAlgFunctorCoboundaryZero_mem_cocyclesOne F g, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · rw [dTot0_ω, dTot0_ω, dTot0_f, p1_D, map_sub]
    abel
  · rw [dTot0_ω]
    exact dOne_D _

theorem dTot1_mem (c : Tot1 F) : dTot1 F c ∈ cechDeRhamTotalCocyclesTwo F := by
  rw [mem_cechDeRhamTotalCocyclesTwo_iff]
  refine ⟨differential_one_mem_scaled_lattice F c.1, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · simp only [dTot1_a, cechDeRhamTotalDifferentialOne_functionPart, oneFormsMapOfFunctorMorphism_comp, map_sub, map_add (f := _), p1_D]
    abel
  · simp only [dTot1_η, dTot1_a, map_sub, pOm_dOne, dOne_D]
    abel
  · rw [dTot1_η]
    exact dTwo_dOne _

def Hyp1 : Type _ := cechDeRhamTotalCocyclesOne F ⧸ LinearMap.range ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F))

def Hyp2 : Type _ := cechDeRhamTotalCocyclesTwo F ⧸ LinearMap.range ((dTot1 F).codRestrict (cechDeRhamTotalCocyclesTwo F) (dTot1_mem F))

instance : AddCommGroup (Hyp1 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))

instance : Module R (Hyp1 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))

instance : AddCommGroup (Hyp2 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))

instance : Module R (Hyp2 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))

def Hyp1.mk : cechDeRhamTotalCocyclesOne F →ₗ[R] Hyp1 F := Submodule.mkQ _

def Hyp2.mk : cechDeRhamTotalCocyclesTwo F →ₗ[R] Hyp2 F := Submodule.mkQ _

theorem Hyp1.mk_surjective : Function.Surjective (Hyp1.mk F) := Submodule.mkQ_surjective _

theorem Hyp2.mk_surjective : Function.Surjective (Hyp2.mk F) := Submodule.mkQ_surjective _

variable {F}

theorem Hyp1.mk_eq_zero {c : cechDeRhamTotalCocyclesOne F} : Hyp1.mk F c = 0 ↔ ∃ g, dTot0 F g = c.1 := by
  show (Submodule.Quotient.mk c : cechDeRhamTotalCocyclesOne F ⧸ _) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

theorem Hyp2.mk_eq_zero {c : cechDeRhamTotalCocyclesTwo F} : Hyp2.mk F c = 0 ↔ ∃ e, dTot1 F e = c.1 := by
  show (Submodule.Quotient.mk c : cechDeRhamTotalCocyclesTwo F ⧸ _) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, congrArg Subtype.val he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, Subtype.ext he⟩

theorem Hyp1.mk_eq_mk {c c' : cechDeRhamTotalCocyclesOne F} : Hyp1.mk F c = Hyp1.mk F c' ↔ ∃ g, dTot0 F g = c.1 - c'.1 := by
  rw [← sub_eq_zero, ← map_sub, Hyp1.mk_eq_zero]
  rfl

theorem Hyp2.mk_eq_mk {c c' : cechDeRhamTotalCocyclesTwo F} : Hyp2.mk F c = Hyp2.mk F c' ↔ ∃ e, dTot1 F e = c.1 - c'.1 := by
  rw [← sub_eq_zero, ← map_sub, Hyp2.mk_eq_zero]
  rfl

variable (F)

def cupTot : Tot1 F →ₗ[R] Tot1 F →ₗ[R] Tot2 F :=
  LinearMap.mk₂ R
    (fun a b ↦ (fun T T' T'' φ ψ ↦ mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ,
      fun T T' φ ↦ a.1 T T' φ • b.2 T' - b.1 T T' φ • p1 F φ (a.2 T),
      fun T ↦ wedge R _ (a.2 T) (b.2 T)))
    (fun a a' b ↦ Tot2.ext (by intros; simp [add_mul]) (by intros; simp [add_smul]; abel)
      (by intros; simp))
    (fun r a b ↦ Tot2.ext (by intros; simp) (by intros; simp [smul_sub, smul_comm r])
      (by intros; simp [wedge_smul_left]))
    (fun a b b' ↦ Tot2.ext (by intros; simp [mul_add]) (by intros; simp [add_smul]; abel)
      (by intros; simp))
    (fun r a b ↦ Tot2.ext (by intros; simp) (by intros; simp [smul_sub, smul_comm r])
      (by intros; simp [wedge_smul_right]))

section
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (a b : Tot1 F)

theorem cupTot_apply : (cupTot F a b).1 T T' T'' φ ψ = mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ := rfl

theorem cupTot_a : (cupTot F a b).2.1 T T' φ = a.1 T T' φ • b.2 T' - b.1 T T' φ • p1 F φ (a.2 T) := rfl

theorem cupTot_η (T : C) : (cupTot F a b).2.2 T = wedge R _ (a.2 T) (b.2 T) := rfl

end

theorem cupTot_mem (a b : cechDeRhamTotalCocyclesOne F) : cupTot F a.1 b.1 ∈ cechDeRhamTotalCocyclesTwo F := by
  rw [mem_cechDeRhamTotalCocyclesTwo_iff]
  refine ⟨?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · intro T T' T'' T''' φ ψ χ
    simp only [cupTot_apply, cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_add (f := _), mp_comp]
    ring
  · simp only [cupTot_a, cupTot_apply]
    rw [cechDeRhamTotalCocyclesOne.comp a φ ψ, cechDeRhamTotalCocyclesOne.comp b φ ψ, cechDeRhamTotalCocyclesOne.conn b ψ, cechDeRhamTotalCocyclesOne.conn a φ]
    simp only [map_add (f := _), map_sub, oneFormsMapOfFunctorMorphism_smul, oneFormsMapOfFunctorMorphism_comp, p1_D, Derivation.leibniz]
    module
  · simp only [cupTot_η, cupTot_a, map_sub, dOne_smul, cechDeRhamTotalCocyclesOne.closed b, ← pOm_dOne, cechDeRhamTotalCocyclesOne.closed a,
      map_zero, smul_zero, add_zero, pOm_wedge]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [wedge_swap (D R _ (b.1.1 T T' φ)) (p1 F φ (a.1.2 T))]
    abel
  · rw [cupTot_η]
    exact dTwo_wedge (cechDeRhamTotalCocyclesOne.closed a T) (cechDeRhamTotalCocyclesOne.closed b T)

def cupZZ : cechDeRhamTotalCocyclesOne F →ₗ[R] cechDeRhamTotalCocyclesOne F →ₗ[R] cechDeRhamTotalCocyclesTwo F :=
  LinearMap.mk₂ R (fun a b ↦ ⟨cupTot F a.1 b.1, cupTot_mem F a b⟩)
    (fun a a' b ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))
    (fun a b b' ↦ Subtype.ext (by simp)) (fun r a b ↦ Subtype.ext (by simp))

theorem coe_cupZZ (a b : cechDeRhamTotalCocyclesOne F) : (cupZZ F a b).1 = cupTot F a.1 b.1 := rfl

def cupHyp : Hyp1 F →ₗ[R] Hyp1 F →ₗ[R] Hyp2 F :=
  LinearMap.liftQ₂ _ _ ((cupZZ F).compr₂ (Hyp2.mk F))
    (by
      rintro _ ⟨g, rfl⟩
      ext b
      refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ mp F φ (g T) * b.1.1 T T' φ, fun T ↦ g T • b.1.2 T), ?_⟩
      refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
      · simp only [cechDeRhamTotalDifferentialOne_functionPart, coe_cupZZ, cupTot_apply, LinearMap.codRestrict_apply, dTot0_f, cechDeRhamTotalCocyclesOne.comp b,
          map_mul, map_sub, mp_comp]
        ring
      · simp only [dTot1_a, coe_cupZZ, cupTot_a, LinearMap.codRestrict_apply, dTot0_f, dTot0_ω,
          oneFormsMapOfFunctorMorphism_smul, p1_D, Derivation.leibniz]
        rw [cechDeRhamTotalCocyclesOne.conn b φ]
        module
      · simp only [dTot1_η, coe_cupZZ, cupTot_η, LinearMap.codRestrict_apply, dTot0_ω, dOne_smul,
          cechDeRhamTotalCocyclesOne.closed b, smul_zero, add_zero])
    (by
      rintro _ ⟨g, rfl⟩
      ext a
      refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * g T'), fun T ↦ -(g T • a.1.2 T)), ?_⟩
      refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
      · simp only [cechDeRhamTotalDifferentialOne_functionPart, coe_cupZZ, cupTot_apply, LinearMap.codRestrict_apply, dTot0_f, cechDeRhamTotalCocyclesOne.comp a,
          map_mul, map_neg]
        ring
      · simp only [dTot1_a, coe_cupZZ, cupTot_a, LinearMap.codRestrict_apply, dTot0_f, dTot0_ω,
          oneFormsMapOfFunctorMorphism_smul, map_neg, Derivation.leibniz]
        rw [cechDeRhamTotalCocyclesOne.conn a φ]
        module
      · simp only [dTot1_η, coe_cupZZ, cupTot_η, LinearMap.codRestrict_apply, dTot0_ω, dOne_smul,
          map_neg, cechDeRhamTotalCocyclesOne.closed a, smul_zero, add_zero]
        exact (wedge_swap _ _).symm)

theorem cupHyp_mk (a b : cechDeRhamTotalCocyclesOne F) : cupHyp F (Hyp1.mk F a) (Hyp1.mk F b) = Hyp2.mk F (cupZZ F a b) := rfl

def cechDeRhamTotalCocyclesOne.fn : cechDeRhamTotalCocyclesOne F →ₗ[R] Z1 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesOne_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toO : Hyp1 F →ₗ[R] H1 F :=
  Submodule.mapQ _ _ (cechDeRhamTotalCocyclesOne.fn F) (by rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩)

theorem toO_mk (c : cechDeRhamTotalCocyclesOne F) : toO F (Hyp1.mk F c) = H1.mk F (cechDeRhamTotalCocyclesOne.fn F c) := rfl

def Fil1 : Submodule R (Hyp1 F) := LinearMap.ker (toO F)

def Glob1 : Submodule R (A0 F) where
  carrier := {ω | ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T)}
  add_mem' {a b} ha hb T T' φ := by simp [ha φ, hb φ]
  zero_mem' T T' φ := by simp
  smul_mem' r a ha T T' φ := by simp [ha φ]

def Closed1 : Submodule R (Glob1 F) where
  carrier := {ω | ∀ T, dOne R _ (ω.1 T) = 0}
  add_mem' {a b} ha hb T := by simp [ha T, hb T]
  zero_mem' T := by simp
  smul_mem' r a ha T := by simp [ha T]

def formZZ : Closed1 F →ₗ[R] cechDeRhamTotalCocyclesOne F where
  toFun ω := ⟨(0, ω.1.1), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨zero_mem _, fun T T' φ ↦ by simpa using ω.1.2 φ, ω.2⟩⟩
  map_add' a b := Subtype.ext (Prod.ext (add_zero _).symm rfl)
  map_smul' r a := Subtype.ext (Prod.ext (smul_zero _).symm rfl)

def ofForm : Closed1 F →ₗ[R] Hyp1 F := Hyp1.mk F ∘ₗ formZZ F

theorem Fil1_eq_range : Fil1 F = LinearMap.range (ofForm F) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := Hyp1.mk_surjective F x
    rw [Fil1, LinearMap.mem_ker, toO_mk, H1.mk_eq_zero] at hx
    obtain ⟨g, hg⟩ := hx
    have hg' : d0 F g = c.1.1 := hg
    let c' : cechDeRhamTotalCocyclesOne F := c - ⟨dTot0 F g, dTot0_mem F g⟩
    have h1 : c'.1.1 = 0 := by
      show c.1.1 - d0 F g = 0
      rw [hg', sub_self]
    have hm := mem_cechDeRhamTotalCocyclesOne_iff.1 c'.2
    let ω : Closed1 F := ⟨⟨c'.1.2, by
      intro T T' φ
      have e := hm.2.1 φ
      rw [h1] at e
      simpa using e⟩, by
      intro T
      exact hm.2.2 T⟩
    refine ⟨ω, ?_⟩
    show Hyp1.mk F (formZZ F ω) = Hyp1.mk F c
    have hω : formZZ F ω = c' := Subtype.ext (Prod.ext h1.symm rfl)
    rw [hω, Hyp1.mk_eq_mk]
    refine ⟨-g, ?_⟩
    rw [map_neg]
    show -dTot0 F g = (c.1 - dTot0 F g) - c.1
    abel
  · rintro ⟨ω, rfl⟩
    rw [Fil1, LinearMap.mem_ker]
    show toO F (Hyp1.mk F (formZZ F ω)) = 0
    rw [toO_mk, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    rfl


variable {F} in
theorem ofForm_eq_zero {ω : Closed1 F} : ofForm F ω = 0 ↔
    ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ T, D R _ (g T) = ω.1.1 T := by
  show Hyp1.mk F (formZZ F ω) = 0 ↔ _
  rw [Hyp1.mk_eq_zero]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · have e : (dTot0 F g).1 T T' φ = 0 := congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ
      rw [dTot0_f] at e
      exact sub_eq_zero.1 e
    · have e : (dTot0 F g).2 T = ω.1.1 T := congrFun (congrArg Prod.snd hg) T
      rw [dTot0_ω] at e
      exact e
  · rintro ⟨g, h1, h2⟩
    refine ⟨g, Prod.ext ?_ ?_⟩
    · funext T T' φ
      show (dTot0 F g).1 T T' φ = 0
      rw [dTot0_f, h1 φ, sub_self]
    · funext T
      show (dTot0 F g).2 T = ω.1.1 T
      rw [dTot0_ω]
      exact h2 T

end Complex

end GlobalTheory.CechDR
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR

open CatCoh

universe v u v' u' v'' u''

section Pull

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')

theorem semiHom_coef (T : C') : SemiHom σ (m.α T) := m.smul T

def q1 (T : C') : Ω[F.obj (m.G.obj T)⁄R] →ₛₗ[σ] Ω[F'.obj T⁄R'] := (semiHom_coef m T).m1

def qOm (j : ℕ) (T : C') : Om R (F.obj (m.G.obj T)) j →ₛₗ[σ] Om R' (F'.obj T) j :=
  (semiHom_coef m T).mOm j

section
variable {T T' : C'}

theorem cechDeRhamCoefMapOneForms_D (b : F.obj (m.G.obj T)) : q1 m T (D R _ b) = D R' _ (m.α T b) := (semiHom_coef m T).m1_D b

theorem prodFirstProjection_smul (b : F.obj (m.G.obj T)) (ω : Ω[F.obj (m.G.obj T)⁄R]) :
    q1 m T (b • ω) = m.α T b • q1 m T ω := (semiHom_coef m T).oneFormMap_smul_semilinear b ω

theorem cechDeRhamCoefMapOneForms_naturality (φ : T ⟶ T') (ω : Ω[F.obj (m.G.obj T)⁄R]) :
    q1 m T' (p1 F (m.G.map φ) ω) = p1 F' φ (q1 m T ω) :=
  (SemiHom.oneFormMap_comp_oneFormMap _ _ ((semiHom_coef m T).comp (semiHom_mp F' φ)) (m.naturality φ) ω).trans
    (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) ω).symm

theorem qOm_pOm {j : ℕ} (φ : T ⟶ T') (x : Om R (F.obj (m.G.obj T)) j) :
    qOm m j T' (pOm F j (m.G.map φ) x) = pOm F' j φ (qOm m j T x) :=
  (SemiHom.mOm_mOm _ _ ((semiHom_coef m T).comp (semiHom_mp F' φ)) (m.naturality φ) x).trans
    (SemiHom.mOm_mOm _ _ _ (fun _ ↦ rfl) x).symm

theorem qOm_dOne (ω : Ω[F.obj (m.G.obj T)⁄R]) : qOm m 2 T (dOne R _ ω) = dOne R' _ (q1 m T ω) :=
  (semiHom_coef m T).mOm_dOne ω

theorem qOm_dTwo (x : Om R (F.obj (m.G.obj T)) 2) : qOm m 3 T (dTwo R _ x) = dTwo R' _ (qOm m 2 T x) :=
  (semiHom_coef m T).mOm_dTwo x

theorem qOm_wedge (a b : Ω[F.obj (m.G.obj T)⁄R]) :
    qOm m 2 T (wedge R _ a b) = wedge R' _ (q1 m T a) (q1 m T b) := (semiHom_coef m T).mOm_wedge a b

end

def pullTot1 : Tot1 F →ₛₗ[σ] Tot1 F' where
  toFun c := (fun _ T' φ ↦ m.α T' (c.1 _ _ (m.G.map φ)), fun T ↦ q1 m T (c.2 _))
  map_add' a b := Tot1.ext (F := F') (by intros; simp) (by intros; simp)
  map_smul' r a := Tot1.ext (F := F') (by intros; simp [m.smul]) (by intros; simp)

def pullTot2 : Tot2 F →ₛₗ[σ] Tot2 F' where
  toFun c := (fun _ _ T'' φ ψ ↦ m.α T'' (c.1 _ _ _ (m.G.map φ) (m.G.map ψ)),
    fun _ T' φ ↦ q1 m T' (c.2.1 _ _ (m.G.map φ)), fun T ↦ qOm m 2 T (c.2.2 _))
  map_add' a b := Tot2.ext (F := F') (by intros; simp) (by intros; simp) (by intros; simp)
  map_smul' r a := Tot2.ext (F := F') (by intros; simp [m.smul]) (by intros; simp) (by intros; simp)

section
variable {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'')

theorem pullTot1_f (c : Tot1 F) : (pullTot1 m c).1 T T' φ = m.α T' (c.1 _ _ (m.G.map φ)) := rfl

theorem pullTot1_ω (c : Tot1 F) (T : C') : (pullTot1 m c).2 T = q1 m T (c.2 _) := rfl

theorem cechDeRhamPullbackTotalDegreeTwo_function_part (c : Tot2 F) :
    (pullTot2 m c).1 T T' T'' φ ψ = m.α T'' (c.1 _ _ _ (m.G.map φ) (m.G.map ψ)) := rfl

theorem pullTot2_a (c : Tot2 F) : (pullTot2 m c).2.1 T T' φ = q1 m T' (c.2.1 _ _ (m.G.map φ)) := rfl

theorem pullTot2_η (c : Tot2 F) (T : C') : (pullTot2 m c).2.2 T = qOm m 2 T (c.2.2 _) := rfl

end

theorem pullTot1_dTot0 (g : Tot0 F) : pullTot1 m (dTot0 F g) = dTot0 F' fun T ↦ m.α T (g _) :=
  Tot1.ext (fun T T' φ ↦ by simp only [pullTot1_f, dTot0_f, map_sub, m.naturality])
    fun T ↦ by simp only [pullTot1_ω, dTot0_ω, cechDeRhamCoefMapOneForms_D]

theorem pullTot2_dTot1 (c : Tot1 F) : pullTot2 m (dTot1 F c) = dTot1 F' (pullTot1 m c) :=
  Tot2.ext (fun T T' T'' φ ψ ↦ by
      simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, cechDeRhamTotalDifferentialOne_functionPart, pullTot1_f, map_sub, map_add (f := _), m.naturality, Functor.map_comp])
    (fun T T' φ ↦ by simp only [pullTot2_a, dTot1_a, pullTot1_f, pullTot1_ω, map_sub, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D])
    fun T ↦ by simp only [pullTot2_η, dTot1_η, pullTot1_ω, qOm_dOne]

theorem pullTot2_cupTot (a b : Tot1 F) :
    pullTot2 m (cupTot F a b) = cupTot F' (pullTot1 m a) (pullTot1 m b) :=
  Tot2.ext (fun T T' T'' φ ψ ↦ by simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, cupTot_apply, pullTot1_f, map_mul, m.naturality])
    (fun T T' φ ↦ by simp only [pullTot2_a, cupTot_a, pullTot1_f, pullTot1_ω, map_sub, cechDeRhamCoefMapOneForms_naturality, prodFirstProjection_smul])
    fun T ↦ by simp only [pullTot2_η, cupTot_η, pullTot1_ω, qOm_wedge]

def pullZZ1 : cechDeRhamTotalCocyclesOne F →ₛₗ[σ] cechDeRhamTotalCocyclesOne F' :=
  ((pullTot1 m).domRestrict (cechDeRhamTotalCocyclesOne F)).codRestrict (cechDeRhamTotalCocyclesOne F') fun c ↦ by
    change dTot1 F' (pullTot1 m c.1) = 0
    rw [← pullTot2_dTot1, show dTot1 F c.1 = 0 from c.2, map_zero]

def pullZZ2 : cechDeRhamTotalCocyclesTwo F →ₛₗ[σ] cechDeRhamTotalCocyclesTwo F' :=
  ((pullTot2 m).domRestrict (cechDeRhamTotalCocyclesTwo F)).codRestrict (cechDeRhamTotalCocyclesTwo F') fun c ↦ by
    change pullTot2 m c.1 ∈ _
    refine mem_cechDeRhamTotalCocyclesTwo_iff.2 ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
    · simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, Functor.map_comp, ← map_add (f := _), ← m.naturality, cechDeRhamTotalCocyclesTwo.comp c]
    · simp only [cechDeRhamPullbackTotalDegreeTwo_function_part, pullTot2_a, Functor.map_comp, cechDeRhamTotalCocyclesTwo.one c, map_add (f := _), cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D]
    · simp only [pullTot2_η, pullTot2_a]
      rw [cechDeRhamTotalCocyclesTwo.two c (m.G.map φ), map_add (f := _), qOm_pOm, qOm_dOne]
    · rw [pullTot2_η, ← qOm_dTwo, cechDeRhamTotalCocyclesTwo.closed c, map_zero]

theorem coe_pullZZ1 (c : cechDeRhamTotalCocyclesOne F) : (pullZZ1 m c).1 = pullTot1 m c.1 := rfl

theorem coe_pullZZ2 (c : cechDeRhamTotalCocyclesTwo F) : (pullZZ2 m c).1 = pullTot2 m c.1 := rfl

def pullHyp1 : Hyp1 F →ₛₗ[σ] Hyp1 F' :=
  Submodule.mapQ _ _ (pullZZ1 m) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, Subtype.ext (pullTot1_dTot0 m g).symm⟩)

def pullHyp2 : Hyp2 F →ₛₗ[σ] Hyp2 F' :=
  Submodule.mapQ _ _ (pullZZ2 m) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, Subtype.ext (pullTot2_dTot1 m g).symm⟩)

theorem pullHyp1_mk (c : cechDeRhamTotalCocyclesOne F) : pullHyp1 m (Hyp1.mk F c) = Hyp1.mk F' (pullZZ1 m c) := rfl

theorem pullHyp2_mk (c : cechDeRhamTotalCocyclesTwo F) : pullHyp2 m (Hyp2.mk F c) = Hyp2.mk F' (pullZZ2 m c) := rfl

theorem pullHyp2_cup (a b : Hyp1 F) :
    pullHyp2 m (cupHyp F a b) = cupHyp F' (pullHyp1 m a) (pullHyp1 m b) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  exact congrArg (Hyp2.mk F') (Subtype.ext (pullTot2_cupTot m a.1 b.1))

theorem toO_pullHyp1 (c : Hyp1 F) : toO F' (pullHyp1 m c) = m.pull1 (toO F c) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F c; rfl

def pullGlob1 : Glob1 F →ₛₗ[σ] Glob1 F' where
  toFun ω := ⟨fun T ↦ q1 m T (ω.1 _), fun T T' φ ↦ by
    simp only; rw [ω.2 (m.G.map φ), cechDeRhamCoefMapOneForms_naturality]⟩
  map_add' a b := Subtype.ext (funext fun T ↦ by simp)
  map_smul' r a := Subtype.ext (funext fun T ↦ by simp)

def pullClosed1 : Closed1 F →ₛₗ[σ] Closed1 F' :=
  ((pullGlob1 m).domRestrict (Closed1 F)).codRestrict (Closed1 F') fun ω T ↦ by
    change dOne R' _ (q1 m T (ω.1.1 _)) = 0
    rw [← qOm_dOne, ω.2, map_zero]

theorem pullHyp1_ofForm (ω : Closed1 F) : pullHyp1 m (ofForm F ω) = ofForm F' (pullClosed1 m ω) :=
  congrArg (Hyp1.mk F') (Subtype.ext (Tot1.ext (fun _ _ _ ↦ map_zero _) fun _ ↦ rfl))

theorem cechDeRhamCoefMapOneForms_restrictAlongFunctor (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (T : C') (ω : Ω[F.obj (G.obj T)⁄R]) :
    q1 (CoefMap.restrict F G) T ω = ω := SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω

theorem qOm_restrict (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) {j : ℕ} (T : C')
    (x : Om R (F.obj (G.obj T)) j) : qOm (CoefMap.restrict F G) j T x = x :=
  SemiHom.mOm_id _ (fun _ ↦ rfl) x

theorem pullHyp1_id (c : Hyp1 F) : pullHyp1 (CoefMap.id F) c = c := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F c
  exact congrArg (Hyp1.mk F) (Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl)
    fun _ ↦ SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) _))

theorem pullHyp2_id (c : Hyp2 F) : pullHyp2 (CoefMap.id F) c = c := by
  obtain ⟨a, rfl⟩ := Hyp2.mk_surjective F c
  exact congrArg (Hyp2.mk F) (Subtype.ext (Tot2.ext (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ ↦ SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) _) fun _ ↦ SemiHom.mOm_id _ (fun _ ↦ rfl) _))

theorem pullHyp1_comp (n : CoefMap τ F' F'') (c : Hyp1 F) :
    pullHyp1 (m.comp n) c = pullHyp1 n (pullHyp1 m c) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F c
  exact congrArg (Hyp1.mk F'') (Subtype.ext (Tot1.ext (fun _ _ _ ↦ rfl)
    fun _ ↦ (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _).symm))

theorem pullHyp2_comp (n : CoefMap τ F' F'') (c : Hyp2 F) :
    pullHyp2 (m.comp n) c = pullHyp2 n (pullHyp2 m c) := by
  obtain ⟨a, rfl⟩ := Hyp2.mk_surjective F c
  exact congrArg (Hyp2.mk F'') (Subtype.ext (Tot2.ext (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ ↦ (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _).symm)
    fun _ ↦ (SemiHom.mOm_mOm _ _ _ (fun _ ↦ rfl) _).symm))

section Nat

variable {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
  (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b)
include h

theorem cechDeRhamCoefMapOneForms_eq_of_natTrans (T : C') (ω : Ω[F.obj (m.G.obj T)⁄R]) : q1 m' T (p1 F (θ.app T) ω) = q1 m T ω :=
  SemiHom.oneFormMap_comp_oneFormMap _ _ _ (h T) ω

theorem qOm_pOm_app {j : ℕ} (T : C') (x : Om R (F.obj (m.G.obj T)) j) :
    qOm m' j T (pOm F j (θ.app T) x) = qOm m j T x := SemiHom.mOm_mOm _ _ _ (h T) x

theorem pullHyp1_eq_of_natTrans (c : Hyp1 F) : pullHyp1 m c = pullHyp1 m' c := by
  obtain ⟨f, rfl⟩ := Hyp1.mk_surjective F c
  rw [pullHyp1_mk, pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨fun T ↦ -m'.α T (f.1.1 _ _ (θ.app T)), Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · have e := congrArg (fun ξ ↦ m'.α T' (f.1.1 _ _ ξ)) (θ.naturality φ)
    simp only [cechDeRhamTotalCocyclesOne.comp f, map_add (f := _), h, m'.naturality] at e
    simp only [dTot0_f, Prod.fst_sub, Pi.sub_apply, coe_pullZZ1, pullTot1_f, map_neg]
    linear_combination -e
  · simp only [dTot0_ω, Prod.snd_sub, Pi.sub_apply, coe_pullZZ1, pullTot1_ω, map_neg]
    rw [cechDeRhamTotalCocyclesOne.conn f (θ.app T), map_add (f := _), cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h, cechDeRhamCoefMapOneForms_D]; abel

theorem pullHyp2_eq_of_natTrans (c : Hyp2 F) : pullHyp2 m c = pullHyp2 m' c := by
  obtain ⟨z, rfl⟩ := Hyp2.mk_surjective F c
  rw [pullHyp2_mk, pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨(fun T T' φ ↦ m'.α T' (z.1.1 _ _ _ (m.G.map φ) (θ.app T') -
    z.1.1 _ _ _ (θ.app T) (m'.G.map φ)), fun T ↦ -q1 m' T (z.1.2.1 _ _ (θ.app T))),
    Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · have e1 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    simp only [map_add (f := _), h, m'.naturality] at e1 e2 e3
    simp only [cechDeRhamTotalDifferentialOne_functionPart, Prod.fst_sub, Pi.sub_apply, coe_pullZZ2, cechDeRhamPullbackTotalDegreeTwo_function_part, map_sub, Functor.map_comp]
    linear_combination -e1 + e2 - e3
  · have e := congrArg (fun ξ ↦ q1 m' T' (z.1.2.1 _ _ ξ)) (θ.naturality φ)
    simp only [cechDeRhamTotalCocyclesTwo.one z, map_add (f := _), cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D] at e
    simp only [dTot1_a, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, coe_pullZZ2, pullTot2_a, map_sub,
      map_neg]
    linear_combination (norm := abel1) -e
  · simp only [dTot1_η, Prod.snd_sub, Pi.sub_apply, coe_pullZZ2, pullTot2_η, map_neg]
    rw [cechDeRhamTotalCocyclesTwo.two z (θ.app T), map_add (f := _), qOm_pOm_app m m' θ h, qOm_dOne]; abel

end Nat

end Pull

section Initial

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def exact1 : Submodule R (LinearMap.ker (dOne R B)) :=
  (LinearMap.range (D R B).toLinearMap).comap (LinearMap.ker (dOne R B)).subtype

abbrev AlgebraFirstDeRham : Type := LinearMap.ker (dOne R B) ⧸ exact1 R B

variable {R B} {C : Type u} [Category.{v} C] {F : C ⥤ CommAlgCat.{0} R}
  (e : ∀ T : C, B →ₐ[R] F.obj T) (he : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (b : B), mp F φ (e T b) = e T' b)

def coneForm : LinearMap.ker (dOne R B) →ₗ[R] Closed1 F where
  toFun ω := ⟨⟨fun T ↦ (SemiHom.of_algHom (e T)).m1 ω.1, fun T T' φ ↦
    (SemiHom.oneFormMap_comp_oneFormMap _ _ _ (he φ) _).symm⟩, fun T ↦ by
      change dOne R _ ((SemiHom.of_algHom (e T)).m1 ω.1) = 0
      rw [← SemiHom.mOm_dOne, show dOne R B ω.1 = 0 from ω.2, map_zero]⟩
  map_add' a b := Subtype.ext (Subtype.ext (funext fun T ↦ map_add _ _ _))
  map_smul' r a := Subtype.ext (Subtype.ext (funext fun T ↦ (SemiHom.of_algHom (e T)).m1.map_smulₛₗ r a.1))

theorem coneForm_apply (ω : LinearMap.ker (dOne R B)) (T : C) :
    (coneForm e he ω).1.1 T = (SemiHom.of_algHom (e T)).m1 ω.1 := rfl

def coneMap : AlgebraFirstDeRham R B →ₗ[R] Hyp1 F :=
  Submodule.liftQ _ (ofForm F ∘ₗ coneForm e he) (by
    rintro ω ⟨b, hb⟩
    refine ofForm_eq_zero.2 ⟨fun T ↦ e T b, fun T T' φ ↦ (he φ b).symm, fun T ↦ ?_⟩
    rw [coneForm_apply, show ω.1 = D R B b from hb.symm, SemiHom.m1_D]; rfl)

theorem coneMap_mk (ω : LinearMap.ker (dOne R B)) :
    coneMap e he (Submodule.Quotient.mk ω) = ofForm F (coneForm e he ω) := rfl

theorem coneMap_bijective {T₀ : C} (h : Limits.IsInitial T₀) (hb : Function.Bijective (e T₀)) :
    Function.Bijective (coneMap e he) := by
  let i := (AlgEquiv.ofBijective _ hb).symm.toAlgHom
  have hi : ∀ b, i (e T₀ b) = b := (AlgEquiv.ofBijective _ hb).symm_apply_apply
  have hi' : ∀ b, e T₀ (i b) = b := (AlgEquiv.ofBijective _ hb).apply_symm_apply
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨g, -, hg⟩ := ofForm_eq_zero.1 hc
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨i (g T₀), ?_⟩
    have := congrArg (SemiHom.of_algHom i).m1 (hg T₀)
    rw [SemiHom.m1_D, coneForm_apply] at this
    exact this.trans ((SemiHom.oneFormMap_comp_oneFormMap _ _ (SemiHom.of_algHom (AlgHom.id R B)) (fun b ↦ hi b) _).trans
      (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) _))
  · intro c
    have hc : c ∈ Fil1 F := H1.eq_zero_of_isInitial F h _
    rw [Fil1_eq_range] at hc
    obtain ⟨ω, rfl⟩ := hc
    refine ⟨Submodule.Quotient.mk ⟨(SemiHom.of_algHom i).m1 (ω.1.1 T₀), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, ← SemiHom.mOm_dOne, ω.2 T₀, map_zero]
    · rw [coneMap_mk]
      refine congrArg _ (Subtype.ext (Subtype.ext (funext fun T ↦ ?_)))
      rw [coneForm_apply, ω.1.2 (h.to T)]
      exact SemiHom.oneFormMap_comp_oneFormMap _ _ (semiHom_mp F (h.to T))
        (fun b ↦ ((he (h.to T) (i b)).symm.trans (congrArg _ (hi' b)))) _

end Initial

end GlobalTheory.CechDR
