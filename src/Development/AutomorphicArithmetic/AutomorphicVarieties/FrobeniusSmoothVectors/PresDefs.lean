module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def UpT {C : Type} [Zero C] {n : ℕ} (M : Matrix (Fin n) (Fin n) C) : Prop := ∀ i j, j < i → M i j = 0

def bor {K : Type} [CommRing K] {n : ℕ} (g : GL (Fin n) K) : Submodule K (Matrix (Fin n) (Fin n) K) where
  carrier := {X | UpT ((g : Matrix (Fin n) (Fin n) K) * X * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
  add_mem' {X Y} hX hY i j h := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  zero_mem' i j _ := by simp
  smul_mem' c X hX i j h := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX i j h, smul_zero]

def lieT (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => ((w n i : ℤ) : K)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

@[ext] structure Box (F : Frame l k) (n : ℕ) (C : Type) [CommRing C] where
  r : F.Γ →* GG (m := n) (R := C)
  nu : ∀ s, (r s).right = F.del s
  g : F.V → GL (Fin n) C
  tri : ∀ v s, UpT ((g v : Matrix (Fin n) (Fin n) C) * (r (F.loc v s)).mat *
    (((g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))

variable {F : Frame l k} {n : ℕ}

namespace Box

variable {C C' : Type} [CommRing C] [CommRing C']

def map (f : C →+* C') (B : Box F n C) : Box F n C' where
  r := (GG.map f).comp B.r
  nu := B.nu
  g v := GeneralLinearGroup.map f (B.g v)
  tri v s i j h := by
    have e : ((GeneralLinearGroup.map f (B.g v) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
        (((GG.map f).comp B.r) (F.loc v s)).mat *
        (((GeneralLinearGroup.map f (B.g v))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).mat *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul, ← map_inv]
      rfl
    rw [e]
    exact (congrArg f (B.tri v s i j h)).trans (map_zero f)

theorem map_map {C'' : Type} [CommRing C''] (f : C →+* C') (f' : C' →+* C'') (B : Box F n C) :
    (B.map f).map f' = B.map (f'.comp f) := rfl

def Cont (I : Ideal C) (B : Box F n C) : Prop := ∀ i j, AdicCont I fun s => (B.r s).mat i j

structure Of (B : Box F n C) (ρ : NRep F n C) : Prop where
  atc : (B.r F.c).mat = 1
  res : ∀ s : F.G0, (B.r s).mat = ρ.r s
  psi : ∀ v i s, ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) i i = ρ.ψ v i s

theorem Of.map {B : Box F n C} {ρ : NRep F n C} (h : B.Of ρ) (f : C →+* C') : (B.map f).Of (ρ.map f) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((B.r F.c).mat).map f = 1
    rw [h.atc]
    exact Matrix.map_one _ (map_zero f) (map_one f)
  · intro s
    show ((B.r s).mat).map f = _
    rw [h.res]
    rfl
  · intro v i s
    have e : (((B.map f).g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') * (ρ.map f).r (F.loc0 v s) *
        ((((B.map f).g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
        f.mapMatrix ((B.g v : Matrix (Fin n) (Fin n) C) * ρ.r (F.loc0 v s) *
          (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) := by
      rw [map_mul, map_mul]
      rfl
    rw [e]
    exact congrArg f (h.psi v i s)

def ad (B : Box F n C) : Representation C F.Γ (Matrix (Fin n) (Fin n) C) := adRep B.r

def b (B : Box F n C) (v : F.V) : Submodule C (Matrix (Fin n) (Fin n) C) := bor (B.g v)

end Box

structure NRep.Good {K : Type} [Field K] (ρ : NRep F n K) : Prop where
  two : (2 : K) ≠ 0
  zd : ∀ i j, i ≠ j → (ρ.r F.g0 - ρ.r (F.star F.g0)) i i ≠ (ρ.r F.g0 - ρ.r (F.star F.g0)) j j
  ψd : ∀ v, ∃ s, ∀ i j, i ≠ j → ρ.ψ v i s ≠ ρ.ψ v j s

section CO

variable (O : Type) [CommRing O] [IsLocalRing O]

abbrev NRep.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (ρ : NRep F n C) : NRep F n (ResidueField O) :=
  ρ.map (res O C : C →+* ResidueField O)

abbrev Box.bar {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (B : Box F n C) : Box F n (ResidueField O) :=
  B.map (res O C : C →+* ResidueField O)

structure NRep.Univ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) : Prop where
  cont : ρ.Cont (maximalIdeal R)
  univ : ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (ρ' : NRep F n C), ρ'.Cont (maximalIdeal C) →
    ρ'.bar O = ρ.bar O → ∃! g : R →ₐ[O] C, ρ.map (g : R →+* C) = ρ'

abbrev Tan (R : Type) [CommRing R] [Algebra O R] [IsCO O R] : Submodule (ResidueField O) (R →ₗ[O] ResidueField O) :=
  PtDer (res O R) (ResidueField O)

def Box.tanCo {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R) :
    (R →ₗ[O] ResidueField O) →ₗ[ResidueField O] (F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun D s := (B.r s).mat.map D *
    ((((B.bar O).r s).left⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O))
  map_add' D D' := funext fun s => by
    rw [Pi.add_apply, ← Matrix.add_mul]
    rfl
  map_smul' c D := funext fun s => by
    rw [Pi.smul_apply, RingHom.id_apply, ← Matrix.smul_mul]
    rfl

structure IsSq {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (μ : ResidueField O →+ C) : Prop where
  mul : ∀ a c, μ (res O C a * c) = a * μ c
  mem : ∀ c, μ c ∈ maximalIdeal C

variable {O}


open Classical in
def evK {C : Type} [CommRing C] [Algebra O C] (K : Ideal C) (u : K →ₗ[O] ResidueField O) (x : C) : ResidueField O :=
  if h : x ∈ K then u ⟨x, h⟩ else 0

theorem evK_of_mem {C : Type} [CommRing C] [Algebra O C] {K : Ideal C} (u : K →ₗ[O] ResidueField O) {x : C}
    (h : x ∈ K) : evK K u x = u ⟨x, h⟩ := dite_eq_left h

variable {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C] [Algebra O C]

structure SetLift (p : C' →ₐ[O] C) (B : Box F n C) where
  r : F.Γ → GL (Fin n) C'
  r_cont : ∀ i j, AdicCont (maximalIdeal C') fun s => r s i j
  r_map : ∀ s, GeneralLinearGroup.map (p : C' →+* C) (r s) = (B.r s).left
  g : F.V → GL (Fin n) C'
  g_map : ∀ v, GeneralLinearGroup.map (p : C' →+* C) (g v) = B.g v
  t : ∀ v, F.Gv v → GL (Fin n) C'
  t_cont : ∀ v i j, AdicCont (maximalIdeal C') fun s => t v s i j
  t_tri : ∀ v s, UpT (t v s : Matrix (Fin n) (Fin n) C')
  t_map : ∀ v s, GeneralLinearGroup.map (p : C' →+* C) (t v s) = B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹

namespace SetLift

variable {p : C' →ₐ[O] C} {B : Box F n C} (D : SetLift p B)

def om (x : F.Γ × F.Γ) : Matrix (Fin n) (Fin n) C' :=
  ((D.r x.1 * sgnAct n C' (F.del x.1) (D.r x.2) * (D.r (x.1 * x.2))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def a (v : F.V) (s : F.Gv v) : Matrix (Fin n) (Fin n) C' :=
  ((D.r (F.loc v s) * ((D.g v)⁻¹ * D.t v s * D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1

def co : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O]
    (F.Γ × F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) × (∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)) where
  toFun u := (fun x => (D.om x).map (evK _ u), fun v s => (D.a v s).map (evK _ u))
  map_add' u u' := by
    have e : ∀ x, evK _ (u + u') x = evK _ u x + evK _ u' x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]
  map_smul' c u := by
    have e : ∀ x, evK _ (c • u) x = c * evK _ u x := fun x => by
      unfold evK
      split_ifs <;> simp
    ext <;> simp [e]

end SetLift


variable (O) in
def HasObs (R : Type) [CommRing R] [Algebra O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ →
    ∃ ob : (RingHom.ker p →ₗ[O] ResidueField O) →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

def IsMinPres {σ R : Type} [CommRing R] [Algebra O R] (p : MvPowerSeries σ O →ₐ[O] R) : Prop :=
  Function.Surjective p ∧ ∀ f ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) f ∈ maximalIdeal O

end CO

end UpperTheory.V.Fr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.star :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → (∀ g : F.G0, F.star (F.star g) = g) ∧ (∀ g h : F.G0, F.star (g * h) = F.star h * F.star g) ∧ (∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹) ∧ Continuous F.star ∧ ∀ {n : ℕ} {K : Type} [CommRing K] (ρ : NRep F n K) (g : F.G0) (i j : Fin n), ρ.r (F.star g) i j = ρ.r g j.rev i.rev := by
  intro l _ k _ _ F C₀ hF
  have hs : ∀ g : F.G0, ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := fun g => by
    simp [Frame.star, Frame.conj, MulAut.conjNormal_apply, mul_assoc]
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  refine ⟨fun g => ?_, fun g h => ?_, fun g => ?_, ?_, fun {n} {K} _ ρ g i j => ?_⟩
  · apply Subtype.ext
    rw [hs, hs, hc]
    simp only [_root_.mul_inv_rev, inv_inv, hc]
    calc F.c * (F.c * ((g : F.Γ) * F.c)) * F.c = (F.c * F.c) * (g : F.Γ) * (F.c * F.c) := by group
      _ = g := by rw [hF.c_sq]; group
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, hs, _root_.mul_inv_rev, hc]
    calc F.c * ((h : F.Γ)⁻¹ * (g : F.Γ)⁻¹) * F.c
        = F.c * (h : F.Γ)⁻¹ * (F.c * F.c) * (g : F.Γ)⁻¹ * F.c := by rw [hF.c_sq]; group
      _ = F.c * (h : F.Γ)⁻¹ * F.c * (F.c * (g : F.Γ)⁻¹ * F.c) := by group
  · rw [hs, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  · refine continuous_induced_rng.2 ?_
    have : (fun g : F.G0 => ((F.star g : F.G0) : F.Γ)) = fun g : F.G0 => F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := funext hs
    change Continuous (fun g : F.G0 => ((F.star g : F.G0) : F.Γ))
    rw [this]
    exact (continuous_const.mul continuous_subtype_val.inv).mul continuous_const
  · rw [ρ.pol]
    simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
    have h : ∀ a : Fin n, (j = a.rev) ↔ (a = j.rev) := fun a => by
      constructor <;> rintro rfl <;> simp
    simp [h]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FlagLoc
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem entry_of_conj {C : Type} [CommRing C] {n : ℕ} (g : GL (Fin n) C) (f : Fin n → Matrix (Fin n) (Fin n) C)
    (hg : ∀ i, (g : Matrix (Fin n) (Fin n) C) * f i * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = single i i 1)
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n) :
    ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b =
      ((g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b := by
  have h : (g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      single a a 1 * ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) *
        single b b 1 := by
    rw [← hg a, ← hg b]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [h, Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, one_mul, mul_one]

theorem UpperTheory.V.Fr.flag_loc :
    ∀ {H C : Type} [Group H] [CommRing C] [IsLocalRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ) (g₀ : H), (∀ i j, i ≠ j → IsUnit ((ψ i g₀ : C) - ψ j g₀)) → ((r g₀).map (residue C)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (residue C (ψ i g₀))) → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) → UpperTheory.V.W.HasFlag r.toHomUnits ψ := by
  intro H C _ _ _ n r ψ g₀ hu hc ho
  have h0 := UpperTheory.V.AlgebraTools.ord_ext (R := C) r (fun i => (Units.coeHom C).comp (ψ i)) (fun g => by
    have := ho g
    unfold ordProd at this
    simpa only [Algebra.algebraMap_eq_smul_one, MonoidHom.comp_apply, Units.coeHom_apply] using this)
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.AlgebraTools.lag_triangular (MonoidAlgebra.lift C (Matrix (Fin n) (Fin n) C) H r)
    (fun i => MonoidAlgebra.lift C C H ((Units.coeHom C).comp (ψ i))) (MonoidAlgebra.of C H g₀) h0
    (fun i j hij => by simpa using hu i j hij)
  simp only [MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply] at h1 h2 h3
  have h4 := UpperTheory.V.AlgebraTools.lag_ne_zero (fun i => (ψ i g₀ : C)) (r g₀) hu (by rw [← Matrix.charpoly_map, hc])
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ h1 h4
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have h5 := h2 (MonoidAlgebra.of C H s) i j hij
    rw [MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i j
    rw [h5, mul_zero, zero_mul] at h6
    exact h6
  · have h5 := h3 (MonoidAlgebra.of C H s) i
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i i
    rw [h5, mul_smul_comm, smul_mul_assoc, hg] at h6
    refine h6.trans ?_
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def sg (K : Type) [CommRing K] (j : ZMod 2) : K := (-1) ^ j.val

def pw (a b : Fin 3) : ZMod 2 := ((w 3 a - w 3 b : ℤ) : ZMod 2)

def adp (K : Type) [CommRing K] (j : ZMod 2) : Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := {X | ∀ a b, pw a b ≠ j → X a b = 0}
  add_mem' h h' a b e := by simp [h a b e, h' a b e]
  zero_mem' _ _ _ := rfl
  smul_mem' c X h a b e := by simp [h a b e]

def prp (K : Type) [CommRing K] (j : ZMod 2) : Matrix (Fin 3) (Fin 3) K →ₗ[K] adp K j where
  toFun X := ⟨Matrix.of fun a b => if pw a b = j then X a b else 0, fun a b e => by simp [e]⟩
  map_add' X Y := Subtype.ext (by ext a b; by_cases e : pw a b = j <;> simp [e])
  map_smul' c X := Subtype.ext (by ext a b; by_cases e : pw a b = j <;> simp [e])

def evp {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) : Submodule O R where
  carrier := {x | σ x = sg R j * x}
  add_mem' {x y} (h : _ = _) (h' : _ = _) := show _ = _ by rw [map_add (f := _), h, h', mul_add]
  zero_mem' := show _ = _ by simp
  smul_mem' c x (h : _ = _) := show _ = _ by rw [map_smul, h, mul_smul_comm]

section Pres

variable (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R)

def derp (j : ZMod 2) : Submodule (ResidueField O) (R →ₗ[O] ResidueField O) :=
  PtDer (res O R) (ResidueField O) ⊓
    { carrier := {D | ∀ x, D (σ x) = sg (ResidueField O) j * D x}
      add_mem' := fun h h' x => by simp only [LinearMap.add_apply, h x, h' x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c D h x => by simp only [LinearMap.smul_apply, h x, smul_eq_mul, mul_left_comm] }

structure GPres where
  a : ℕ
  g : ℕ
  p : MvPowerSeries (Fin a ⊕ Fin g) O →ₐ[O] R
  κ : Type
  [fin : Fintype κ]
  f : κ → MvPowerSeries (Fin a ⊕ Fin g) O
  wf : κ → ZMod 2
  surj : Function.Surjective p
  var : ∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal R
  part : ∀ j, (wtPart O (Space.Loc.par a g) j).map p.toLinearMap = evp σ j
  homog : IsHomog O (Space.Loc.par a g) (RingHom.ker p)
  min : ∀ h ∈ RingHom.ker p, ∀ s, MvPowerSeries.coeff (Finsupp.single s 1) h ∈ maximalIdeal O
  hf : ∀ u, f u ∈ wtPart O (Space.Loc.par a g) (wf u)
  ker : RingHom.ker p = Ideal.span (Set.range f)
  indep : ∀ c : κ → O, ∑ u, c u • f u ∈ maximalIdeal (MvPowerSeries (Fin a ⊕ Fin g) O) * RingHom.ker p →
    ∀ u, c u ∈ maximalIdeal O

attribute [instance] GPres.fin

end Pres

structure Space.Loc.IsInv {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {F : Frame l (ResidueField O)} {S : Space O F 3} {x : Ideal S.A} (L : S.Loc x) (σ : L.R →ₐ[L.O'] L.R) : Prop where
  sq : ∀ y, σ (σ y) = y
  ent : ∀ g a b, L.ρ.r g a b ∈ evp σ (pw a b)
  base : ∀ y : S.B, L.b y ∈ evp σ 0

end UpperTheory.V.Fr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
noncomputable section

namespace UpperTheory.V.Fr.Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (M : Type) [AddCommGroup M] [Module k M]

def strY : Submodule k (F.G0 → M) where
  carrier := {y | IsLocallyConstant y ∧ (∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h) ∧
    y F.g0 = y (F.star F.g0) ∧
    (∀ v, ∃ α : M, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α) ∧
    ∀ v, ∃ β : M, ∀ s, y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨a1.add b1, fun g h => ?_, by simp [a3, b3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
    · obtain ⟨α, h⟩ := a5 v
      obtain ⟨α', h'⟩ := b5 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, rfl, fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, by simp [a3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩
    · obtain ⟨α, h⟩ := a5 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

def strS : Submodule k (F.G0 → M) where
  carrier := {a | IsLocallyConstant a ∧
    (∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + (((F.Ψ g)⁻¹ : kˣ) : k) • a h) ∧ (∀ g, a (F.star g) = a g) ∧
    ∀ v, ∃ γ : M, ∀ s, a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun g h => ?_, fun g => by simp [a3, b3], fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, fun _ => rfl, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, fun g => by simp [a3], fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

variable {F M} {M' : Type} [AddCommGroup M'] [Module k M']

theorem strY_map (f : M →ₗ[k] M') {y : F.G0 → M} (hy : y ∈ F.strY M) : (fun g => f (y g)) ∈ F.strY M' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  refine ⟨h1.comp f, fun g h => ?_, congrArg f h3, fun v => ?_, fun v => ?_⟩
  · simp only [h2, map_add (f := _), map_smul]
  · obtain ⟨α, hα⟩ := h4 v
    exact ⟨f α, fun s => by simp only [hα, map_smul]⟩
  · obtain ⟨β, hβ⟩ := h5 v
    exact ⟨f β, fun s => by simp only [hβ, map_smul]⟩

theorem strS_map (f : M →ₗ[k] M') {a : F.G0 → M} (ha : a ∈ F.strS M) : (fun g => f (a g)) ∈ F.strS M' := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  refine ⟨h1.comp f, fun g h => ?_, fun g => congrArg f (h3 g), fun v => ?_⟩
  · simp only [h2, map_add (f := _), map_smul]
  · obtain ⟨γ, hγ⟩ := h4 v
    exact ⟨f γ, fun s => by simp only [hγ, map_smul]⟩

end UpperTheory.V.Fr.Frame
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AddMulSelfEqOfOrthogonalIdempotents
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents {C K : Type} [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (hn : n = 2 ∨ n = 3) (A : Subalgebra C (Matrix (Fin n) (Fin n) K)) (h2 : IsUnit (2 : C))
    (hY : Matrix.diagonal (fun i => (w n i : K)) ∈ A) (i : Fin n) : Matrix.single i i (1 : K) ∈ A := by
  have key : ∀ M : Matrix (Fin n) (Fin n) K, (2 : C) • M ∈ A → M ∈ A := by
    intro M hM
    have := A.smul_mem hM (↑h2.unit⁻¹ : C)
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  have hYY := A.mul_mem hY hY
  rcases hn with rfl | rfl
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 2) 0 (1 : K) = 1 + Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.add_mem A.one_mem hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 2) 1 (1 : K) = 1 - Matrix.diagonal (fun i => (w 2 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem A.one_mem hY
      rw [← e] at h
      exact h
  · apply key
    fin_cases i
    · have e : (2 : C) • Matrix.single (0 : Fin 3) 0 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) +
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.add_mem hYY hY
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (1 : Fin 3) 1 (1 : K) =
          (2 : C) • (1 - Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K))) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.one_apply, Matrix.single_apply] <;> norm_num
      have h := A.smul_mem (A.sub_mem A.one_mem hYY) (2 : C)
      rw [← e] at h
      exact h
    · have e : (2 : C) • Matrix.single (2 : Fin 3) 2 (1 : K) =
          Matrix.diagonal (fun i => (w 3 i : K)) * Matrix.diagonal (fun i => (w 3 i : K)) -
            Matrix.diagonal (fun i => (w 3 i : K)) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [w, two_smul, Matrix.single_apply] <;> norm_num
      have h := A.sub_mem hYY hY
      rw [← e] at h
      exact h

theorem UpperTheory.V.Fr.idem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F n K), Integral O C ρ → ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range ρ.r) := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ ρ hI i
  haveI : CharP (ResidueField O) l := IsCoef.char
  have hunit : ∀ x : C, res O C x ≠ 0 → IsUnit x := by
    intro x hx
    by_contra h
    exact hx ((res_eq_zero_iff O C x).2 ((IsLocalRing.mem_maximalIdeal x).2 h))
  have h2 : IsUnit (2 : C) := by
    apply hunit
    rw [map_ofNat]
    intro h0
    have h0' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h0'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).1 h0')
  obtain ⟨ζ, hζr, hζ⟩ := hI.ze
  have hζu : IsUnit ζ := by
    apply hunit
    rw [hζr]
    intro h0
    apply hF.baseSubgroup_spec
    rw [sub_eq_zero] at h0
    try simp only [← Units.val_inv_eq_inv_val] at h0
    have hx : F.Ψ ↑F.g0 = (F.Ψ ↑F.g0)⁻¹ := Units.ext h0
    calc F.Ψ ↑F.g0 ^ 2 = F.Ψ ↑F.g0 * F.Ψ ↑F.g0 := sq _
      _ = F.Ψ ↑F.g0 * (F.Ψ ↑F.g0)⁻¹ := by rw [← hx]
      _ = 1 := mul_inv_cancel _
  have hD : ρ.r F.g0 - ρ.r (F.star F.g0) = ζ • Matrix.diagonal (fun i => (w n i : K)) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, Algebra.smul_def, hζ a]
      ring
    · rw [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab, smul_zero]
      exact ρ.diag a b hab
  have hspan : (Algebra.adjoin C (Set.range ρ.r)).toSubmodule = Submodule.span C (Set.range ρ.r) := by
    rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq]
  have hmem : ρ.r F.g0 - ρ.r (F.star F.g0) ∈ Submodule.span C (Set.range ρ.r) :=
    Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hY : Matrix.diagonal (fun i => (w n i : K)) ∈ Algebra.adjoin C (Set.range ρ.r) := by
    rw [← Subalgebra.mem_toSubmodule, hspan]
    have h := Submodule.smul_mem _ (↑hζu.unit⁻¹ : C) hmem
    rwa [hD, smul_smul, IsUnit.val_inv_mul, one_smul] at h
  rw [← hspan, Subalgebra.mem_toSubmodule]
  exact UpperTheory.V.Fr.add_mul_self_eq_of_orthogonal_idempotents hn _ h2 hY i
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_of_rel {R D : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    (T : Subalgebra R D) {x c d : D} {p : ℕ} (hp : 0 < p) (hc : c ∈ T) (hd : d ∈ T) (h0 : c ≠ 0)
    (h : x ^ p * c = d) : IsAlgebraic T x := by
  refine IsAlgebraic.of_pow hp ?_
  have hc' : (⟨c, hc⟩ : T) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine IsAlgebraic.of_smul (y := (⟨c, hc⟩ : T)) (mem_nonZeroDivisors_of_ne_zero hc') ?_
  have : (⟨c, hc⟩ : T) • x ^ p = algebraMap T D ⟨d, hd⟩ := by
    rw [Algebra.smul_def, mul_comm]; exact h
  rw [this]
  exact isAlgebraic_algebraMap _

private theorem trdeg_le_one {R D ι : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    [FaithfulSMul R D] (x : ι → D) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R D))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ≠ 0) (hb0 : x b ≠ 0) : Algebra.trdeg R D ≤ 1 := by
  set T : Subalgebra R D := Algebra.adjoin R {x a} with hT
  have haT : x a ∈ T := Algebra.subset_adjoin rfl
  have hR : ∀ {y}, y ∈ Set.range (algebraMap R D) → y ∈ T := by
    rintro _ ⟨r, rfl⟩; exact T.algebraMap_mem r
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hb.le)
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hq' : wt b = -q := by omega
  have key : ∀ i, IsAlgebraic T (x i) := by
    intro i
    rcases le_total (wt i) 0 with h | h
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h)
      have hm' : wt i = -m := by omega
      exact alg_of_rel T hp0 (pow_mem haT m) (hR (h0 i a p m (by rw [hm', hp]; ring))) (pow_ne_zero _ ha0) rfl
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
      have h1 := hR (h0 i b q m (by rw [hm, hq']; ring))
      have h2 := hR (h0 b a p q (by rw [hp, hq']; ring))
      refine alg_of_rel T (mul_pos hq0 hp0) (pow_mem h2 m) (mul_mem (pow_mem h1 p) (pow_mem haT (q * m)))
        (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ ha0))) (by ring)
  have hall : Algebra.IsAlgebraic T D := ⟨fun y => by
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact key i
    | algebraMap r => exact isAlgebraic_algebraMap (⟨_, T.algebraMap_mem r⟩ : T)
    | add y z _ _ h1 h2 => exact h1.add h2
    | mul y z _ _ h1 h2 => exact h1.mul h2⟩
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk R ({x a} : Set D)

private theorem trdeg_quot_le_one {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (η : Ideal A) (hη : η.IsPrime) (x : ι → A) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R A))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ∉ η) (hb0 : x b ∉ η) :
    Algebra.trdeg (R ⧸ η.comap (algebraMap R A)) (A ⧸ η) ≤ 1 := by
  refine trdeg_le_one (fun s => Ideal.Quotient.mk η (x s)) wt ?_ ?_ ha hb
    (fun e => ha0 (Ideal.Quotient.eq_zero_iff_mem.1 e)) (fun e => hb0 (Ideal.Quotient.eq_zero_iff_mem.1 e))
  · rw [eq_top_iff]
    intro y hy
    clear hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (Ideal.Quotient.mk (η.comap (algebraMap R A)) r)
    | add y z _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | mul y z _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
  · intro i j p q h
    obtain ⟨r, hr⟩ := h0 i j p q h
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [← map_pow, ← map_pow, ← map_mul, ← hr]
    rfl

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

theorem UpperTheory.V.Fr.fibre :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η : Ideal S.A, η.IsPrime → S.u.OffTri η → S.td η ≤ 1 := by
  intro l _ O _ _ _ _ F C₀ n _ _ S η hη hoff
  obtain ⟨h1, h2⟩ := hoff
  have hb : ∃ g i j, j < i ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h1 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  have ha : ∃ g i j, i < j ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h2 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  obtain ⟨g, i, j, hij, hg⟩ := ha
  obtain ⟨g', i', j', hij', hg'⟩ := hb
  refine trdeg_quot_le_one (ι := F.G0 × Fin n × Fin n) η hη (fun s => S.u.r s.1 s.2.1 s.2.2)
    (fun s => w n s.2.1 - w n s.2.2) ?_ ?_ (a := (g, i, j)) (b := (g', i', j'))
    (sub_pos.2 (w_lt hij)) (sub_neg.2 (w_lt hij')) hg hg'
  · rw [eq_top_iff]
    rintro ⟨y, hy⟩ hy'
    clear hy'
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : S.B)
      · exact Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O S.B r)
    | add y z hy hz h1 h2 => exact add_mem h1 h2
    | mul y z hy hz h1 h2 => exact mul_mem h1 h2
  · intro s t p q h
    have hm : S.ρ.r s.1 s.2.1 s.2.2 ^ p * S.ρ.r t.1 t.2.1 t.2.2 ^ q ∈ S.ρ.mon 0 :=
      ⟨List.replicate p s ++ List.replicate q t, by simpa using h, by simp⟩
    exact ⟨⟨_, S.mon_mem hm⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

section Lau

variable {C K : Type} [CommRing C] [CommRing K] [Algebra C K] (P : ℤ → Submodule C K) [SetLike.GradedMonoid P]

theorem coeff_mul_mem {p q : AddMonoidAlgebra K ℤ} (j : ℤ) (M : Submodule C K)
    (h : ∀ a b, a + b = j → p.coeff a * q.coeff b ∈ M) : (p * q).coeff j ∈ M := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  dsimp only
  split_ifs with e
  · exact h a b e
  · exact zero_mem _

def lauSub : Subalgebra C (AddMonoidAlgebra K ℤ) where
  carrier := {p | ∀ j, p.coeff j ∈ P j}
  mul_mem' {p q} hp hq j := coeff_mul_mem j _ fun a b e => e ▸ SetLike.mul_mem_graded (hp a) (hq b)
  add_mem' {p q} hp hq j := add_mem (hp j) (hq j)
  algebraMap_mem' c j := by
    classical
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with e
    · subst e
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.one_mem_graded P)
    · exact zero_mem _

theorem single_mem_lauSub {j : ℤ} {x : K} (hx : x ∈ P j) : AddMonoidAlgebra.single j x ∈ lauSub P := by
  classical
  intro i
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with e
  · subst e
    exact hx
  · exact zero_mem _

variable [IsLocalRing C]

structure HasVertex : Prop where
  zero : ∀ x ∈ P 0, ∃ c : C, algebraMap C K c = x
  cross : ∀ j, j ≠ 0 → ∀ x ∈ P j, ∀ y ∈ P (-j), ∃ c ∈ maximalIdeal C, algebraMap C K c = x * y


variable {P} in
def vertex (h : HasVertex P) : Ideal (lauSub P) where
  carrier := {p | ∃ c ∈ maximalIdeal C, algebraMap C K c = p.1.coeff 0}
  add_mem' := by
    rintro p q ⟨c, h1, h2⟩ ⟨d, h3, h4⟩
    exact ⟨c + d, add_mem h1 h3, by rw [map_add (f := _), h2, h4]; rfl⟩
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  smul_mem' := by
    rintro q p ⟨c, h1, h2⟩
    refine Submodule.mem_map.1 (coeff_mul_mem (p := q.1) (q := p.1) 0
      (Submodule.map (Algebra.linearMap C K) (maximalIdeal C)) fun a b e => Submodule.mem_map.2 ?_)
    by_cases h0 : a = 0
    · subst h0
      rw [zero_add] at e
      subst e
      obtain ⟨d, hd⟩ := h.zero _ (q.2 0)
      exact ⟨d * c, Ideal.mul_mem_left _ _ h1, by rw [← hd, ← h2, ← map_mul]; rfl⟩
    · obtain rfl : b = -a := by omega
      exact h.cross a h0 _ (q.2 a) _ (p.2 _)

variable {P} in
theorem mem_vertex (h : HasVertex P) {p : lauSub P} :
    p ∈ UpperTheory.V.Fr.vertex (P := P) h ↔
      ∃ c ∈ maximalIdeal C, algebraMap C K c = p.1.coeff 0 := Iff.rfl

end Lau

section Part

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} (C : Type) [CommRing C] {K : Type}
  [CommRing K] [Algebra C K] (ρ : NRep F n K)

def NRep.part (j : ℤ) : Submodule C K := Submodule.span C (ρ.mon j)

instance : SetLike.GradedMonoid (ρ.part C) where
  one_mem := Submodule.subset_span ⟨[], by simp, by simp⟩
  mul_mem i j x y hx hy := by
    have := Submodule.mul_mem_mul hx hy
    rw [NRep.part, NRep.part, Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨L, h1, rfl⟩, _, ⟨M, h2, rfl⟩, rfl⟩
    exact ⟨L ++ M, by simp only [List.map_append, List.sum_append, h1, h2], by simp⟩

theorem NRep.r_mem_part (g : F.G0) (i j : Fin n) : ρ.r g i j ∈ ρ.part C (w n i - w n j) :=
  Submodule.subset_span ⟨[(g, i, j)], by simp, by simp⟩

end Part

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

structure IsVertexRing (C : Type) [CommRing C] [IsLocalRing C] {D : Type} [CommRing D] [Algebra C D] (𝔪 : Ideal D) :
    Prop where
  noeth : IsNoetherianRing D
  inj : Function.Injective (algebraMap C D)
  sep : ⨅ N : ℕ, 𝔪 ^ N = ⊥
  comap : 𝔪.comap (algebraMap C D) = maximalIdeal C
  surj : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ 𝔪

structure IsModel (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra C D]
    (𝔪 : Ideal D) (ρ : NRep F n D) : Prop where
  cont : ρ.Cont 𝔪
  off : ∀ g i j, i ≠ j → ρ.r g i j ∈ 𝔪
  dg : ∀ g i, ∃ c : C, algebraMap C D c = ρ.r g i i ∧
    res O C c = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  psi : ∀ v i g, ∃ c : C, algebraMap C D c = ρ.ψ v i g ∧
    res O C c = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O)
  mon : ∀ x ∈ ρ.mon 0, ∃ c : C, algebraMap C D c = x

end UpperTheory.V.Fr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimQuotientBound
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.krull_dim_quotient_bound :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I K : Ideal R) {ι : Type} [Fintype ι] (t : ι → R), (∀ a, t a ∈ maximalIdeal R) → (∀ P : Ideal R, P.IsPrime → I ≤ P → (∀ a, t a ∈ P) → K ≤ P) → ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ K) + (Fintype.card ι : ℕ) := by
  intro R _ _ _ I K ι _ t ht hP
  classical
  have hjac : (Set.range fun a => Ideal.Quotient.mk I (t a)) ⊆ Ring.jacobson (R ⧸ I) := by
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Ring.jacobson_eq_sInf_isMaximal, Ideal.mem_sInf]
    intro m hm
    have hm' : m.IsMaximal := hm
    have h1 : (m.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 := IsLocalRing.eq_maximalIdeal h1
    have h3 : t a ∈ m.comap (Ideal.Quotient.mk I) := h2 ▸ ht a
    exact h3
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hjac
  have hspan : Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a))
      = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have h2 : ringKrullDim ((R ⧸ I) ⧸ Ideal.span (Set.range fun a => Ideal.Quotient.mk I (t a)))
      = ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) := by
    rw [hspan]
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)
  have h3 : ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) ≤ ringKrullDim (R ⧸ K) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient]
    have hsub : PrimeSpectrum.zeroLocus (R := R) ((I ⊔ Ideal.span (Set.range t) : Ideal R) : Set R)
        ⊆ PrimeSpectrum.zeroLocus (R := R) (K : Set R) := by
      intro p hp
      have hp' : I ⊔ Ideal.span (Set.range t) ≤ p.asIdeal := hp
      refine hP p.asIdeal p.isPrime (le_sup_left.trans hp') fun a => ?_
      exact (le_sup_right.trans hp') (Ideal.subset_span ⟨a, rfl⟩)
    exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) fun _ _ h => h
  have h4 : (Set.range fun a => Ideal.Quotient.mk I (t a)).encard ≤ (Fintype.card ι : ℕ) := by
    rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    simp
  refine h1.trans ?_
  rw [h2]
  refine add_le_add h3 ?_
  exact_mod_cast h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K]

def cor : Fin 2 → Fin 3 := ![0, 2]

theorem w_cor (i : Fin 2) : w 3 (cor i) = w 2 i := by
  fin_cases i <;> rfl

structure IsCorner (ρ : NRep F 3 K) (σ : NRep F 2 K) : Prop where
  odd : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0
  r : ∀ g i j, σ.r g i j = ρ.r g (cor i) (cor j)
  ψ : ∀ v i g, σ.ψ v i g = ρ.ψ v (cor i) g
  mid : ∀ v g, ρ.r (F.loc0 v g) 1 1 = ρ.ψ v 1 g

def CornerUnits (ρ : NRep F 3 K) : Prop :=
  ∀ v, ∃ g, IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 0 g) ∧ IsUnit (ρ.r (F.loc0 v g) 1 1 - ρ.ψ v 2 g) ∧
    IsUnit ((ρ.r (F.loc0 v g) 0 0 - ρ.ψ v 1 g) * (ρ.r (F.loc0 v g) 2 2 - ρ.ψ v 1 g) -
      ρ.r (F.loc0 v g) 0 2 * ρ.r (F.loc0 v g) 2 0)

theorem mid_mul (ρ : NRep F 3 K) (h : ∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) (g g' : F.G0) :
    ρ.r (g * g') 1 1 = ρ.r g 1 1 * ρ.r g' 1 1 := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, h g 1 0 (by decide), h g 1 2 (by decide)]
  simp

end UpperTheory.V.Fr
end
end
