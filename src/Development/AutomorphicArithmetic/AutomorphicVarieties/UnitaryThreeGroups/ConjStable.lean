module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GRepresents
noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Emb

variable {m : ℕ} {R : Type*} [CommRing R]

def emb : GG (m := m) (R := R) →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R where
  toFun x := if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : GL (Fin m) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : GL (Fin m) R) 0
  map_one' := by
    have h : theta (1 : GL (Fin m) R) = 1 := map_one (thetaAut (m := m) (R := R))
    simp [GG.mat, h]
  map_mul' x y := by
    have h : ((-1 : ℤˣ) = 1) = False := by decide
    obtain ⟨a, s⟩ := x
    obtain ⟨b, t⟩ := y
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
      simp [GG.mat, h, theta_mul, theta_theta, Matrix.fromBlocks_multiply]

def wt6 : Fin 3 ⊕ Fin 3 → ℤ := Sum.elim wt1 wt1

end Emb

section Lift

variable (O : Type) [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]

def barChar (Ψ : Γ →* Oˣ) : Γ →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp Ψ

variable (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)

def rbar : Γ →* GG (m := 3) (R := ResidueField O) := r0 η (barChar O Ψ)

@[ext] structure GLift (R : Type) [CommRing R] [Algebra O R] [IsCO O R] where
  hom : Γ →* GG (m := 3) (R := R)
  cont : ∀ a b, AdicCont (maximalIdeal R) fun g => (hom g).mat a b
  red : ∀ g, GG.map (res O R : R →+* ResidueField O) (hom g) = rbar O η Ψ g

variable {O η Ψ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']

theorem GLift.hasMult (r : GLift O η Ψ R) : HasMult η r.hom := fun g => congrArg SemidirectProduct.right (r.red g)

theorem GG.map_map {m : ℕ} {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C)
    (x : GG (m := m) (R := A)) : GG.map f' (GG.map f x) = GG.map (f'.comp f) x := rfl

def GLift.map (f : R →ₐ[O] R') (r : GLift O η Ψ R) : GLift O η Ψ R' where
  hom := (GG.map (f : R →+* R')).comp r.hom
  cont a b N := by
    have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
      refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
      show f y ∈ maximalIdeal R'
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    exact (r.cont a b N).comp (Ideal.quotientMap _ (f : R →+* R') hle)
  red g := by
    have e : (res O R' : R' →+* ResidueField O).comp (f : R →+* R') = (res O R : R →+* ResidueField O) :=
      RingHom.ext fun x => res_map (O := O) (R := R) (R' := R') f x
    rw [MonoidHom.comp_apply, GG.map_map, e, r.red]

def GLift.comap {H : Type} [Group H] [TopologicalSpace H] (φ : H →* Γ) (hφ : Continuous φ) (r : GLift O η Ψ R) :
    GLift O (η.comp φ) (Ψ.comp φ) R where
  hom := r.hom.comp φ
  cont a b N := (r.cont a b N).comp_continuous hφ
  red g := r.red (φ g)


variable (O η Ψ) in
def GCond (O : Type) [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) : Type 1 := ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], GLift O η Ψ R → Prop


variable (O η Ψ) in
def GCond.noCondition (O : Type) [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) : GCond O η Ψ := fun _ _ _ _ _ => True

def GRepresents (P : GCond O η Ψ) (r : GLift O η Ψ R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'],
    (∀ f : R →ₐ[O] R', P R' (r.map f)) ∧ ∀ r' : GLift O η Ψ R', P R' r' → ∃! f : R →ₐ[O] R', r.map f = r'

structure Univ (P : GCond O η Ψ) : Type 1 where
  R : Type
  [cr : CommRing R]
  [al : Algebra O R]
  [co : IsCO O R]
  r : GLift O η Ψ R
  rep : GRepresents P r

attribute [instance] Univ.cr Univ.al Univ.co

def OnI (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) : GCond O η Ψ :=
  fun R _ _ _ r => ∃ f : U.R →ₐ[O] R, U.r.map f = r ∧ I ≤ RingHom.ker f

def Kills (N : Set Γ) : GCond O η Ψ := fun _ _ _ _ r => ∀ g ∈ N, r.hom g = 1

def BoxCond (N : Set Γ) {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Γ) (hι : Continuous ι)
    (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R) : GCond O η Ψ :=
  fun R _ _ _ r => Kills N R r ∧ OnI U I R (r.comap ι hι)

def NormCond (c g₁ : Γ) (P : GCond O η Ψ) : GCond O η Ψ :=
  fun R _ _ _ r => Normalised c g₁ r.hom ∧ P R r

end Lift

section Points

variable (O : Type) [CommRing O] {Γ R : Type} [Group Γ] [CommRing R] [Algebra O R]

def entAlg (r : Γ →* GG (m := 3) (R := R)) : Subalgebra O R := Algebra.adjoin O {x | ∃ g a b, x = (r g).mat a b}

def entMon (r : Γ →* GG (m := 3) (R := R)) (j : ℤ) : Set R :=
  {x | ∃ L : List (Γ × Fin 3 × Fin 3), (L.map fun s => wt s.2.1 s.2.2).sum = j ∧
    x = (L.map fun s => (r s.1).mat s.2.1 s.2.2).prod}

def weightZeroSubalgebra (r : Γ →* GG (m := 3) (R := R)) : Subalgebra O R := Algebra.adjoin O (entMon r 0)

variable {O} {κ : Type} [CommRing κ] [Algebra O κ]

def push (f : R →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) : Γ →* GG (m := 3) (R := κ) := (GG.map (f : R →+* κ)).comp r

def IsPush {A : Subalgebra O R} (ξ : A →ₐ[O] κ) (r : Γ →* GG (m := 3) (R := R)) (r' : Γ →* GG (m := 3) (R := κ)) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ ∀ a b, ∃ h : (r g).mat a b ∈ A, (r' g).mat a b = ξ ⟨_, h⟩

def tanCoc (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG (m := 3) (R := R)) (g : Γ) : Matrix (Fin 3) (Fin 3) κ :=
  ((r g).mat.map fun x => (F x).snd) *
    (((r g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map fun x => (F x).fst

def dualFst (F : R →ₐ[O] DualNumber κ) : R →ₐ[O] κ := (TrivSqZeroExt.fstHom O κ κ).comp F

def Rigid (r : Γ →* GG (m := 3) (R := R)) (f : R →ₐ[O] κ) : Prop :=
  ∀ F : R →ₐ[O] DualNumber κ, dualFst F = f → ∃ X, tanCoc F r = cob (push f r) X

def RigidWt (j : ℤ) (r : Γ →* GG (m := 3) (R := R)) (f : R →ₐ[O] κ) : Prop :=
  ∀ F : R →ₐ[O] DualNumber κ, dualFst F = f → (∀ g, tanCoc F r g ∈ gw (R := κ) j) → ∃ X, tanCoc F r = cob (push f r) X

def IsLocPt [IsLocalRing R] {κ : Type} [NormedField κ] [Algebra O κ] (f : R →ₐ[O] κ) : Prop :=
  ∀ x ∈ maximalIdeal R, ‖f x‖ < 1

end Points

section Base

variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)

def baseLift (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) : GLift O η Ψ O where
  hom := r0 η Ψ
  cont a b := by
    by_cases h : a = b
    · subst h
      simpa [GG.mat, tor_val] using hΨ (wt1 a)
    · intro N
      simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ h]
      exact IsLocallyConstant.const _
  red g := by
    have e : ∀ x : O, res O O x = residue O x := fun x => (res O O).commutes x
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    show (tor (R := O) (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (res O O) = tor (R := ResidueField O) (barChar O Ψ g)
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [e]
    exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

end Base

end UpperTheory.V.U3
end
end

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg MvPowerSeries

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {H : Type} [Group H] [TopologicalSpace H]
  {η : H →* ℤˣ} {Ψ : H →* Oˣ} (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R)

def IsBase {Γ R : Type} [Group Γ] [CommRing R] [Algebra O R] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ) (r : Γ →* GG (m := 3) (R := R))
    (x : R →ₐ[O] O) : Prop := push x r = r0 η Ψ

def ConjStable : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r r' : GLift O η Ψ R) (h : GL (Fin 3) R),
    CongOne (maximalIdeal R) h → r'.hom = conjBy h r.hom → OnI U I R r → OnI U I R r'

def locDims (j : ℤ) : ℕ :=
  if j = -2 then 1 else if j = -1 then 2 else if j = 0 then 3 else if j = 1 then 4 else if j = 2 then 2 else 0

structure LocChart (x : U.R →ₐ[O] O) {τ : Type} (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O)) :
    Prop where
  ker : RingHom.ker φ = I
  graded : ∀ g a b, φ ((U.r.hom g).mat a b) ∈ wtPart (FractionRing O) w (wt a b)
  const : ∀ f, constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)
  onto : ∀ i, ∃ f : U.R, coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧ ∀ i', i' ≠ i → coeff (Finsupp.single i' 1) (φ f) = 0
  inj : ∀ f, x f = 0 → (∀ i, coeff (Finsupp.single i 1) (φ f) = 0) →
    ∃ c : O, c ≠ 0 ∧ c • f ∈ RingHom.ker x ^ 2 ⊔ I

structure LocGood : Prop where
  conj : ConjStable U I
  chart : ∃ (x : U.R →ₐ[O] O) (τ : Type) (_ : Fintype τ) (w : τ → ℤ) (φ : U.R →ₐ[O] MvPowerSeries τ (FractionRing O)),
    IsBase η Ψ U.r.hom x ∧ LocChart U I x w φ ∧ ∀ j, Nat.card {i // w i = j} = locDims j

end Local

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {Γ H : Type} [Group Γ] [TopologicalSpace Γ]
  [Group H] [TopologicalSpace H] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {c g₁ : Γ}


variable (N hι U I c g₁) in
abbrev SRing : Type 1 := Univ (NormCond c g₁ (BoxCond N ι hι U I))

def EntWt {G R Q : Type} [Group G] [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (r : G →* GG (m := 3) (R := R)) (j : ℤ)
    (D : R →ₗ[O] Q) : Prop := ∀ g a b, wt a b ≠ j → D ((r g).mat a b) = 0

structure Model (S : SRing (N := N) (hι := hι) (U := U) (I := I) (c := c) (g₁ := g₁)) (K : Type) [NormedField K] [Algebra O K] : Type 1 where
  A : Type
  [cr : CommRing A]
  [al : Algebra O A]
  𝒜 : ℤ → Submodule O A
  [gr : GradedAlgebra 𝒜]
  x : A →ₐ[O] O
  wring : IsWRing 𝒜 x
  r : ℕ
  s : ℕ
  r' : ℕ
  s' : ℕ
  m : ℕ
  Q : Eqns 𝒜 x r s r' s' m
  one_le : 1 ≤ r
  smooth : SmoothPt 𝒜 x (mDims r s r' s' m)
  q : A →ₐ[O] S.R
  ker_q : RingHom.ker q = Q.ideal
  x₀ : S.R →ₐ[O] O
  base : IsBase η Ψ S.r.hom x₀
  x₀_q : x₀.comp q = x
  ent : ∀ g a b, ∃ f ∈ 𝒜 (wt a b), q f = (S.r.hom g).mat a b
  dense : ∀ j, ∀ f ∈ 𝒜 j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon S.r.hom j), q f - y ∈ maximalIdeal S.R ^ n
  pts : M2 𝒜 Q.ideal → ∀ ξ : A →ₐ[O] K, OnS Q.ideal ξ →
    ∃ (t : Kˣ) (f : S.R →ₐ[O] K), IsLocPt f ∧ act 𝒜 (tz t) ξ = f.comp q
  der : M2 𝒜 Q.ideal → ∀ f : S.R →ₐ[O] K, IsLocPt f → ∀ D ∈ PtDer (f.comp q) K, (∀ y ∈ Q.ideal, D y = 0) →
    ∃ F : S.R →ₐ[O] DualNumber K, dualFst F = f ∧ ∀ y, (F (q y)).snd = D y
  lift : ∀ a : O, a ≠ 0 → ∀ D ∈ PtDer x₀ (O ⧸ Ideal.span {a}), EntWt S.r.hom (-1) D →
    ∀ xl : U.R →ₐ[O] O, IsBase (η.comp ι) (Ψ.comp ι) U.r.hom xl → ∀ D₁ ∈ PtDer xl O, (∀ y ∈ I, D₁ y = 0) →
    EntWt U.r.hom (-1) D₁ →
    (∀ h a' b', Ideal.Quotient.mk _ (D₁ ((U.r.hom h).mat a' b')) = D ((S.r.hom (ι h)).mat a' b')) →
    ∃ D' ∈ PtDer x O, HasWt 𝒜 (-1) D' ∧ ∀ f, D (q f) = Ideal.Quotient.mk _ (D' f)

attribute [instance] Model.cr Model.al Model.gr

def Model.len {S : SRing (N := N) (hι := hι) (U := U) (I := I) (c := c) (g₁ := g₁)} {K : Type} [NormedField K] [Algebra O K] (M : Model S K) : ℕ∞ :=
  cotLen M.x M.𝒜 (-1) M.Q.F


variable (η) in
def TwoPt {R K : Type} [CommRing R] [Algebra O R] [IsLocalRing R] [NormedField K] [Algebra O K] (r : Γ →* GG (m := 3) (R := R))
    (f : R →ₐ[O] K) : Prop := IsLocPt f ∧ ¬ Upper η (push f r) ∧ ¬ Lower η (push f r)

def CoversPt {R K : Type} [CommRing R] [Algebra O R] [IsLocalRing R] [NormedField K] [Algebra O K] (η : Γ →* ℤˣ)
    (r : Γ →* GG (m := 3) (R := R)) (T : Finset (R →ₐ[O] K)) : Prop :=
  (∀ f ∈ T, TwoPt (η := η) r f) ∧ ∀ f : R →ₐ[O] K, TwoPt (η := η) r f → ∃ f' ∈ T, ∃ t : Kˣ, push f r = conjBy (tor (R := K) t) (push f' r)

def trDiff {R K : Type} [CommRing R] [Algebra O R] [CommRing K] [Algebra O K] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)
    (r : Γ →* GG (m := 3) (R := R)) (σ : Γ) (f : R →ₐ[O] K) : K :=
  f (r σ).mat.trace - algebraMap O K (r0 η Ψ σ).mat.trace


variable (η Ψ N ι c g₁) in
def shaCoc (a : O) : Set (Γ → Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})) :=
  {γ | IsLocallyConstant γ ∧ (∀ g, γ g ∈ gw (R := O ⧸ Ideal.span {a}) (-1)) ∧
    IsCoc ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) γ ∧
    NormCoc c g₁ ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) γ ∧ (∀ g ∈ N, γ g = 0) ∧
    ∃ X ∈ gw (R := O ⧸ Ideal.span {a}) (-1), ∀ h,
      γ (ι h) = cob ((GG.map (Ideal.Quotient.mk (Ideal.span {a}))).comp (r0 η Ψ)) X (ι h)}

end Model

end UpperTheory.V.U3
