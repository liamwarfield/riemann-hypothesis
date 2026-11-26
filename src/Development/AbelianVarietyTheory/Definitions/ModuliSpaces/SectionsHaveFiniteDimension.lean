module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}

def SectionsHaveFiniteDimension (p : X ⟶ Sp K) (M : LB X) (r : ℕ) : Prop :=
  ∃ s : Fin r → M.Sec, ∀ t : M.Sec, ∃! a : Fin r → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j

def Vol (p : X ⟶ Sp K) (M : LB X) (g : ℕ) (δ : ℝ) : Prop :=
  ∃ h : ℕ → ℕ, (∀ e, SectionsHaveFiniteDimension p (lbPow M e) (h e)) ∧
    Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds δ)

def VAmp (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) : Prop :=
  (⨆ i, Out.nonzeroLocus (th i) = ⊤) ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (th i)) ∧
    ∃ r : σ → Γ(X, Out.nonzeroLocus (th i)),
      (∀ j k, resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th j).f k) =
        resG X (inf_le_left : Out.nonzeroLocus (th i) ⊓ M.U k ≤ Out.nonzeroLocus (th i)) (r j) *
          resG X (inf_le_right : Out.nonzeroLocus (th i) ⊓ M.U k ≤ M.U k) ((th i).f k)) ∧
      ∀ f : Γ(X, Out.nonzeroLocus (th i)), ∃ F : MvPolynomial σ K,
        f = MvPolynomial.eval₂ (RingHom.comp (p.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r F

def MapDeg (ψ : X ⟶ Y) (D : ℕ) : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
    letI := (ψ.app U).hom.toAlgebra
    Module.rank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = (D : Cardinal)

def TorsBasis (A : Over (Sp K)) [GrpObj A] (k : ℕ) {m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) : Prop :=
  0 < k ∧ (∀ i, pt i ^ k = 1) ∧ ∀ y : Out.baseOver (Sp K) ⟶ A, y ^ k = 1 →
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y

def ActsBy {A : Over (Sp K)} [GrpObj A] {k m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ A)) (f : A ⟶ A)
    (Mat : Matrix (Fin m) (Fin m) (ZMod k)) : Prop :=
  0 < k ∧ ∀ i, pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val)

def FormIs (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) : Prop :=
  IsMonHom s ∧ LBIso (abelian₂ P.A M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ s] P.L)

def SymB {A : Over (Sp K)} [GrpObj A] (M : LB A.left) : Prop := LBIso M (M.pull (GrpObj.inv : A ⟶ A).left)

theorem SectionsHaveFiniteDimension.one_of_isIso (p : X ⟶ Sp K) [IsIso p] {M : LB X} [Unique M.ι] (hU : M.U default = ⊤)
    (hg : ∀ i j, M.g i j = 1) : SectionsHaveFiniteDimension p M 1 := by
  have hb := AbLaw.cst_bijective p hU
  refine ⟨fun _ => ⟨fun _ => 1, fun i j => by rw [hg, map_one, map_one, Units.val_one, _root_.mul_one]⟩, fun t => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 (t.f default)
  refine ⟨fun _ => a, fun j => ?_, fun b hb' => ?_⟩
  · obtain rfl : j = default := Subsingleton.elim _ _
    rw [Fin.sum_univ_one, _root_.mul_one]
    exact ha.symm
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hb' default
    rw [Fin.sum_univ_one, _root_.mul_one] at this
    exact hb.1 (this.symm.trans ha.symm)

theorem SectionsHaveFiniteDimension.trivial_point (K : Type) [Field K] : SectionsHaveFiniteDimension (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 1 :=
  haveI : Unique (Out.Inh.trivLB (Sp K)).ι := inferInstanceAs (Unique PUnit)
  SectionsHaveFiniteDimension.one_of_isIso _ rfl fun _ _ => rfl

theorem Vol.trivial_point (K : Type) [Field K] : Vol (𝟙 (Sp K)) (Out.Inh.trivLB (Sp K)) 0 1 := by
  refine ⟨fun _ => 1, fun e => ?_, by simp⟩
  haveI : Unique (lbPow (Out.Inh.trivLB (Sp K)) e).ι := inferInstanceAs (Unique (PUnit → PUnit))
  exact SectionsHaveFiniteDimension.one_of_isIso _ (top_unique fun _ _ => Set.mem_iInter.2 fun _ => trivial)
    fun i j => Out.Inh.linComb_triv_g _ _ i j

theorem vAmp_iff_veryAmpleBy (p : X ⟶ Sp K) (M : LB X) {m : ℕ} (s : Fin (m + 1) → M.Sec) :
    VAmp p M s ↔ AbLaw.VeryAmpleBy p M s :=
  and_congr Iff.rfl (forall_congr' fun _ => and_congr Iff.rfl (exists_congr fun _ =>
    and_congr Iff.rfl (forall_congr' fun _ => exists_congr fun _ => eq_comm)))

theorem VAmp.comp_surjective {p : X ⟶ Sp K} {M : LB X} {σ τ : Type} {th : σ → M.Sec} (h : VAmp p M th)
    {e : τ → σ} (he : Function.Surjective e) : VAmp p M (fun i => th (e i)) := by
  refine ⟨(he.iSup_comp fun i => Out.nonzeroLocus (th i)).trans h.1, fun i => ⟨(h.2 (e i)).1, ?_⟩⟩
  obtain ⟨r, hr, hF⟩ := (h.2 (e i)).2
  refine ⟨fun j => r (e j), fun j k => hr (e j) k, fun f => ?_⟩
  obtain ⟨F, rfl⟩ := hF f
  obtain ⟨G, rfl⟩ := MvPolynomial.rename_surjective e he F
  exact ⟨G, MvPolynomial.eval₂_rename _ _ _ _⟩

theorem vAmp_comp_equiv (p : X ⟶ Sp K) (M : LB X) {σ τ : Type} (th : σ → M.Sec) (e : τ ≃ σ) :
    VAmp p M (fun i => th (e i)) ↔ VAmp p M th :=
  ⟨fun h => by simpa only [Equiv.apply_symm_apply] using h.comp_surjective e.symm.surjective,
    fun h => h.comp_surjective e.surjective⟩

theorem vAmp_iff_veryAmpleBy_equiv (p : X ⟶ Sp K) (M : LB X) {σ : Type} (th : σ → M.Sec) {m : ℕ}
    (e : Fin (m + 1) ≃ σ) : VAmp p M th ↔ AbLaw.VeryAmpleBy p M (fun i => th (e i)) :=
  (vAmp_comp_equiv p M th e).symm.trans (vAmp_iff_veryAmpleBy p M _)

theorem VAmp.exists_veryAmpleBy {p : X ⟶ Sp K} {M : LB X} {σ : Type} [Finite σ] [Nonempty σ] {th : σ → M.Sec}
    (h : VAmp p M th) : ∃ (m : ℕ) (e : Fin (m + 1) ≃ σ), AbLaw.VeryAmpleBy p M (fun i => th (e i)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero fun hn => (hn ▸ e (Classical.arbitrary σ) : Fin 0).elim0
  exact ⟨m, e.symm, (vAmp_iff_veryAmpleBy_equiv p M th e.symm).1 h⟩

theorem MapDeg.finrank_eq {ψ : X ⟶ Y} {D : ℕ} (h : MapDeg ψ D) (U : Y.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (ψ.app U).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D :=
  (congrArg Cardinal.toNat (h U hU hne)).trans (Cardinal.toNat_natCast D)

theorem MapDeg.of_isFinite {ψ : X ⟶ Y} [IsFinite ψ] {D : ℕ}
    (h : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      letI := (ψ.app U).hom.toAlgebra
      Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D) : MapDeg ψ D := fun U hU hne => by
  letI := (ψ.app U).hom.toAlgebra
  haveI : Nonempty U := hne.to_subtype
  haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  exact (Module.finrank_eq_rank _ _).symm.trans (congrArg _ (h U hU hne))

theorem MapDeg.id_one (X : Scheme.{0}) : MapDeg (𝟙 X) 1 := fun U _ hne =>
  haveI : Nonempty U := hne.to_subtype
  (Module.rank_self Γ(X, U)).trans Nat.cast_one.symm

section Torsion
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}

theorem TorsBasis.pos (h : TorsBasis A k pt) : 0 < k := h.1

theorem TorsBasis.pow_eq_one (h : TorsBasis A k pt) (i : Fin m) : pt i ^ k = 1 := h.2.1 i

theorem TorsBasis.existsUnique (h : TorsBasis A k pt) {y : Out.baseOver (Sp K) ⟶ A} (hy : y ^ k = 1) :
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y := h.2.2 y hy

theorem ActsBy.comp_eq {f : A ⟶ A} {Mat : Matrix (Fin m) (Fin m) (ZMod k)} (h : ActsBy pt f Mat) (i : Fin m) :
    pt i ≫ f = Out.linComb pt (fun i' => (Mat i' i).val) := h.2 i

end Torsion

theorem FormIs.isMonHom {P : Out.PolAV (Sp K)} {M : LB P.A.left} {s : P.A ⟶ P.A} (h : FormIs P M s) :
    IsMonHom s := h.1

end GlobalTheory.ZV
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS

def IsDer {R : Type} [CommRing R] (x₀ : R →+* ℂ) (D : R → ℂ) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure PtDer {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  add : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f + f') = δ W f + δ W f'
  mul : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f * f') = valAt' y W f * δ W f' + valAt' y W f' * δ W f
  res : ∀ W W' (h : W' ≤ W), ⊤ ≤ y ⁻¹ᵁ W' → ∀ f, δ W' (resG X h f) = δ W f

structure LocDer {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = resG Y (fun _ hy => h hy) (d W f)
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

def dom (m : A₀.left ⟶ X) (W : X.Opens) : Set (Fin g → ℂ) := {z | ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W}

def fn (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) : ℂ := valAt' ((u.ex z).left ≫ m) W f

structure GoodU (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop where
  ah : u.IsAH Hm χ
  tan₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v
  tan₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  endo : ∀ f : A₀ ⟶ A₀, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f
  sec : ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ

structure KSRel {R : Type} [CommRing R] (p : X ⟶ Sp R) (m : A₀.left ⟶ X) (D : R → ℂ) (Θ : Matrix (Fin g) (Fin g) ℂ)
    (s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  der : ∀ z, PtDer ((u.ex z).left ≫ m) (s z)
  base : ∀ z r, s z ⊤ (constFn p ⊤ r) = D r
  hol : ∀ W f, DifferentiableOn ℂ (fun z => s z W f) (dom u m W)
  per : ∀ (l : u.Λ) W f, ∀ z ∈ dom u m W,
    s (z + l) W f = s z W f + fderiv ℂ (fn u m W f) z (Θ.mulVec (star (l : Fin g → ℂ)))

def IsSymm (Hm Θ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ z w, hermForm Hm (Θ.mulVec (star z)) w = hermForm Hm (Θ.mulVec (star w)) z

def Comm (Θ : Matrix (Fin g) (Fin g) ℂ) (F : (Fin g → ℂ) → (Fin g → ℂ)) : Prop :=
  ∀ z, F (Θ.mulVec (star z)) = Θ.mulVec (star (F z))

def IsConst (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (A₀ : Over (Sp ℂ)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap ℂ (DualNumber ℂ))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS

open Classical in
def rsT {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : Γ(Y, O) := if h : O ≤ O₀ then resG Y h s else 0

open Classical in
def pbT {Z Y : Scheme.{0}} (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens) : Γ(Z, O) :=
  if h : O ≤ f ⁻¹ᵁ O₀ then (f.appLE O₀ O h).hom s else 0
variable {K : Type} [Field K] {Y X : Scheme.{0}} {I : Type} {g : ℕ}

abbrev C1 (U : I → Y.Opens) : Type := ∀ i j, Γ(Y, U i ⊓ U j)

def IsCoc (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∀ i j k, rsT (c i j) (U i ⊓ U j ⊓ U k) + rsT (c j k) (U i ⊓ U j ⊓ U k) = rsT (c i k) (U i ⊓ U j ⊓ U k)

def IsCob (U : I → Y.Opens) (c : C1 U) : Prop :=
  ∃ b : ∀ i, Γ(Y, U i), ∀ i j, c i j = rsT (b j) (U i ⊓ U j) - rsT (b i) (U i ⊓ U j)

def Cohom (f : Y ⟶ Y) (U : I → Y.Opens) (c c' : C1 U) : Prop :=
  ∃ b : ∀ i k, Γ(Y, U i ⊓ f ⁻¹ᵁ U k),
    (∀ i i' k, rsT (b i' k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) - rsT (b i k) (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k) =
      rsT (c i i') (U i ⊓ U i' ⊓ f ⁻¹ᵁ U k)) ∧
    ∀ i k k', rsT (b i k) (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') - rsT (b i k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k') =
      pbT f (c' k k') (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k')

def lc (q : Y ⟶ Sp K) {U : I → Y.Opens} (c : Fin g → K) (φ : Fin g → C1 U) : C1 U :=
  fun i j => ∑ a, constFn q (U i ⊓ U j) (c a) * φ a i j

def IsDerK {R : Type} [CommRing R] (x₀ : R →+* K) (D : R → K) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure LocDerK {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m ⁻¹ᵁ W')
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)

def IsInvDer {A₀ : Over (Sp K)} [GrpObj A₀] (v : epsR K ⟶ A₀) (dd : ∀ W : A₀.left.Opens, Γ(A₀.left, W) → Γ(A₀.left, W)) : Prop :=
  ∀ (W : A₀.left.Opens) (f : Γ(A₀.left, W)),
    pbT ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) =
      pbT (snd (epsR K) A₀).left f ((snd (epsR K) A₀).left ⁻¹ᵁ W) +
        constFn (R := DualNumber K) (fst (epsR K) A₀).left _ DualNumber.eps *
          pbT (snd (epsR K) A₀).left (dd W f) ((snd (epsR K) A₀).left ⁻¹ᵁ W)

structure KSCoc {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W : I → X.Opens)
    (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)) (d : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O))
    (θ : Fin g → C1 (fun i => m ⁻¹ᵁ W i)) : Prop where
  der : ∀ i, LocDerK q p m D (W i) (d i)
  diff : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, d j O f - d i O f = ∑ a, rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)

def IsDlog (m : Y ⟶ X) (L : LB X) (dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O))
    (φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)) : Prop :=
  ∀ a i j, pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j) * φ a i j = dd a _ (pbT m (L.g i j).val (m ⁻¹ᵁ L.U i ⊓ m ⁻¹ᵁ L.U j))

def IsConstK (A' : Over (Sp (DualNumber K))) [GrpObj A'] (A₀ : Over (Sp K)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap K (DualNumber K))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ZM

abbrev Ix (g k : ℕ) : Type := Fin (2 * g) → ZMod k

structure TBase (o : Type) [CommRing o] (k : ℕ) where
  ζ : oˣ
  unit : IsUnit (k : o)
  prim : ∀ (K : Type) [Field K] (β : o →+* K), IsPrimitiveRoot (β ζ) k
variable {o : Type} [CommRing o] {S S' : Scheme.{0}}

def unitS (s : S ⟶ Sp o) (u : oˣ) : Γ(S, ⊤)ˣ := Units.map s.appTop.hom.toMonoidHom (unitOn u)

structure TObj (g k : ℕ) (J : Type) (b : TBase o k) (s : S ⟶ Sp o) where
  A : Over S
  [grp : GrpObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension g A.hom
  L : LB A.left
  isLB : L.IsLB
  rigid : Out.Rigidified A L
  sym : Out.Sym A L
  ample : Out.RelAmple A L
  ktriv : Out.KTriv A L
  pt : Fin (2 * g) → (Out.baseOver S ⟶ A)
  torsion : ∀ i, pt i ^ k = 1
  bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 →
    ∃! c : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (c i).val) = y
  pairing : ∀ i j, Out.WeilIs A L k (pt i) (pt j) (unitS s b.ζ ^ Out.stdSymp g i j)
  act : J → (A ⟶ A)
  hom : ∀ j, IsMonHom (act j)
attribute [instance] TObj.grp
variable {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def TObj.pol (t : TObj g k J b s) : Out.PolAV S :=
  { A := t.A, isAb := t.ab, g := g, smoothDim := t.dim, L := t.L, isLB := t.isLB, rigid := t.rigid, sym := t.sym, ample := t.ample, ktriv := t.ktriv }

def TObj.lab (t : TObj g k J b s) (a : Ix g k) : Out.baseOver S ⟶ t.A := Out.linComb t.pt (fun i => (a i).val)

def TMap (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) : Prop :=
  ∃ φ : t'.A.left ⟶ t.A.left, IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

def TObj.HasTh {N' : ℕ} {b : TBase o (N' ^ 2)} (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] (x : Sp R ⟶ S)
    (v : Ix g (N' ^ 2) → R) : Prop :=
  Out.IsThetaPt t.pol N' (T := Over.mk x) (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.lab a)
    (fun a => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v a))

def Coset (n N' : ℕ) {R : Type} [CommRing R] (v : Ix g (N' ^ 2) → R) (q : Ideal R) : Prop :=
  ∀ a, ∃ c, v (a + (N' / n) • c) ∉ q

def thIdeal {N' : ℕ} {b : TBase o (N' ^ 2)} (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) :
    Ideal (MvPolynomial (Ix g (N' ^ 2)) o) :=
  ⨅ (t : TObj g (N' ^ 2) J b (spMap em)) (v : Ix g (N' ^ 2) → ℂ) (_ : C t ∧ t.HasTh (𝟙 _) v), RingHom.ker (MvPolynomial.eval₂Hom em v)

def InMM (n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) {R : Type} [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) : Prop :=
  (∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ∧ ∀ q : Ideal R, q.IsPrime → Coset n N' v q

def FromC (em : o →+* ℂ) (C : TObj g k J b (spMap em) → Prop) (t : TObj g k J b s) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (β : o →+* K₀) (i : K₀ →+* K) (j : K₀ →+* ℂ) (t₀ : TObj g k J b (spMap β))
    (tx : TObj g k J b (x ≫ s)) (tc : TObj g k J b (spMap em)),
    j.comp β = em ∧ x ≫ s = spMap i ≫ spMap β ∧ TMap tx t x ∧ TMap tx t₀ (spMap i) ∧ TMap tc t₀ (spMap j) ∧ C tc

def fromSet (em : o →+* ℂ) (C : TObj g k J b (spMap em) → Prop) (t : TObj g k J b s) : Set S :=
  {p | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S), p ∈ Set.range x ∧ FromC em C t x}

def TObj.Prim (t : TObj g k J b s) (w w' : J) : Prop :=
  letI := t.ab.comm
  t.act w * t.act w' = 𝟙 t.A ∧
  LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act w, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act w'] t.L) ∧
  LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act w] t.L)

def TObj.Shape (t : TObj g k J b s) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) : Prop :=
  ∀ j, (∀ i, t.pt i ≫ t.act j = t.lab (fun i' => (Mat j i' i : ZMod k))) ∧
    Out.RelAmple t.A (LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1])

structure GoodClass {N' : ℕ} {b : TBase o (N' ^ 2)} (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop)
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (d : ℕ) : Prop where
  iso : ∀ t t', C t → TMap t' t (𝟙 _) → C t'
  shape : ∀ t, C t → t.Shape Mat κ ∧ t.Prim w w'
  fam : ∃ (r : ℕ) (B : Fin r → Set (Fin d → ℂ)) (θ : Fin r → (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ),
    (∀ i, IsOpen (B i) ∧ IsPreconnected (B i) ∧ (∀ a, DifferentiableOn ℂ (fun z => θ i z a) (B i)) ∧
      ∀ z ∈ B i, (∃ t, C t ∧ t.HasTh (𝟙 _) (θ i z)) ∧ {z' ∈ B i | ∃ c : ℂ, θ i z' = c • θ i z}.Countable) ∧
    ∀ t, C t → ∃ i, ∃ z ∈ B i, t.HasTh (𝟙 _) (θ i z)

structure ThetaFam (n : ℕ) {N' : ℕ} {b : TBase o (N' ^ 2)} (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) where
  MM : Scheme.{0}
  s : MM ⟶ Sp o
  qproj : IsQProjOver s
  flat : Flat s
  reduced : IsReduced MM
  univ : TObj g (N' ^ 2) J b s
  dense : Dense (fromSet em C univ)
  loc : ∀ (R : Type) [CommRing R] [IsLocalRing R] (β : o →+* R) (x : Sp R ⟶ MM), x ≫ s = spMap β →
    ∃ v, univ.HasTh x v ∧ InMM n N' (thIdeal em C) β v
  pts : ∀ (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R), InMM n N' (thIdeal em C) β v →
    ∃! x : Sp R ⟶ MM, x ≫ s = spMap β ∧ univ.HasTh x v
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) →
    ∃! f : S ⟶ MM, f ≫ s = s' ∧ TMap t univ f
  unram : ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ MM) (t : TObj g (N' ^ 2) J b (x ≫ s)),
    x ≫ s = constPt x ≫ s → TMap t univ x → TMap t univ (constPt x) → x = constPt x

def TObj.zero (k : ℕ) (J : Type) (b : TBase o k) (s : S ⟶ Sp o) : TObj 0 k J b s where
  A := (Out.Inh.zeroPolAV S).A
  grp := (Out.Inh.zeroPolAV S).grp
  ab := (Out.Inh.zeroPolAV S).isAb
  dim := (Out.Inh.zeroPolAV S).smoothDim
  L := (Out.Inh.zeroPolAV S).L
  isLB := (Out.Inh.zeroPolAV S).isLB
  rigid := (Out.Inh.zeroPolAV S).rigid
  sym := (Out.Inh.zeroPolAV S).sym
  ample := (Out.Inh.zeroPolAV S).ample
  ktriv := (Out.Inh.zeroPolAV S).ktriv
  pt := fun i => Fin.elim0 i
  torsion := fun i => Fin.elim0 i
  bij := fun _ _ _ _ _ _ => ⟨fun i => Fin.elim0 i, toUnit_unique _ _, fun _ _ => funext fun i => Fin.elim0 i⟩
  pairing := fun i => Fin.elim0 i
  act := fun _ => 𝟙 _
  hom := fun _ => inferInstance

end GlobalTheory.ZM
end
end
