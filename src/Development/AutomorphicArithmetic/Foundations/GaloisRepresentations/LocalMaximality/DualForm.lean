module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F : Type} [Field F] [Algebra ℂ F] {V V' : Type} [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

def Lat (A : Subalgebra ℂ F) (M : Submodule ℂ V) : Prop :=
  (∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) ∧ ∃ (n : ℕ) (v : Fin n → V) (φ : Fin n → V →ₗ[F] F), (∀ k, v k ∈ M) ∧ (∀ k, ∀ m ∈ M, φ k m ∈ A) ∧
    ∀ m ∈ M, m = ∑ k, φ k m • v k


variable (F V V') in
def actF : F ⊗[ℂ] F →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] V') :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V) (Algebra.lsmul ℂ ℂ V'))


variable (V') in
def ctrF (ψ : V →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((Algebra.lsmul ℂ ℂ V').toLinearMap ∘ₗ ψ.restrictScalars ℂ)

def f0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (j : Fin (d + 1)) (l : Fin d) : F ⊗[ℂ] F :=
  ((x (j.succAbove l) : F) / x j) ⊗ₜ 1 - 1 ⊗ₜ ((x (j.succAbove l) : F) / x j)

def R0 {d : ℕ} (x : Fin (d + 1) → Fˣ) (I J : Finset (Fin (d + 1))) : Subalgebra ℂ (F ⊗[ℂ] F) :=
  (Algebra.TensorProduct.map (rA ℂ (xv x) I).val (rA ℂ (xv x) J).val).range

def omG {d : ℕ} (x : Fin (d + 1) → Fˣ) (i : Fin (d + 1)) : F := ∏ l, ((x l : F) / x i)


variable (V') in
def resP (ρ : F →ₗ[ℂ] ℂ) : F ⊗[ℂ] V' →ₗ[ℂ] V' := TensorProduct.lift ((LinearMap.lsmul ℂ V') ∘ₗ ρ)

end

section
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

structure ZF {κ : Type} [LinearOrder κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) : Prop where
  adm : (sysZ K x 0).admitted n z
  diag : ∀ l, Algebra.TensorProduct.lmul' ℂ (z l) = 0
  gen : ∀ i, Algebra.adjoin ℂ {b : K | b ∈ rB ℂ K (xv x) {i} ∧ ∃ l N, n l = (N, N) ∧
    z l = (((sysZ K x 0).X i ^ N * (sysZ K x 0).Y i ^ N : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) * (b ⊗ₜ 1 - 1 ⊗ₜ b)} = rB ℂ K (xv x) {i}

def IsDiag (τ : DR ℂ K →ₗ[K] K) (a : ℕ) (c : Finset (Two d ⊕ₗ Mi d) → DR ℂ K ⊗[ℂ] DR ℂ K) : Prop :=
  ∀ i j L, L.card = d → Acts (F := F) K τ a (c (uni (uni {i} {j}) L)) ((-1) ^ d * kap K x L)

abbrev pr (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) : (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] (Finset (Fin (d + 1)) → DR ℂ K) →ₗ[ℂ] ℂ :=
  cupPair ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))

end

def GoodZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a : ℕ, (sysZ K x a).Good ∧ (sysP K x a).Good ∧
  ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t → omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a

def LatOm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a : ℕ) (I : Finset (Fin (d + 1))), I.Nonempty →
  Lat (rA ℂ (xv x) I) (omB ℂ K (rB ℂ K (xv x) I) a) ∧
  ∀ w ∈ ⋀[K]^a Ω[K⁄ℂ], w ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) I) a : Set (DR ℂ K))

def LatA : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I : Finset (Fin (d + 1))), ∀ i ∈ I, Lat (rA ℂ (xv x) I) (omA ℂ (xv x) I) ∧
  (∀ y : F, y ∈ omA ℂ (xv x) I ↔ y / omG x i ∈ rA ℂ (xv x) I) ∧
  ∀ j, ∀ y ∈ omA ℂ (xv x) (insert j I), ∃ N : ℕ, ((x j : F) / x i) ^ N * y ∈ omA ℂ (xv x) I

def Reg0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J →
  Reg (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (f0 x j)

def Ker0 : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (I J : Finset (Fin (d + 1))), ∀ j ∈ I, j ∈ J → ∀ m ∈ R0 x I J,
  Algebra.TensorProduct.lmul' ℂ m = 0 →
  m ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) (Set.range (f0 x j))

def RegLat : Prop := ∀ (F : Type) [Field F] [Algebra ℂ F] (d : ℕ) (x : Fin (d + 1) → Fˣ), IsPd ℂ (xv x) → ∀ (V V' : Type) [AddCommGroup V] [Module F V] [Module ℂ V] [IsScalarTower ℂ F V]
  [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V'] (I J : Finset (Fin (d + 1))) (M : Submodule ℂ V)
  (M' : Submodule ℂ V'), Lat (rA ℂ (xv x) I) M → Lat (rA ℂ (xv x) J) M' → ∀ j ∈ I, j ∈ J →
  Reg (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (f0 x j) ∧
  ∀ m ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M', (∀ ψ : V →ₗ[F] F, ctrF V' ψ m = 0) →
    m ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') (Set.range (f0 x j))

def DualForm : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ ψ : DR ℂ K →ₗ[F] F,
  (∃ w ∈ ⋀[K]^a Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (y * w))) ∧
  ∃ w ∈ ⋀[K]^(d - a) Ω[K⁄ℂ], ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], ψ y = Algebra.trace F K (τ (w * y))

def ColZ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysZ K x a).act ((sysZ K x a).M I J) fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysZ K x a).M I J, Acts (F := F) K τ a m 0 →
    m ∈ sm (sysZ K x a).act ((sysZ K x a).M I J) (Set.range fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l))

def ColP : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, ∀ i ∈ I, ∀ j ∈ J,
  KE (kos (sysP K x a).act ((sysP K x a).M I J) fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l)) d ∧
  ∀ m ∈ (sysP K x a).M I J, mulP F K m = 0 →
    m ∈ sm (sysP K x a).act ((sysP K x a).M I J) (Set.range fun l => (sysP K x a).r n11 (sysP K x a).mu i j (dj j l))

def ActsLin : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a : ℕ,
  (∀ m m' c c', Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
    Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c')) ∧
  (∀ m c s, Acts (F := F) K τ a m c → Acts (F := F) K τ a (actZ K s m) (Algebra.TensorProduct.lmul' ℂ s * c)) ∧
  (∀ i j M m, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) → Acts (F := F) K τ a m 0) ∧
  (∀ (u : (K ⊗[ℂ] K)ˣ) M m i j, m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) →
    Acts (F := F) K τ a (actZ K u m) 0) ∧
  (∀ (s : F ⊗[ℂ] K) m, mulP F K ((sysP K x a).act s m) =
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s • mulP F K m) ∧
  ∀ (s : F ⊗[ℂ] K) m w, muP F K τ (actZ K (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℂ F K) (AlgHom.id ℂ K) s) m) w =
    (sysP K x a).act s (muP F K τ m w)

def IdJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ j, ∃ m ∈ (sysZ K x a).M {j} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x j))

def IdIJ : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ i j, ∃ m ∈ (sysZ K x a).M {i} {j}, Acts (F := F) K τ a m (algebraMap F K (omG x i))

def ZFam : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∃ (m : ℕ) (n : Fin m → ℕ × ℕ) (z : Fin m → K ⊗[ℂ] K), ZF K x n z

def KapInd : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (S E : Type) [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  (π : S →ₐ[ℂ] K), (∀ i, π (T.X i) = algebraMap F K (x i)) → (∀ i, π (T.Y i) = algebraMap F K (x i)) →
  ∀ i L, L.card = d → π (detC T.rowMu (uni {i} L)) = kap K x L

def ZCol : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∀ i j, ∃ c ∈ ((sysZ K x a).colCx (app n11 n) (app (sysZ K x a).mu z) {i} {j}).Z d,
    ∀ L : Finset (Mi d), L.card = d → Acts (F := F) K τ a (c (uni L ∅)) ((-1) ^ d * kap K x L)

def ZEx : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∃ c ∈ ((sysZ K x a).cx (app n11 n) (app (sysZ K x a).mu z)).Z (d + 2), IsDiag K x τ a (resK inlE c)

def PLift : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ a I J, I.Nonempty → J.Nonempty → ∀ w ∈ omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a,
  ∃ y ∈ ((sysP K x a).colCx n11 (sysP K x a).mu I J).Z d, ∀ L, L.card = d → mulP F K (y L) = kap K x L • w

def PCmp : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2),
  (∀ b L, d < L.card → c (uni b L) = 0) →
  ∀ γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2),
  (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • γ b) → c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).B (d + p + 2)

def PTheta : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (a p : ℕ), ∀ β ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  ∃ c ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2), (∀ b L, d < L.card → c (uni b L) = 0) ∧
    (∀ b L, L.card = d → mulP F K (c (uni b L)) = kap K x L • ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 β b) ∧
    ∀ J, c (uni (uni Finset.univ J) ∅) = 1 ⊗ₜ β J

def PCup : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  rcup (muP F K τ) p c α ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) ∧
    (∀ b L, d < L.card → rcup (muP F K τ) p c α (uni b L) = 0) ∧
    ∀ b L, L.card = d → mulP F K (rcup (muP F K τ) p c α (uni b L)) = kap K x L • ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α b

def PInt : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), ∀ t ∈ (sysP K x a).mix.B (d + p + 2),
  (fun J => resP (DR ℂ K) ρ (t (uni Finset.univ J))) ∈ (omCx (rB ℂ K (xv x)) a).B p

def RCupTop : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ t ∈ (sysZ K x a).mix.B (d + 2), ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (t (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZAct : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a p : ℕ), a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z p,
  α - (fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) ∈
    (omCx (rB ℂ K (xv x)) a).B p

def ZId : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ a : ℕ, a ≤ d → ∀ c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2), IsDiag K x τ a c →
  ∃ (m : ℕ) (p : Fin m → ℕ) (e f : Fin m → Finset (Fin (d + 1)) → DR ℂ K),
    (∀ k, p k ≤ d ∧ e k ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - p k) ∧ f k ∈ (omCx (rB ℂ K (xv x)) a).Z (p k)) ∧
    top c - ∑ k, join (TensorProduct.mk ℂ _ _) (e k) (f k) ∈ (sysZ K x a).mix.B (d + 2) ∧
    ∀ q : ℕ, ∀ α ∈ (omCx (rB ℂ K (xv x)) a).Z q,
      α - ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k ∈ (omCx (rB ℂ K (xv x)) a).B q

def PrB : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ → ∀ (a q : ℕ), a ≤ d → q ≤ d → ∀ e ∈ (omCx (rB ℂ K (xv x)) (d - a)).Z (d - q),
  ∀ y ∈ (omCx (rB ℂ K (xv x)) a).B q, pr K τ ρ e y = 0

end UpperTheory.Gal.productCup_of_system

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem wd_apply' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem wd_anti' {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w w' : σ → Module.End ℂ E) (h : ∀ i j, Commute (w i) (w' j)) (c : Finset σ → E) :
    wd w (wd w' c) + wd w' (wd w c) = 0 := by
  funext t
  have hc : ∀ f : σ → σ → E, ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = ∑ i ∈ t, ∑ j ∈ t.erase i, f j i := by
    intro f
    refine Finset.sum_comm' ?_
    intro x y
    simp only [Finset.mem_erase]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨Ne.symm b, a⟩, c⟩, fun ⟨⟨b, a⟩, c⟩ => ⟨a, Ne.symm b, c⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [wd_apply', map_sum, map_zsmul, Finset.smul_sum, smul_smul, Pi.add_apply, Pi.zero_apply]
  conv_lhs => rhs; rw [hc]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hji : j ≠ i := (Finset.mem_erase.1 hj).1
  have hjt : j ∈ t := (Finset.mem_erase.1 hj).2
  have hcomm : w' j (w i (c ((t.erase j).erase i))) = w i (w' j (c ((t.erase i).erase j))) := by
    rw [show (t.erase j).erase i = (t.erase i).erase j from Finset.erase_right_comm]
    exact (LinearMap.congr_fun (h i j).eq _).symm
  rw [hcomm, ← add_smul, GlobalTheory.cubeSign_mul_erase hi hjt (Ne.symm hji), neg_add_cancel, zero_smul]

private theorem cubeSign_map' {σ σ' : Type} [LinearOrder σ] [LinearOrder σ'] (e : σ' ↪o σ)
    (s : Finset σ') (i : σ') :
    GlobalTheory.cubeSign (s.map e.toEmbedding) (e i) = GlobalTheory.cubeSign s i := by
  simp only [GlobalTheory.cubeSign, Finset.filter_map, Finset.card_map]
  congr 2
  ext x
  simp

theorem UpperTheory.Gal.productCup_of_system.wdBasic_of :
    WdBasic := by
  intro σ E _ _ _ _ A w
  have d2 : (∀ i j, Commute (w i) (w j)) → ∀ c, wd w (wd w c) = 0 := by
    intro h c
    have hx := wd_anti' w w h c
    have h2 : (2 : ℂ) • wd w (wd w c) = 0 := by rw [two_smul]; exact hx
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  refine ⟨d2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨hw, hA⟩ n a ha
    refine ⟨?_, d2 hw a⟩
    simp only [acx, Submodule.mem_pi, Set.mem_univ, forall_const] at ha ⊢
    intro s
    rw [wd_apply']
    by_cases hs : (s.card : ℤ) = n + 1
    · rw [if_pos hs]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_of_tower_mem _ _ ?_
      have hcard : ((s.erase i).card : ℤ) = n := by
        have := Finset.card_erase_add_one hi
        omega
      have hmem := ha (s.erase i)
      rw [if_pos hcard] at hmem
      have := hA (s.erase i) i (by simp) _ hmem
      rwa [Finset.insert_erase hi] at this
    · rw [if_neg hs, Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hcard : ¬ ((s.erase i).card : ℤ) = n := by
        have := Finset.card_erase_add_one hi
        omega
      have hmem := ha (s.erase i)
      rw [if_neg hcard, Submodule.mem_bot] at hmem
      rw [hmem, map_zero, smul_zero]
  · intro w'
    refine LinearMap.ext fun c => funext fun t => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, wd_apply', smul_add, Finset.sum_add_distrib]
  · intro w' h _ c
    exact wd_anti' w w' h c
  · intro c
    funext t
    rw [wd_apply']
    simp only [Module.End.one_apply]
    rfl
  · intro σ' _ e c s
    rw [wd_apply', wd_apply', Finset.sum_map]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [RelEmbedding.coe_toEmbedding, cubeSign_map']
    rw [Finset.map_erase]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdUni
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {β κ : Type} [LinearOrder β] [LinearOrder κ]

private theorem lex_cases (t : β ⊕ₗ κ) : (∃ i, t = inlE i) ∨ ∃ l, t = inrE l := by
  rcases t with i | l
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨l, rfl⟩

private theorem mem_uni_l (b : Finset β) (L : Finset κ) (i : β) :
    (inlE i : β ⊕ₗ κ) ∈ uni b L ↔ i ∈ b := by
  simp [uni, inlE]

private theorem mem_uni_r (b : Finset β) (L : Finset κ) (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ uni b L ↔ l ∈ L := by
  simp [uni, inrE]

private theorem mem_lft (s : Finset (β ⊕ₗ κ)) (i : β) : i ∈ lft s ↔ (inlE i : β ⊕ₗ κ) ∈ s := by
  simp [lft, inlE]

private theorem mem_rgt (s : Finset (β ⊕ₗ κ)) (l : κ) : l ∈ rgt s ↔ (inrE l : β ⊕ₗ κ) ∈ s := by
  simp [rgt, inrE]

private theorem l_lt_r (i : β) (l : κ) : (inlE i : β ⊕ₗ κ) < inrE l := Sum.Lex.inl_lt_inr i l

private theorem not_r_lt_l (i : β) (l : κ) : ¬ (inrE l : β ⊕ₗ κ) < inlE i := Sum.Lex.not_inr_lt_inl

private theorem card_uni (b : Finset β) (L : Finset κ) : (uni b L).card = b.card + L.card := by
  simp [uni]

private theorem sum_uni {M : Type} [AddCommMonoid M] (b : Finset β) (L : Finset κ) (f : β ⊕ₗ κ → M) :
    ∑ t ∈ uni b L, f t = ∑ i ∈ b, f (inlE i) + ∑ l ∈ L, f (inrE l) := by
  rw [uni, Finset.sum_map, Finset.sum_disjSum]
  rfl

private theorem erase_l [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (i : β) :
    (uni b L).erase (inlE i) = uni (b.erase i) L := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l, Finset.mem_erase, inlE.injective.ne_iff]
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r]
    exact and_iff_right (l_lt_r i m).ne'

private theorem erase_r [DecidableEq (β ⊕ₗ κ)] (b : Finset β) (L : Finset κ) (l : κ) :
    (uni b L).erase (inrE l) = uni b (L.erase l) := by
  ext t
  rcases lex_cases t with ⟨j, rfl⟩ | ⟨m, rfl⟩
  · rw [Finset.mem_erase, mem_uni_l, mem_uni_l]
    exact and_iff_right (l_lt_r j l).ne
  · rw [Finset.mem_erase, mem_uni_r, mem_uni_r, Finset.mem_erase, inrE.injective.ne_iff]

private theorem sign_l (b : Finset β) (L : Finset κ) (i : β) :
    GlobalTheory.cubeSign (uni b L) (inlE i) = GlobalTheory.cubeSign b i := by
  unfold GlobalTheory.cubeSign
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [not_r_lt_l]

private theorem sign_r (b : Finset β) (L : Finset κ) (l : κ) :
    GlobalTheory.cubeSign (uni b L) (inrE l) = (-1 : ℤ) ^ b.card * GlobalTheory.cubeSign L l := by
  unfold GlobalTheory.cubeSign
  rw [← pow_add]
  congr 1
  rw [Finset.card_filter, Finset.card_filter, sum_uni]
  simp [l_lt_r]

private theorem wd_app {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

end

theorem UpperTheory.Gal.productCup_of_system.wdUni_of :
    WdUni := by
  intro β κ E _ _ _ _ w c b L
  refine ⟨?_, ?_, ?_, card_uni b L, ?_⟩
  · rw [wd_app, wd_app, wd_app, sum_uni, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by rw [sign_l, erase_l]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [sign_r, erase_r, mul_smul]
  · ext i
    rw [mem_lft, mem_uni_l]
  · ext l
    rw [mem_rgt, mem_uni_r]
  · intro s
    ext t
    rcases lex_cases t with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · rw [mem_uni_l, mem_lft]
    · rw [mem_uni_r, mem_rgt]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrLin
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.trLin_of :
    TrLin := by
  intro V _ _ ι _ φ v hv
  have hfin : FiniteDimensional ℂ V := by
    refine Module.Finite.of_surjective (Fintype.linearCombination ℂ v) ?_
    intro y
    exact ⟨fun k => φ k y, by rw [Fintype.linearCombination_apply]; exact (hv y).symm⟩
  refine ⟨hfin, fun u => ?_⟩
  have hu : u = ∑ k, dualTensorHom ℂ V V (φ k ⊗ₜ u (v k)) := by
    ext y
    rw [LinearMap.sum_apply]
    simp only [dualTensorHom_apply]
    conv_lhs => rw [hv y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp [map_smul]
  conv_lhs => rw [hu]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.trace_eq_contract_apply]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMuSpan
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma muSpan_base {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (R : Subalgebra ℂ S) (i j a : Fin (d + 1)) :
    InSp R (fun t => T.r n11 T.mu i j (dj j t)) (T.r n11 T.mu i j (toLex (a, j))) := by
  by_cases h : a = j
  · subst h
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    simp [Sys.r, Sys.mu, mul_comm]
  · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq h
    refine ⟨Pi.single t 1, fun l => ?_, ?_⟩
    · by_cases hl : l = t
      · subst hl
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hl] using R.zero_mem
    · rw [Finset.sum_eq_single t]
      · simp only [Pi.single_eq_same, one_mul]
        rfl
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro hb
        exact absurd (Finset.mem_univ t) hb

private lemma muSpan_rel {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) (i j : Fin (d + 1)) (l : Mi d) :
    T.r n11 T.mu i j l =
      ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).1, j)) -
      ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * T.r n11 T.mu i j (toLex ((ofLex l).2, j)) := by
  have hv : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  have hu : ∀ l' : Mi d, T.u n11 i j l' = T.X i * T.Y j := fun _ => by simp [Sys.u, n11]
  simp only [Sys.r, Sys.mu, ofLex_toLex, Units.val_mul, hu]
  linear_combination (-((T.X (ofLex l).1 : S) * T.Y (ofLex l).2 - T.X (ofLex l).2 * T.Y (ofLex l).1) *
    ((T.X i * T.Y j)⁻¹ : Sˣ)) * hv

theorem UpperTheory.Gal.productCup_of_system.muSpan_of :
    MuSpan := by
  intro d S E _ _ _ _ T hT I J i hi j hj l
  have hI : I.Nonempty := ⟨i, hi⟩
  obtain ⟨p, hp, hp'⟩ := muSpan_base T (T.R I J) i j (ofLex l).1
  obtain ⟨q, hq, hq'⟩ := muSpan_base T (T.R I J) i j (ofLex l).2
  have hb := hT.memY I J hI j hj (ofLex l).2
  have ha := hT.memY I J hI j hj (ofLex l).1
  refine ⟨fun t => ((T.Y (ofLex l).2 * (T.Y j)⁻¹ : Sˣ) : S) * p t -
    ((T.Y (ofLex l).1 * (T.Y j)⁻¹ : Sˣ) : S) * q t, fun t => ?_, ?_⟩
  · exact sub_mem (mul_mem hb (hp t)) (mul_mem ha (hq t))
  · rw [muSpan_rel T i j l, hp', hq', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KSubOf
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.kSub_of :
    FiltrationBoundaryCriterion → SubQEx → KSub := by
  intro gl sub S E _ _ _ _ act κ _ _ R M r hst hr
  refine ⟨?_, ?_⟩
  · intro d e hK m hm c hc
    have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
      refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm]
    have hQ := sub S E act κ M r d e hK
    have hcard : (img e).card = d := by simp [img]
    refine gl κ E (fun _ => M) (fun l => act (r l)) (img e) d m hW hQ c hc ?_
      ⟨0, Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
    · intro s hs
      exfalso
      apply hs
      have h1 : (s ∩ img e).card ≤ (img e).card := Finset.card_le_card Finset.inter_subset_right
      rw [hcard] at h1
      exact_mod_cast h1
    · intro s hs
      have h1 : (s ∩ img e).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
      have hne : (s.card : ℤ) ≠ m := by
        have : ((s ∩ img e).card : ℤ) ≤ s.card := by exact_mod_cast h1
        omega
      have h2 : c s ∈ (if (s.card : ℤ) = m then M else ⊥ : Submodule ℂ E) := hc.1 s (Set.mem_univ s)
      rw [if_neg hne, Submodule.mem_bot] at h2
      rw [h2, map_zero]
      rfl
  · intro n c hc L
    obtain ⟨y, hy, rfl⟩ := hc
    have hval : ∀ i ∈ L, y (L.erase i) ∈ M := by
      intro i _
      have h2 : y (L.erase i) ∈ (if ((L.erase i).card : ℤ) = n - 1 then M else ⊥ : Submodule ℂ E) :=
        hy (L.erase i) (Set.mem_univ _)
      split_ifs at h2 with h
      · exact h2
      · rw [Submodule.mem_bot] at h2
        rw [h2]
        exact M.zero_mem
    have hexp : (kos act M r).D y L
        = ∑ i ∈ L, (GlobalTheory.cubeSign L i : ℤ) • act (r i) (y (L.erase i)) := by
      simp [kos, acx, wd]
    rw [hexp]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_of_tower_mem _ _ ?_
    have h3 : act (r i) (y (L.erase i)) ∈ M.map (act (r i)) := ⟨_, hval i hi, rfl⟩
    exact (le_iSup₂_of_le (r i) (Set.mem_range_self i) le_rfl : M.map (act (r i)) ≤ sm act M (Set.range r)) h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CoordinateSystemDegreeOneOfUniversalDerivation
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma acx_eq_zero {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : A s = ⊥) : c s = 0 := by
  have h : c s ∈ (if (s.card : ℤ) = n then A s else ⊥) :=
    Submodule.mem_pi.1 (show c ∈ Submodule.pi Set.univ
      (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) from hc) s (Set.mem_univ _)
  rw [hs, ite_self, Submodule.mem_bot] at h
  exact h

theorem UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_one_of_universalDerivation :
    L1 → SysOk → WdUni → CechKoszulSystemBoundaryCriterion := by
  intro hL hOk hU
  intro d S E _ _ _ _ T κ _ _ n z N hG hAdm hKE c hc hbig hcol
  obtain ⟨hW, -, -⟩ := hOk d S E T κ n z hG hAdm
  set A : Finset (Two d ⊕ₗ κ) → Submodule ℂ E := fun s => mixF (fun I J =>
    Submodule.map (T.act ↑(∏ l ∈ rgt s, T.u n (pk I) (pk J) l)) (T.M I J)) (lft s) with hA
  have hu := fun (b : Finset (Two d)) (L : Finset κ) => hU (Two d) κ E (T.wt z) (fun _ => 0) b L
  have hcolA : ∀ b : Finset (Two d), (lft b).Nonempty → (rgt b).Nonempty →
      colA A (T.wt z) b = T.colCx n z (lft b) (rgt b) := by
    intro b h1 h2
    simp only [colA, Sys.colCx, kosT]
    congr 1
    funext L
    simp only [hA, (hu b L).2.1, (hu b L).2.2.1, mixF, h1, h2, and_self, if_true]
  have hbot : ∀ b : Finset (Two d), ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) → ∀ L, A (uni b L) = ⊥ := by
    intro b h L
    simp only [hA, (hu b L).2.1, mixF, if_neg h]
  have hcC : c ∈ (acx A (T.wt z)).C N := hc.1
  refine hL (Two d) κ E A (T.wt z) (d : ℤ) N hW ?_ c hc ?_ ?_
  · intro b
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      exact hKE _ _ h.1 h.2
    · intro m _ x hx
      have hx1 : x ∈ (colA A (T.wt z) b).C m := hx.1
      have hx0 : x = 0 := funext fun L =>
        acx_eq_zero (fun L => A (uni b L)) (fun l => T.wt z (inrE l)) m x hx1 L (hbot b h L)
      rw [hx0]
      exact Submodule.zero_mem _
  · intro b L hlt
    exact hbig b L (by exact_mod_cast hlt)
  · intro b hb
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      have hU2 := hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) (lft b) (rgt b)
      have hs : uni (lft b) (rgt b) = b := hU2.2.2.2.2 b
      have := hcol (lft b) (rgt b) h.1 h.2 (by rw [← hb, ← hU2.2.2.2.1, hs])
      rw [hs] at this
      exact this
    · have h0 : col c b = 0 := funext fun L => acx_eq_zero A (T.wt z) N c hcC (uni b L) (hbot b h L)
      rw [h0]
      exact Submodule.zero_mem _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdUniImpliesMJ
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_at {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private lemma wd_act {ι S E : Type} [LinearOrder ι] [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (u : ι → S) (f : Finset ι → S) (m : E) (t : Finset ι) :
    wd (fun i => act (u i)) (fun t => act (f t) m) t =
      act (wd (fun i => Algebra.lmul ℂ S (u i)) f t) m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [wd_at, wd_at, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_zsmul, Module.End.mul_apply]

private lemma wd_one {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (g : E →ₗ[ℂ] E) (b : Finset ι → E) (t : Finset ι) :
    wd (fun _ => (1 : Module.End ℂ E)) (fun t => g (b t)) t = g (deltaL ℂ ι E b t) := by
  rw [wd_at]
  change _ = g (∑ i ∈ t, GlobalTheory.cubeSign t i • b (t.erase i))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_zsmul]

private lemma lft_uni' (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β) (L : Finset κ) :
    lft (uni b L) = b := (h β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.1

private lemma rgt_uni' (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β) (L : Finset κ) :
    rgt (uni b L) = L := (h β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1

private lemma uni_lr (h : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (s : Finset (β ⊕ₗ κ)) :
    uni (lft s) (rgt s) = s := (h β κ ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s

private lemma mj_uni (h : WdUni) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (T : Sys d S E) {κ : Type} [LinearOrder κ] (p : ℕ) (θ : Finset (Fin (d + 1) ⊕ₗ κ) → S)
    (b : Finset (Fin (d + 1)) → E) (I J : Finset (Fin (d + 1))) (L : Finset κ) :
    T.mj p θ b (uni (uni I J) L) = T.act (θ (uni I L)) (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) := by
  simp only [Sys.mj, lft_uni' h, rgt_uni' h, map_zsmul]

theorem UpperTheory.Gal.productCup_of_system.mJ_of :
    WdUni → MJ := by
  intro h d S E _ _ _ _ T κ _ _ z p θ b hθ hb hJ
  funext s
  obtain ⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L :=
    ⟨lft (lft s), rgt (lft s), rgt s, by rw [uni_lr h, uni_lr h]⟩
  have hw2 : ∀ l : κ, T.wt z (inrE l) = T.act (z l) := fun _ => rfl
  have hw3 : ∀ i : Fin (d + 1), T.wt z (inlE (inlE i)) = 1 := fun _ => rfl
  have hw4 : ∀ i : Fin (d + 1), T.wt z (inlE (inrE i)) = 1 := fun _ => rfl
  have e1 := (h (Two d) κ E (T.wt z) (T.mj p θ b) (uni I J) L).1
  have e2 := (h (Fin (d + 1)) (Fin (d + 1)) E (fun i => T.wt z (inlE i))
    (fun b' => T.mj p θ b (uni b' L)) I J).1
  have e3 := (h (Fin (d + 1)) κ S (fun t => Algebra.lmul ℂ S (app (fun _ => 1) z t)) θ I L).1
  rw [hθ] at e3
  have hcard : (uni I J).card = I.card + J.card := (h _ _ ℂ (fun _ => 0) (fun _ => 0) I J).2.2.2.1
  set P : S := wd (fun i => Algebra.lmul ℂ S (1 : S)) (fun b' => θ (uni b' L)) I with hP
  set Q : S := wd (fun l => Algebra.lmul ℂ S (z l)) (fun L' => θ (uni I L')) L with hQ
  have hPQ : P + ((-1 : ℤ) ^ I.card) • Q = 0 := e3.symm

  have tA : wd (fun i => T.wt z (inlE (inlE i))) (fun b' => T.mj p θ b (uni (uni b' J) L)) I =
      T.act P (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) := by
    rw [hP, ← wd_act]
    simp only [mj_uni h, hw3, map_one]

  have tB : wd (fun j => T.wt z (inlE (inrE j))) (fun J' => T.mj p θ b (uni (uni I J') L)) J = 0 := by
    have : (fun J' => T.mj p θ b (uni (uni I J') L)) = fun J' =>
        (((-1 : ℤ) ^ ((p + 1) * L.card)) • T.act (θ (uni I L))) (b J') := by
      funext J'
      simp only [mj_uni h, map_zsmul, LinearMap.smul_apply]
    simp only [this, hw4]
    rw [wd_one, hb]
    simp

  have tC : wd (fun l => T.wt z (inrE l)) (fun L' => T.mj p θ b (uni (uni I J) L')) L =
      T.act Q (((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) • b J) := by
    rw [hQ, ← wd_act, wd_at, wd_at]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hc : (L.erase l).card + 1 = L.card := Finset.card_erase_add_one hl
    have hs : ((-1 : ℤ) ^ ((p + 1) * (L.erase l).card)) = (-1 : ℤ) ^ ((p + 1) * (L.card + 1)) := by
      rw [← hc, show (p + 1) * ((L.erase l).card + 1 + 1) = (p + 1) * (L.erase l).card + 2 * (p + 1) by ring,
        pow_add, pow_mul]
      simp
    rw [mj_uni h, hs, hw2]
  have main : wd (T.wt z) (T.mj p θ b) (uni (uni I J) L) =
      T.act P (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J) +
        ((-1 : ℤ) ^ (I.card + J.card)) • T.act Q (((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) • b J) := by
    rw [e1, e2, hcard, tA, tB, tC]
    simp
  rw [main]
  change _ = (0 : E)
  by_cases hJc : J.card = p + 1
  · have hsgn : ((-1 : ℤ) ^ (I.card + J.card)) * ((-1 : ℤ) ^ ((p + 1) * (L.card + 1))) =
        ((-1 : ℤ) ^ I.card) * ((-1 : ℤ) ^ ((p + 1) * L.card)) := by
      rw [hJc, pow_add, show (p + 1) * (L.card + 1) = (p + 1) * L.card + (p + 1) by ring, pow_add]
      have : ((-1 : ℤ) ^ (p + 1)) * ((-1 : ℤ) ^ (p + 1)) = 1 := by
        rw [← mul_pow]; simp
      linear_combination ((-1 : ℤ) ^ I.card * (-1 : ℤ) ^ ((p + 1) * L.card)) * this
    have hPQ' : T.act P + ((-1 : ℤ) ^ I.card) • T.act Q = 0 := by
      rw [← map_zsmul, ← map_add (f := _), hPQ, map_zero]
    have := congrArg (fun f : Module.End ℂ E => f (((-1 : ℤ) ^ ((p + 1) * L.card)) • b J)) hPQ'
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at this
    simp only [map_zsmul, smul_smul] at this ⊢
    rw [hsgn]
    simpa [smul_smul, mul_comm] using this
  · rw [hJ J hJc]
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CubeSignEmb
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubeSignEmb
noncomputable def UpperTheory.Reformulated.B.Qh71.cubeSign :
    {ι : Type} → [LinearOrder ι] → Finset ι → ι → ℤ :=
    fun {ι : Type} [LinearOrder ι] (t : Finset ι) (i : ι) ↦ (-1 : ℤ) ^ {x ∈ t | x < i}.card

theorem UpperTheory.Reformulated.B.Qh71.cubeSign_emb :
    ∀ {κ : Type} [inst : LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n),
      UpperTheory.Reformulated.B.Qh71.cubeSign t ((t.orderEmbOfFin h : Fin n → κ) k) = (-1 : ℤ) ^ (↑k : ℕ) := by
  intro κ _ t n h k
  have key : {x ∈ t | x < t.orderEmbOfFin h k}
      = (Finset.Iio k).map (t.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have hr : x ∈ Set.range (t.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (t.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem t h j, (t.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  unfold UpperTheory.Reformulated.B.Qh71.cubeSign
  rw [key, Finset.card_map, Fin.card_Iio]
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem cubeSign_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n) (k : Fin n) :
    GlobalTheory.cubeSign t (t.orderEmbOfFin h k) = (-1) ^ (k : ℕ) :=
  _root_.UpperTheory.Reformulated.B.Qh71.cubeSign_emb t h k

private theorem erase_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n + 1) (k : Fin (n + 1))
    (h' : (t.erase (t.orderEmbOfFin h k)).card = n) (a : Fin n) :
    (t.erase (t.orderEmbOfFin h k)).orderEmbOfFin h' a = t.orderEmbOfFin h (k.succAbove a) := by
  have := Finset.orderEmbOfFin_unique h' (f := fun a => t.orderEmbOfFin h (k.succAbove a))
    (fun x => Finset.mem_erase.2 ⟨fun hx => Fin.succAbove_ne k x ((t.orderEmbOfFin h).injective hx),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((t.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove k))
  exact (congrFun this a).symm

private theorem detC_erase {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (t : Finset κ)
    (h : t.card = p + 1) (k : Fin (p + 1)) :
    detC ρ (t.erase (t.orderEmbOfFin h k)) =
      (Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b).det := by
  have h' : (t.erase (t.orderEmbOfFin h k)).card = p := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), h]; rfl
  unfold detC
  rw [dite_eq_left h']
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [erase_emb t h k h' a]

private theorem ring_core {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (f : Fin p → S)
    (t : Finset κ) (h : t.card = p + 1) :
    ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) = 0 := by
  set e := t.orderEmbOfFin h with he
  let A : Matrix (Fin (p + 1)) (Fin (p + 1)) S :=
    Matrix.of fun a => Fin.cons (∑ b, ρ (e a) b * f b) (ρ (e a))
  have hA : A.det = 0 := by
    have h1 := Matrix.det_updateCol_sum A 0 (Fin.cons 0 f : Fin (p + 1) → S)
    have h2 : (A.updateCol 0 fun k => ∑ i, (Fin.cons 0 f : Fin (p + 1) → S) i • A k i) = A := by
      ext a b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp [A, Matrix.updateCol_apply, Fin.sum_univ_succ, mul_comm]
      · simp [A, Matrix.updateCol_apply, Fin.succ_ne_zero]
    rw [h2] at h1
    simpa using h1
  have ht : t = Finset.univ.map e.toEmbedding := by
    rw [he, Finset.map_orderEmbOfFin_univ]
  have hs : ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) =
      ∑ k : Fin (p + 1), (((-1 : ℤ) ^ (k : ℕ) : ℤ) : S) * ((∑ b, ρ (e k) b * f b) * detC ρ (t.erase (e k))) := by
    conv_lhs => rw [show (∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i))) =
      ∑ i ∈ Finset.univ.map e.toEmbedding, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * detC ρ (t.erase i)) by
        rw [← ht]]
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RelEmbedding.coe_toEmbedding]
    rw [he, cubeSign_emb t h k]
  rw [hs, ← hA, Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he, detC_erase ρ t h k]
  have : (A.submatrix k.succAbove Fin.succ) = Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b := by
    ext a b
    simp [A, he]
  rw [this]
  simp [A, he, mul_assoc]

theorem UpperTheory.Gal.productCup_of_system.det_of :
    Det := by
  intro S E _ _ _ _ act κ _ p ρ f m
  funext t
  have key : wd (fun l => act (∑ b, ρ l b * f b)) (fun s => act (detC ρ s) m) t =
      ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • act (∑ b, ρ i b * f b) (act (detC ρ (t.erase i)) m) := by
    simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [key]
  by_cases h : t.card = p + 1
  · have h0 := congrArg (fun x => act x m) (ring_core ρ f t h)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_zero, LinearMap.zero_apply, map_sum, LinearMap.sum_apply] at h0
    rw [Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zsmul_eq_mul, map_zsmul, LinearMap.smul_apply, map_mul, Module.End.mul_apply]
  · rw [Pi.zero_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ p := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [detC, hc]
end
