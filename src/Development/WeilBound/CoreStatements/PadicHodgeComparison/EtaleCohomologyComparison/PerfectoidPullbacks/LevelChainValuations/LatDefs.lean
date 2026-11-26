module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Pb.Lat

section Inj
variable {A B : Type} [CommRing A] [CommRing B] (ι : A →+* B) {J : Ideal B} (δ : DividedPowers J)

def DPClosed : Prop := ∀ x : A, ι x ∈ J → ∀ n : ℕ, ∃ y : A, ι y = δ.dpow n (ι x)

variable {ι δ}

def dpowC (h : DPClosed ι δ) (n : ℕ) (x : A) : A := by
  classical exact if hx : ι x ∈ J then Classical.choose (h x hx n) else 0

theorem dpowC_spec (h : DPClosed ι δ) {n : ℕ} {x : A} (hx : ι x ∈ J) : ι (dpowC h n x) = δ.dpow n (ι x) := by
  rw [dpowC, dite_eq_left hx]; exact Classical.choose_spec (h x hx n)

def dpComap (hι : Function.Injective ι) (h : DPClosed ι δ) : DividedPowers (J.comap ι) where
  dpow := dpowC h
  dpow_null {n x} hx := by rw [dpowC, dite_eq_right (show ¬ ι x ∈ J from hx)]
  dpow_zero {x} hx := hι (by rw [dpowC_spec h hx, δ.dpow_zero hx, map_one])
  dpow_one {x} hx := hι (by rw [dpowC_spec h hx, δ.dpow_one hx])
  dpow_mem {n x} hn hx := by
    show ι _ ∈ J
    rw [dpowC_spec h hx]; exact δ.dpow_mem hn hx
  dpow_add {n x y} hx hy := hι (by
    have hxy : ι (x + y) ∈ J := by rw [map_add (f := _)]; exact J.add_mem hx hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dpowC_spec h hxy, map_add (f := _), δ.dpow_add hx hy, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, dpowC_spec h hx, dpowC_spec h hy])
  dpow_mul {n a x} hx := hι (by
    have hax : ι (a * x) ∈ J := by rw [map_mul]; exact J.mul_mem_left _ hx
    rw [dpowC_spec h hax, map_mul, δ.dpow_mul hx, map_mul, map_pow, dpowC_spec h hx])
  mul_dpow {m n x} hx := hι (by
    rw [map_mul, map_mul, dpowC_spec h hx, dpowC_spec h hx, dpowC_spec h hx, δ.mul_dpow hx, map_natCast])
  dpow_comp {m n x} hn hx := hι (by
    have h1 : ι (dpowC h n x) ∈ J := by rw [dpowC_spec h hx]; exact δ.dpow_mem hn hx
    rw [dpowC_spec h h1, dpowC_spec h hx, δ.dpow_comp hn hx, map_mul, map_natCast, dpowC_spec h hx])

theorem dpComap_dpow (hι : Function.Injective ι) (h : DPClosed ι δ) {n : ℕ} {x : A} (hx : ι x ∈ J) :
    ι ((dpComap hι h).dpow n x) = δ.dpow n (ι x) := dpowC_spec h hx

end Inj

section Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

def η : B := ((l : ℚ) ^ M)⁻¹ • f ξ

def dpE (i : ℕ) : B := ((i.factorial : ℚ))⁻¹ • η f ξ l M ^ i

def sub : Subring B := Subring.closure (Set.range f ∪ Set.range (dpE f ξ l M))

def A : Type := ↥(sub f ξ l M)

instance : CommRing (A f ξ l M) := inferInstanceAs (CommRing ↥(sub f ξ l M))

def ι : A f ξ l M →+* B := (sub f ξ l M).subtype

theorem ι_injective : Function.Injective (ι f ξ l M) := Subtype.val_injective

def ofW : W →+* A f ξ l M := f.codRestrict (sub f ξ l M) fun w => Subring.subset_closure (Or.inl ⟨w, rfl⟩)

theorem ι_ofW (w : W) : ι f ξ l M (ofW f ξ l M w) = f w := rfl

def dpA (i : ℕ) : A f ξ l M := ⟨dpE f ξ l M i, Subring.subset_closure (Or.inr ⟨i, rfl⟩)⟩

theorem ι_dpA (i : ℕ) : ι f ξ l M (dpA f ξ l M i) = dpE f ξ l M i := rfl

def IB : Ideal B := Ideal.span {f ξ}

def γB : DividedPowers (IB f ξ) := by classical exact DividedPowers.RatAlgebra.dividedPowers (IB f ξ)

def I : Ideal (A f ξ l M) := (IB f ξ).comap (ι f ξ l M)

def γ (h : DPClosed (ι f ξ l M) (γB f ξ)) : DividedPowers (I f ξ l M) := dpComap (ι_injective f ξ l M) h

theorem ι_γ (h : DPClosed (ι f ξ l M) (γB f ξ)) {n : ℕ} {x : A f ξ l M} (hx : x ∈ I f ξ l M) :
    ι f ξ l M ((γ f ξ l M h).dpow n x) = (γB f ξ).dpow n (ι f ξ l M x) := dpComap_dpow _ h hx

structure Hyp (m : ℕ) : Prop where
  one_le : 1 ≤ m
  nil : f ξ ^ m = 0
  gr : ∀ i < m, ∀ (a : W) (b : B), f a * f ξ ^ i = f ξ ^ (i + 1) * b → ξ ∣ a
  dom : IsDomain (W ⧸ Ideal.span {ξ})
  val : ∀ x y : W ⧸ Ideal.span {ξ}, x ∣ y ∨ y ∣ x
  dv : ∀ x : W ⧸ Ideal.span {ξ}, x ≠ 0 → ∃ n : ℕ, x ∣ (l : W ⧸ Ideal.span {ξ}) ^ n
  l0 : (l : W ⧸ Ideal.span {ξ}) ≠ 0
  cpl : IsAdicComplete (Ideal.span {(l : W ⧸ Ideal.span {ξ})}) (W ⧸ Ideal.span {ξ})
  unit : ∀ n : ℕ, n ≠ 0 → ∃ (k : ℕ) (u : W), (n : W) * u = (l : W) ^ k

end Lat

section Map
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

def map (g : B →+* B') (h : ∀ x ∈ sub f ξ l M, g x ∈ sub f' ξ' l M) : A f ξ l M →+* A f' ξ' l M :=
  g.restrict (sub f ξ l M) (sub f' ξ' l M) h

theorem ι_map (g : B →+* B') (h : ∀ x ∈ sub f ξ l M, g x ∈ sub f' ξ' l M) (x : A f ξ l M) :
    ι f' ξ' l M (map f ξ f' ξ' l M g h x) = g (ι f ξ l M x) := rfl

end Map

end CrystallineSemistableComparison.Pb.Lat
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

universe u

namespace CrystallineSemistableComparison.Pb.Kap

structure Chain (Λ A B K : Type) [CommRing Λ] [CommRing A] [CommRing B] [Field K] where
  ℓ : ℕ
  S : ℕ → ℕ → Type u
  [sab : ∀ n j, AddCommGroup (S n j)]
  [smd : ∀ n j, Module Λ (S n j)]
  Zn : ℕ → ℕ → Type u
  [znab : ∀ n j, AddCommGroup (Zn n j)]
  [znmd : ∀ n j, Module A (Zn n j)]
  Z : ℕ → Type u
  [zab : ∀ j, AddCommGroup (Z j)]
  [zmd : ∀ j, Module A (Z j)]
  W : ℕ → Type u
  [wab : ∀ j, AddCommGroup (W j)]
  [wmd : ∀ j, Module B (W j)]
  V : ℕ → Type u
  [vab : ∀ j, AddCommGroup (V j)]
  [vmd : ∀ j, Module K (V j)]
  lam : Λ →+* A
  ι : A →+* B
  o : K →+* B
  tS : ∀ n j, S (n + 1) j →ₗ[Λ] S n j
  tZ : ∀ n j, Zn (n + 1) j →ₗ[A] Zn n j
  r : ∀ n j, S n j →ₛₗ[lam] Zn n j
  red : ∀ n j, Z j →ₗ[A] Zn n j
  b : ∀ j, Z j →ₛₗ[ι] W j
  μ : ∀ j, V j →ₛₗ[o] W j

attribute [instance] Chain.sab Chain.smd Chain.znab Chain.znmd Chain.zab Chain.zmd Chain.wab Chain.wmd Chain.vab Chain.vmd

variable {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]

namespace Chain

variable (C : Chain.{u} Λ A B K)

def Comp {j : ℕ} (x : ∀ n, C.S n j) : Prop := ∀ n, C.tS n j (x (n + 1)) = x n

structure Good : Prop where
  unit : IsUnit (C.ℓ : B)
  fin : ∀ j, FiniteDimensional K (C.V j)
  basis : ∀ (j : ℕ) {m : ℕ} (bs : Module.Basis (Fin m) K (C.V j)) (w : C.W j),
    ∃! g : Fin m → B, w = ∑ s, g s • C.μ j (bs s)
  r_tr : ∀ n j (x : C.S (n + 1) j), C.tZ n j (C.r (n + 1) j x) = C.r n j (C.tS n j x)
  red_tr : ∀ n j (z : C.Z j), C.tZ n j (C.red (n + 1) j z) = C.red n j z
  lift : ∀ j (x : ∀ n, C.S n j), C.Comp x → ∃ (e : ℕ) (z : C.Z j), ∀ n, C.red n j z = ((C.ℓ : A) ^ e) • C.r n j (x n)
  sep : ∀ j (z : C.Z j), (∀ n, C.red n j z = 0) → C.b j z = 0

def Rho {j : ℕ} (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B) : Prop :=
  (∀ (k : K) (φ : Module.Dual K (C.V j)), f (k • φ) = C.o k * f φ) ∧
  ∃ (e : ℕ) (z : C.Z j), (∀ n, C.red n j z = ((C.ℓ : A) ^ e) • C.r n j (x n)) ∧
    ∀ {m : ℕ} (bs : Module.Basis (Fin m) K (C.V j)), ((C.ℓ : B) ^ e) • ∑ s, f (bs.coord s) • C.μ j (bs s) = C.b j z

end Chain

structure Hom {Λ' A' B' : Type} [CommRing Λ'] [CommRing A'] [CommRing B'] (C : Chain.{u} Λ A B K)
    (C' : Chain.{u} Λ' A' B' K) where
  sΛ : Λ →+* Λ'
  sA : A →+* A'
  sB : B →+* B'
  fS : ∀ n j, C.S n j →ₛₗ[sΛ] C'.S n j
  fZn : ∀ n j, C.Zn n j →ₛₗ[sA] C'.Zn n j
  fZ : ∀ j, C.Z j →ₛₗ[sA] C'.Z j
  fW : ∀ j, C.W j →ₛₗ[sB] C'.W j
  fV : ∀ j, C.V j →ₗ[K] C'.V j

structure Hom.Good {Λ' A' B' : Type} [CommRing Λ'] [CommRing A'] [CommRing B'] {C : Chain.{u} Λ A B K}
    {C' : Chain.{u} Λ' A' B' K} (h : Hom C C') : Prop where
  ℓ : C'.ℓ = C.ℓ
  lam : ∀ c, h.sA (C.lam c) = C'.lam (h.sΛ c)
  ι : ∀ a, h.sB (C.ι a) = C'.ι (h.sA a)
  o : ∀ k, h.sB (C.o k) = C'.o k
  tS : ∀ n j x, h.fS n j (C.tS n j x) = C'.tS n j (h.fS (n + 1) j x)
  r : ∀ n j x, h.fZn n j (C.r n j x) = C'.r n j (h.fS n j x)
  red : ∀ n j z, h.fZn n j (C.red n j z) = C'.red n j (h.fZ j z)
  b : ∀ j z, h.fW j (C.b j z) = C'.b j (h.fZ j z)
  μ : ∀ j v, h.fW j (C.μ j v) = C'.μ j (h.fV j v)

def Hom.tr {Λ' A' B' : Type} [CommRing Λ'] [CommRing A'] [CommRing B'] {C : Chain.{u} Λ A B K}
    {C' : Chain.{u} Λ' A' B' K} (h : Hom C C') (j : ℕ) (f : Module.Dual K (C.V j) →+ B) :
    Module.Dual K (C'.V j) →+ B' :=
  h.sB.toAddMonoidHom.comp (f.comp (Module.Dual.transpose (R := K) (h.fV j)).toAddMonoidHom)

structure Cup (C : Chain.{u} Λ A B K) where
  cS : ∀ n i j, C.S n i →ₗ[Λ] C.S n j →ₗ[Λ] C.S n (i + j)
  cZn : ∀ n i j, C.Zn n i →ₗ[A] C.Zn n j →ₗ[A] C.Zn n (i + j)
  cZ : ∀ i j, C.Z i →ₗ[A] C.Z j →ₗ[A] C.Z (i + j)
  cW : ∀ i j, C.W i →ₗ[B] C.W j →ₗ[B] C.W (i + j)
  cV : ∀ i j, C.V i →ₗ[K] C.V j →ₗ[K] C.V (i + j)
  oneS : ∀ n, C.S n 0
  oneZ : C.Z 0
  oneV : C.V 0

structure Cup.Good {C : Chain.{u} Λ A B K} (P : Cup C) : Prop where
  r : ∀ n i j x y, C.r n (i + j) (P.cS n i j x y) = P.cZn n i j (C.r n i x) (C.r n j y)
  red : ∀ n i j z w, C.red n (i + j) (P.cZ i j z w) = P.cZn n i j (C.red n i z) (C.red n j w)
  b : ∀ i j z w, C.b (i + j) (P.cZ i j z w) = P.cW i j (C.b i z) (C.b j w)
  μ : ∀ i j v w, C.μ (i + j) (P.cV i j v w) = P.cW i j (C.μ i v) (C.μ j w)
  tS : ∀ n i j x y, C.tS n (i + j) (P.cS (n + 1) i j x y) = P.cS n i j (C.tS n i x) (C.tS n j y)
  oneS_tr : ∀ n, C.tS n 0 (P.oneS (n + 1)) = P.oneS n
  one_r : ∀ n, C.red n 0 P.oneZ = C.r n 0 (P.oneS n)
  one_b : C.b 0 P.oneZ = C.μ 0 P.oneV

end CrystallineSemistableComparison.Pb.Kap
end
end
