module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

structure BK (K : FinExt l) where

  a : ℕ
  [a_ne : NeZero a]

  Ep : Polynomial (Wq l a)
  monic : Ep.Monic
  deg_pos : 0 < Ep.natDegree
  dvd_coeff : ∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i
  coeff_zero : ∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w
  not_expand : ∃ i, ¬ l ∣ i ∧ Ep.coeff i ≠ 0

  str : ↥(OL K) ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)})
  isUnit_δ : IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧))
  complete : IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧

  flat : OCb l

  ev : (Wq l a)⟦X⟧ →+* Ainf l
  ev_X : ev X = WittVector.teichmuller l flat
  ev_C : ∀ w, ev (C w) = wA l a w
  ev_frob : ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x)
  span_ev : Ideal.span {ev (Ep : (Wq l a)⟦X⟧)} = RingHom.ker (Per.θ l)
  θ_ev : ∀ (r : ↥(OL K)) (x : (Wq l a)⟦X⟧), Ideal.Quotient.mk _ x = str r → Per.θ l (ev x) = intToOC K r
  gal_w : ∀ (g : ↥(GK K)) (w : Wq l a), Per.σA (g : GQ l) (wA l a w) = wA l a w

attribute [instance] BK.a_ne

namespace BK

variable {K : FinExt l} (bk : BK K)

abbrev S : Type := (Wq l bk.a)⟦X⟧

abbrev E : bk.S := (bk.Ep : (Wq l bk.a)⟦X⟧)

theorem E_ne_zero : bk.E ≠ 0 := fun h => bk.monic.ne_zero (Polynomial.coe_eq_zero_iff.1 h)

def prism : Obj l ↥(OL K) where
  A := bk.S
  D := deltaS l bk.a
  I := Ideal.span {bk.E}
  inv := invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero bk.E_ne_zero)
  complete := bk.complete
  l_mem := Delta.l_mem_of_isUnit hl.out.pos _ bk.isUnit_δ
  bdd := ⟨0, fun x ⟨m, hm⟩ => by
    have h := congrArg bk.str.symm hm
    rw [map_mul, map_pow, map_natCast, map_zero] at h
    have h2 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
    rw [pow_zero, one_mul]
    exact bk.str.symm.injective (h2.trans (map_zero _).symm)⟩
  str := bk.str.toRingHom

def toP : bk.S ≃+* bk.prism.A := RingEquiv.refl _


variable {bk} in
def hf {B : Obj l ↥(OL K)} (f : Hom bk.prism B) : bk.S →+* B.A := f.f

def ι : Hom bk.prism (ainfObj K) where
  f := bk.ev
  f_δ := (deltaS l bk.a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree bk.ev bk.ev_frob
  f_I x hx := by
    obtain ⟨y, rfl⟩ := (Ideal.mem_span_singleton' (α := bk.S)).1 hx
    change bk.ev (y * bk.E) ∈ RingHom.ker (Per.θ l)
    rw [← bk.span_ev, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  f_str r x h := ((isAinf_ainfObj K).mk_eq_str_iff r (bk.ev x)).2 (bk.θ_ev r x h)

abbrev J : Ideal bk.S := Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E}

def ρ₀ : ℝ≥0 := (l : ℝ≥0) ^ (-(1 / (bk.Ep.natDegree : ℝ)))

def evW : bk.S →+* WCb l := (inclW l).comp bk.ev

def FixFlat (g : ↥(GK K)) : Prop := Per.σF (g : GQ l) bk.flat = bk.flat

def IsPer (τ : Ainf l) : Prop :=
  WittVector.frobenius τ = bk.ev bk.E * τ ∧ ∃ (ε : OCb l) (η : (Ainf l)ˣ), GlobalTheory.MemLoc.IsEps ε ∧
    WittVector.frobenius τ = η * (WittVector.teichmuller l ε - 1)

def OE : Subring (WCb l) where
  carrier := {w | ∀ n : ℕ, ∃ (m : ℕ) (s : bk.S) (y : WCb l), bk.evW X ^ m * w = bk.evW s + (l : WCb l) ^ n * y}
  zero_mem' _ := ⟨0, 0, 0, by simp⟩
  one_mem' _ := ⟨0, 1, 0, by simp⟩
  neg_mem' hw n := by
    obtain ⟨m, s, y, h⟩ := hw n
    exact ⟨m, -s, -y, by rw [map_neg]; linear_combination -h⟩
  add_mem' hw hw' n := by
    obtain ⟨m, s, y, h⟩ := hw n
    obtain ⟨m', s', y', h'⟩ := hw' n
    refine ⟨m + m', X ^ m' * s + X ^ m * s', bk.evW X ^ m' * y + bk.evW X ^ m * y', ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow]
    linear_combination bk.evW X ^ m' * h + bk.evW X ^ m * h'
  mul_mem' {w w'} hw hw' n := by
    obtain ⟨m, s, y, h⟩ := hw n
    obtain ⟨m', s', y', h'⟩ := hw' n
    refine ⟨m + m', s * s', bk.evW s * y' + y * (bk.evW X ^ m' * w'), ?_⟩
    rw [map_mul]
    linear_combination (bk.evW X ^ m' * w') * h + bk.evW s * h'

abbrev DS (ρ : ℝ≥0) : Type := Disc l (X : bk.S) ρ

abbrev DA (ρ : ℝ≥0) : Type := Disc l (bk.ev X) ρ

abbrev iA : Ainf l →+* bk.DA bk.ρ₀ := toDisc l (bk.ev X) bk.ρ₀

abbrev iS : bk.S →+* bk.DA bk.ρ₀ := bk.iA.comp bk.ev

end BK

abbrev Digits (l : ℕ) : Type := {α : ℕ →₀ ℕ // ∀ i, α i < l}

structure Env {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) where

  Q : Obj l ↥(OL K)

  inl : Hom B Q

  inr : Hom bk.prism Q
  univ : ∀ (C : Obj l ↥(OL K)) (f : Hom B C) (g : Hom bk.prism C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g

  w : Q.A
  w_eq : BK.hf inr X = inl.f p + inl.f d * w
  I_eq : Q.I = Ideal.span {inl.f d}

  tb : TopBasis inl.f (Ideal.span {(l : B.A)} ⊔ B.I) (Digits l)
  tb_b : ∀ α, tb.b α = α.1.prod fun i n => (Q.D.δ^[i] w) ^ n

def IsFrame {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) : Prop :=
  B.I = Ideal.span {d} ∧ Ideal.Quotient.mk B.I p = B.str (bk.str.symm (Ideal.Quotient.mk _ X))

structure Strat {K : FinExt l} (bk : BK K) (d : ℕ) where

  a : ℕ

  b : ℕ

  A : Matrix (Fin d) (Fin d) bk.S

  A' : Matrix (Fin d) (Fin d) bk.S
  A_mul : A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S)

  ε : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Matrix (Fin d) (Fin d) B.A
  ε_refl : ∀ {B} (f : Hom bk.prism B), ε f f = 1
  ε_trans : ∀ {B} (f g h : Hom bk.prism B), ε f g * ε g h = ε f h
  ε_nat : ∀ {B B'} (k : Hom B B') (f g : Hom bk.prism B), (ε f g).map k.f = ε (k.comp f) (k.comp g)
  ε_φ : ∀ {B} (f g : Hom bk.prism B), BK.hf g bk.E ^ a • (A.map (BK.hf f) * (ε f g).map B.D.φ) =
    BK.hf f bk.E ^ a • (ε f g * A.map (BK.hf g))

structure Framed {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) : Prop where
  tr : ∀ {B} (f g : Hom bk.prism B) (j : Fin d), M.tr g (e j) = ∑ i, S.ε f g i j • M.tr f (e i)
  Φ : ∀ j : Fin d, IsFrac (bk.toP bk.E)
    (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (S.A i j) • e i) S.a

structure IsStratHom {K : FinExt l} {bk : BK K} {d d' : ℕ} (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S) : Prop where
  φ : bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A)
  ε : ∀ {B} (f g : Hom bk.prism B), S'.ε f g * Y.map (BK.hf g) = Y.map (BK.hf f) * S.ε f g

abbrev zW {m n : Type} (M : Matrix m n ℤ_[l]) : Matrix m n (WCb l) := M.map (algebraMap ℤ_[l] (WCb l))

structure MReal {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (T : Matrix (Fin d) (Fin d) (WCb l)) : Prop where
  unit : IsUnit T
  φ : bk.evW bk.E ^ S.a • T.map (frobW l) = T * S.A.map bk.evW
  gal : ∀ g : ↥(GK K), zW (ρ g) * T.map (galW l (g : GQ l)) =
    T * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)

structure Seed {K : FinExt l} (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) where

  N : ℕ

  c₁ : ℕ

  c₂ : ℕ

  c₃ : ℕ

  F : Matrix (Fin d) (Fin d) (Wq l bk.a)

  F' : Matrix (Fin d) (Fin d) (Wq l bk.a)
  F_mul : F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))

  X : Matrix (Fin d) (Fin d) bk.S

  X' : Matrix (Fin d) (Fin d) bk.S
  X_mul : X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) bk.S)
  nopole : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j,
    BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j

  W : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)

  W' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  W_mul : W * W' = bk.iA τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
  φ : ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ →
    ((l : bk.DA bk.ρ₀) ^ c₁) • (W * X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ N • (W * X'.map bk.iS * F.map (bk.iS.comp C))
  gal : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G →
    bk.iA (bk.ev bk.E * τ) ^ N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (W * X'.map bk.iS).map G) =
      bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ^ N • (W * X'.map bk.iS)

structure Height {K : FinExt l} {bk : BK K} {d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l}
    (s : Seed bk d ρ τ) where

  Y : Matrix (Fin d) (Fin d) (Ainf l)
  unit : IsUnit (Y.map (inclW l))

  Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)
  Z_unit : IsUnit Z
  W_mul : ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA

  a : ℕ

  b : ℕ

  A : Matrix (Fin d) (Fin d) bk.S

  A' : Matrix (Fin d) (Fin d) bk.S
  A_mul : A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S)
  φ : bk.ev bk.E ^ a • Y.map WittVector.frobenius = Y * A.map bk.ev

def Strat.unit {K : FinExt l} (bk : BK K) (d : ℕ) : Strat bk d where
  a := 0
  b := 0
  A := 1
  A' := 1
  A_mul := by simp
  ε _ _ := 1
  ε_refl _ := rfl
  ε_trans _ _ _ := mul_one _
  ε_nat k _ _ := Matrix.map_one _ (map_zero _) (map_one _)
  ε_φ f g := by
    rw [pow_zero, pow_zero, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

namespace GlobalTheory.LamTie

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def Over4 (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  (∃ k, OverP H (H.g k) w) ∨ OverP H H.pde w ∨ OverP H H.pde' w

structure IsAuxiliaryHeckeCharacter (w0 : HeightOneSpectrum (𝓞 H.E)) (c : R.Psi → ℤ) (χ : Formalism.L2.Host.HChar H.E) : Prop where

  unitary : χ.IsUnitary

  triv : χ.TrivOn H.F

  inf : χ.HasInfQ (embPsi H) fun g => (c g : ℚ)

  unr : ∀ w, ¬ Over4 H w → below w ≠ below w0 → χ.UnrAt w

  two : ∀ w, Over4 H w → ExpAt χ w 2

  one : ∀ w, below w = below w0 → ExpAt χ w 1

def cond0 (w0 : HeightOneSpectrum (𝓞 H.E)) : Ideal (OF H.E) :=
  Ideal.span {((H.g 0 * H.g 1 * H.pde * H.pde' : ℕ) : OF H.E)} ^ 2 * (below w0).asIdeal

structure PlacesOk (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)) : Prop where

  referencePlaceOverPrime : OverP H q0 w0

  distinct : [H.g 0, H.g 1, H.pde, H.pde', q0].Nodup

  splits : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr H.E ∧
    ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p

def phi (g : R.Psi) : H.E →+* ℂ := ComplexEmbedding.conjugate (embPsi H g)

end Host

structure LamDat (D : D7) where

  C : CharFrame D

  q0 : ℕ

  w0 : HeightOneSpectrum (𝓞 D.host.E)

  c : Fin D.R.m → D.R.Psi → ℤ

  chi : Fin D.R.m → Formalism.L2.Host.HChar D.host.E

namespace LamDat

variable {D : D7} (Z : LamDat D)

def lam0 (l : ℕ) (j a : Fin D.R.m) : Formalism.L2.Host.HChar D.host.E := Z.C.mu0 j * Z.C.delAt l * (Z.chi a)⁻¹

def kap (j a : Fin D.R.m) (s : ℕ) (g : D.R.Psi) : ℕ := (⌊eExp D j g⌋ + Z.c a g - s).toNat

structure Ok : Prop where

  places : PlacesOk D.host Z.q0 Z.w0

  aux : ∀ a, IsAuxiliaryHeckeCharacter D.host Z.w0 (Z.c a) (Z.chi a)

  big : ∀ j a g, (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + Z.c a g

end LamDat

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsThOf (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF D.host.E)) (χ : Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∃ u : Kbar X i, u ≠ 0 ∧ ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
    ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
      IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
      ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def IsThEmpty (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF D.host.E)) (χ : Formalism.L2.Host.HChar D.host.E) : Prop :=
  ∃ (u : Kbar X i) (T : ℂ), u ≠ 0 ∧ IsToricSum φ s κ 𝔣 χ T ∧
    algebraMap (FractionRing (X.O i)) (Kbar X i) (∑ δ, X.th i ∅ lam δ) = u * ι T

def IsLam (Z : LamDat D) (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (j a : Fin D.R.m) (s : ℕ) : Prop :=
  j.1 + 1 = X.jL i lam ∧ BlochKatoReduction.Gen.SOk X i lam s ∧
    ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (((Z.lam0 (X.l i) j a).val P : ℂˣ) : ℂ) = 1

def IsLamTie (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → (∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i) ∧
    ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      ∀ lam : X.abelian₂ i, ∃ (j a : Fin D.R.m) (s : ℕ), IsLam X Z i (atSide X (X.sideL i lam) ι) lam j a s ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

def IsLamTie0 (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, ∃ (ι : ℂ →+* Kbar X i) (j a : Fin D.R.m) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s ∧
    IsThEmpty X i ι lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

end Record

section Examples

end Examples

end GlobalTheory.LamTie
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Polynomial Module TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

variable {D : D7}

def EigSpan (P : PairedCharacterCondition.Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (x : D.nd.X i) (c : D.nd.O i),
    (∀ PI : D.naut.AV i, D.naut.ptV i PI = some x → ∀ F ∈ D.naut.typeV i PI,
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
        iotaO D.nd D.naut i c • F) →
    ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, (P.zO i z).baseChange (FractionRing (D.nd.O i)) u = c • u


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def LocBoundP (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ) : Prop :=
  BlochKatoDuality.lenMod (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Xs M))
                   (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤
    (e : ℕ∞) * lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw)

def TypeLocus (P : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (k : Fin 2) (Xs : Set (D.nd.X i)) : Prop :=
  ∃ s : D.nd.PlG k → (ZMod (D.host.g k))[X],
    (∀ v, Squarefree (s v) ∧ ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ (s v).IsRoot (u : ZMod (D.host.g k))) ∧
    ∀ x ∈ Xs, ∃ PI : D.naut.AV i, D.naut.ptV i PI = some x ∧ ∀ v, ∃ τ ∈ P.kty i PI k v, (P.lz k).lab τ = s v

def TypeLGC (P : PairedCharacterCondition.Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
  ∀ (x : D.nd.X i) (PI : D.naut.AV i), D.naut.ptV i PI = some x → ∀ (v : D.nd.PlG k), ∀ τ ∈ P.kty i PI k v,
    Squarefree ((P.lz k).lab τ) →
    (∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ).IsRoot (u : ZMod (D.host.g k))) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ u : (ZMod (D.host.g k))ˣ, (u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹) ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (M : Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
        (w = D.naut.plGw k v ∧
          M = Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)) ∨
        (IsConjPl D.host (D.naut.plGw k v) w ∧
          M = (Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)) →
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        D.naut.mono0 (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) ∧
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
          D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) σ =
            (M.map fun y => X - C (P.om k w y σ)).prod

def CentralElt (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (s : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))[X]),
    ∃ (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
      (L : List (Σ k : Fin 2, D.nd.PlG k)), L.Nodup ∧ (∀ kv, kv ∈ L) ∧
      mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
        (D.what₂.restRowsFiniteGroupCard : ℂ) • (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod

def StepDeg : Prop :=
  ∀ D : D7, tieBr (D := D) → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
    (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f ∧
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1

def StepPotDirect : Prop :=
  ∀ (D : D7) (P : Pend D), TypeLGC P → FontaineAtPlacesOverL (D := D) → SumRepresentations.tie0 D → tieBr (D := D) → tiePH (D := D) →
    tieChi (D := D) → InertEq D → ElementDenominator.adm12 D → PcrisTensorL D.loc → TieInePoly D →
    ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ Xs : Set (D.nd.X i), π ∈ Xs → TypeLocus P i k Xs →
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1)

def StepJumpDirect : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (eta s S : ℕ)
    (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ),
    eta + D.R.t + 1 < s → HostJ i r eta s S sg U →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      sg w = true →
      JumpFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) (D.R.nV + 1) (eta + D.R.t + 1) (s + S)

def StepJumpDual : Prop :=
  ∀ D : D7, DualJumpL D.loc → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (eta s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool)
      (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), eta + D.R.t + 1 < s → HostJ i r eta s S sg U →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      sg w = false → PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      JumpFam i w hw (fun x : ↥Xs => rDuO D.nd i r x) (D.R.nV + 1) (eta + D.R.t + 1) (s + S)

def StepLift : Prop :=
  ∀ (D : D7) (CT : ℕ), admT (D := D) CT → FontaineAtPlacesOverL (D := D) →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ (ι : Type) (Ms : ι → (GE D.nd →* Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))),
      (∀ x, Continuous fun g => Ms x g) → ∀ eta H : ℕ, eta + D.R.t + 1 < H →
      CT * (H * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.nd.l i →
      PotFam i w hw Ms (D.R.nV + 1) → JumpFam i w hw Ms (D.R.nV + 1) (eta + D.R.t + 1) H →
      LiftFamW i w hw Ms (eMax D CT eta)

def StepSub : Prop :=
  ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      SubTw i r Xs (WpO D.nd i ρ π) ∧ ∀ c ∈ Finset.Icc 1 D.R.t, SubTw i r Xs (chiRatO D.nd i c)

def StepLocDirect : Prop :=
  ∀ D : D7, LocalPushoutProposition (D := D) → admBK (D := D) → FontaineAtPlacesOverL (D := D) → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ n e : ℕ, PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
      LocBoundP i w hw r Xs M (2 * k * e)

def StepLocDual : Prop :=
  ∀ D : D7, LocalPushoutProposition (D := D) → admBK (D := D) → FontaineAtPlacesOverL (D := D) → PotDRL D.loc →
    ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
    ∀ n e : ℕ, PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
      LiftFamW i w hw (fun x : ↥Xs => rDuO D.nd i r x) e →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
      LocBoundP i w hw r Xs M (2 * k * e)

def StepHfChar : Prop :=
  ∀ (D : D7) (_ : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admTB (D := D) HW F → InertEq D →
    ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → D.nd.l i ≠ 2 →
    ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
      HfChar i w hw

def StepCentral : Prop := CentralIdemCoeff → ∀ (D : D7) (_ : Pend D), CentralElt D

end GlobalTheory.Pass

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.ResSel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)


variable (X) in
def IsCj (g g' : GE N) : Prop := ∀ x, g' x = X.cc (g (X.cc.symm x))

def IsDual (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Prop :=
  ∀ g, (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = Tdual i s g

def ResTriv (g : GE N) : Prop :=
  (Tmat i s g).map (IsLocalRing.residue (X.O0 i)) = 1 ∧ IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1

def Small (L : Subgroup (GE N)) (z : GE N) : Prop :=
  IsOpen (L : Set (GE N)) ∧ L.Normal ∧ (∀ g g', IsCj X g g' → (g ∈ L ↔ g' ∈ L)) ∧ (∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ g ∈ L, ResTriv i s g

section Field

variable (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]

def IsRes : Prop := ∀ x ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) K x = 0

def ResIso : Prop :=
  ∃ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A ∧
    ∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)

abbrev red (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Representation K (GE N) (Fin D.R.r → K) := repOn ρ (1 : GE N →* Kˣ) K

variable {i K}

abbrev cl {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) : H1 (red i K ρ) := Submodule.Quotient.mk x

def form {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) (y : Z1 (red i K ρ')) (g h g' h' : GE N) : K :=
  x.1 g ⬝ᵥ y.1 h - x.1 g' ⬝ᵥ y.1 h'

end Field

def SpanOdd : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ¬ ResIso i s K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ (n n' : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n' → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → LinearIndependent K (fun b => cl (y b)) → ∀ c : Fin n → Fin n' → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → c = 0

def SpanTwo : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A →
      (∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)) →
    ∀ (n : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → (∀ a g g', IsCj X g g' → (y a).1 g' = A.mulVec ((x a).1 g)) →
      ∀ c : Fin n → Fin n → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → ∀ a b, c a b = c b a

def EqDim : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    Module.Finite K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) ∧ Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅) ∧
      Module.finrank K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) = Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅)

def Position (M : ℕ) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (φ φ' : Fin R → GE N) : Prop :=
  SlopeTestRemainingChoices X i M ∅ P d ∧ (∃ z L, IsTameInertiaElementAtTwistPrime X i z ∧ Small i s L z ∧ Steps X i M L z P d) ∧
    ∀ a, (∀ g ∈ DecV N (P (.inr a)), ResTriv i s g) ∧ IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧
      IsCj X (φ a) (φ' a)

def FirstHalf : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ', 1 ≤ M → Position i s M P d φ φ' →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ a v, Over (P (.inl a)) v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

def FirstPlace : Prop :=
  ∀ (P : PlE D.host) (z : GE N) (L : Subgroup (GE N)), IsTameInertiaElementAtTwistPrime X i z → Small i s L z →
    (∀ v, Over P v → v ∉ X.S0 i ∧ normV v % X.l i = 1) →
    (∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ v, Over P v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

theorem mod_l_eq_one {M n : ℕ} (hM : 1 ≤ M) (hn : n % (2 * X.l i ^ M) = 1) : n % X.l i = 1 := by
  have hd : X.l i ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  rw [← Nat.mod_mod_of_dvd _ hd, hn, Nat.mod_eq_of_lt (Fact.out : (X.l i).Prime).one_lt]

def Recip : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q →
    ∀ γ γ' : Fin R → GE N, (∀ a, γ a ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))) ∧
      d (.inr a) (γ a) = Multiplicative.ofAdd 1 ∧ IsCj X (γ a) (γ' a)) →
    ∃ c : Fin R → Kˣ, ∀ (x : Z1 (red i K (Tgl i s))) (y : Z1 (red i K ρ)),
      cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
      ∑ a, (c a : K) * form x y (γ a) (φ a) (γ' a) (φ' a) = 0


variable (X) in
def StepAB : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z →
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal → ∀ (A : Finset (PlE D.host)) (R : ℕ) (h : Fin R → GE N),
    (∀ a, h a ∈ H ∧ ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → h a ζ = ζ) →
    ∃ P : Fin R ⊕ Fin R → PlE D.host, SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M U z P (fun q => d (P q)) ∧
      (∀ q v, Over (P q) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧
      ∀ a, ∃ σ g : GE N, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ ∧ g * σ * g⁻¹ * (h a)⁻¹ ∈ U

def Corank {R : ℕ} (φ φ' : Fin R → GE N) (e : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∃ c : Fin R → K,
    ∀ x : Fin (e + 1) → Z1 (red i K (Tgl i s)), (∀ a, cl (x a) ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) →
      (∀ a (y : Z1 (red i K ρ)), cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
        ∑ b, c b * form (x a) y (φ b) (φ b) (φ' b) (φ' b) = 0) → ¬ LinearIndependent K (fun a => cl (x a))

def ResBound : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 4 * D.R.r * R + 2 < X.l i ^ M →
    Position i s M P d φ φ' → IsQ P Q →
    ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))), Computes bkP i s M d Q Φ →
      (Corank bkP i s φ φ' 0 → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m)) ∧
      (Corank bkP i s φ φ' 1 → a = 0 ∨ ∃ b c, ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.adjugate b c →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m))

def ChooseH : Prop :=
  ∀ T : Set (X.Sig i), (∀ s ∈ T, GalHyp bkP i s) → ∃ R : ℕ, ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L : Subgroup (GE N), IsOpen (L : Set (GE N)) → L.Normal → (∀ s ∈ T, Small i s L z) →
    ∃ (h : Fin R → GE N) (U : Subgroup (GE N)), (∀ a, h a ∈ L) ∧ IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧
      ∀ φ φ' : Fin R → GE N, (∀ a, IsCj X (φ a) (φ' a) ∧ ∃ g, g * φ a * g⁻¹ * (h a)⁻¹ ∈ U) →
        ∀ s ∈ T, Corank bkP i s φ φ' (if nu X i = 0 then 0 else 1)

theorem IsCj.unique {g g' g'' : GE N} (h : IsCj X g g') (h' : IsCj X g g'') : g' = g'' :=
  AlgEquiv.ext fun x => (h x).trans (h' x).symm

def dualRep : GE N →* GL (Fin D.R.r) (X.O0 i) :=
  MonoidHom.toHomUnits
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]
        simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul]
        rw [smul_mul_smul_comm] }

theorem isDual_dualRep : IsDual i s (dualRep i s) := fun _ => rfl

end GlobalTheory.ResSel
end
end
