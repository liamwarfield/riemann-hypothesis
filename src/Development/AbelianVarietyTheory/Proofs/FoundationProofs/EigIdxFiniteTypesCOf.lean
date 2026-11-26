module

public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigIdxFiniteTypesCOf
open Formalism.BasicNotions NumberField

namespace GlobalTheory

def eigIdxFiniteTypes (D : D7) (X : DivX D) : EigIdx D X where
  Pi := D.what₂.FT
  fin := D.what₂.instFT
  dec := D.what₂.instFTd
  cOf := id
  lam_const := by
    intro j _ π π' e _ _ h
    have h' : π = π' := h
    rw [h']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

def trivialIntersectionTheory (d : ℕ) : DV.ITh where
  LB := Unit
  Ch := ℚ
  c1 := fun _ => 0
  VDiv := ℚ
  cD := 0
  capDeg := 0
  divP := 1
  cD_divP := rfl
  dim := d

def trivialFlagPair (d r : ℕ) : DV.FPair (trivialIntersectionTheory d) r where
  x := fun _ => ()
  x' := fun _ => ()
  Dv := fun _ => 0
  hx := fun _ => by
    rw [map_zero, sub_zero]

theorem sub_rkOf_psiOf_eq_rkOf_cEmb (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) (τ : DV.Emb D p) :
    N - DV.rkOf (DV.PsiOf D jc) N j τ = DV.rkOf (DV.PsiOf D jc) N j (DV.cEmb D τ) := by
  have h := Formalism.L2.Geo.cm_type_meets_conjugate_pair p jc τ
  unfold DV.rkOf
  by_cases hτ : τ ∈ DV.PsiOf D jc
  · rw [if_pos hτ, if_neg (h.1 hτ)]
  · have hc : DV.cEmb D τ ∈ DV.PsiOf D jc := by
      by_contra hn
      exact hτ (h.2 hn)
    rw [if_neg hτ, if_pos hc]
    omega

def trivialAdmissibleModel (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := trivialIntersectionTheory (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
  cov := 1
  cov_pos := Nat.one_pos
  lvl := 0
  lie := fun _ => trivialFlagPair _ _
  om := fun _ => trivialFlagPair _ _
  lieW := trivialFlagPair _ _
  omW := trivialFlagPair _ _
  om_dual := fun τ =>
    ⟨finCongr (sub_rkOf_psiOf_eq_rkOf_cEmb D p jc N j hj τ), fun _ => neg_zero.symm⟩
  dim_eq := rfl
  omW_dual := ⟨Equiv.refl _, fun _ => neg_zero.symm⟩

theorem nonempty_admissibleModel :
    ∀ (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (N j : ℕ), j ≤ N →
      Nonempty (DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j)) :=
  fun D p _ jc N j hj => ⟨trivialAdmissibleModel D p jc N j hj⟩

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyRingHomComplexOfLeContinuum
set_option autoImplicit false

open Formalism.BasicNotions NumberField

namespace GlobalTheory.WittFracComplex


open Cardinal in
theorem nonempty_ringHom_complex_of_le_continuum (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem charZero_wittVector (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] :
    CharZero (WittVector p k) := by
  obtain ⟨q, hq⟩ := CharP.exists (WittVector p k)
  have h1 : ((q : ℕ) : k) = 0 := by
    have := congrArg (WittVector.constantCoeff : WittVector p k →+* k) (CharP.cast_eq_zero (WittVector p k) q)
    rwa [map_natCast, map_zero] at this
  have h2 : p ∣ q := (CharP.cast_eq_zero_iff k p q).1 h1
  rcases CharP.char_is_prime_or_zero (WittVector p k) q with h | h
  · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    subst h3
    exact absurd (CharP.cast_eq_zero (WittVector p k) p) (WittVector.p_nonzero p k)
  · subst h
    exact CharP.charP_to_charZero _


open Cardinal in
theorem mk_wittVector_le (p : ℕ) (k : Type) (hk : #k ≤ ℵ₀) : #(WittVector p k) ≤ 𝔠 := by
  have h : Function.Injective (WittVector.coeff : WittVector p k → ℕ → k) :=
    fun x y h => WittVector.ext (fun n => congrFun h n)
  refine (Cardinal.mk_le_of_injective h).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat, ← Cardinal.aleph0_power_aleph0]
  exact Cardinal.power_le_power_right hk


open Cardinal in
theorem nonempty_ringHom_complex : ∀ (p : ℕ) [Fact p.Prime], Nonempty (DV.KW p →+* ℂ) := by
  intro p _
  have hk : #(AlgebraicClosure (ZMod p)) ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max (ZMod p) (AlgebraicClosure (ZMod p))
    rwa [max_eq_right (Cardinal.lt_aleph0_of_finite _).le] at this
  have := charZero_wittVector p (AlgebraicClosure (ZMod p))
  have : CharZero (DV.KW p) :=
    (RingHom.charZero_iff (IsFractionRing.injective (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p))).1 this
  refine nonempty_ringHom_complex_of_le_continuum _ ?_
  rw [Cardinal.mk_fractionRing]
  exact mk_wittVector_le p _ hk

end GlobalTheory.WittFracComplex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFramesNormAtEqNorm
open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem exists_frames_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (c : Module.Basis (Fin n) ℂ W) (L : Submodule (𝓞 K) (Fin n → K)), ∃ X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ v, IsUnit (X v).det) ∧ ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X (InfinitePlace.mk e) x = ‖∑ i, e (x i) • c i‖ := by
  intro K _ _ _ e W _ _ n c _
  have : FiniteDimensional ℂ W := Module.Finite.of_basis c
  have hn : Module.finrank ℂ W = n := by simpa using Module.finrank_eq_card_basis c
  let o : OrthonormalBasis (Fin n) ℂ W := (stdOrthonormalBasis ℂ W).reindex (finCongr hn)
  set A : Matrix (Fin n) (Fin n) ℂ := o.toBasis.toMatrix c with hA
  have hAu : IsUnit A.det :=
    Matrix.isUnit_det_of_right_inverse (o.toBasis.toMatrix_mul_toMatrix_flip c)
  have key : ∀ y : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm (A.mulVec y) = ‖∑ i, y i • c i‖ := by
    intro y
    rw [← o.repr.norm_map, EuclideanSpace.norm_eq]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    simp [hA, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
  rcases InfinitePlace.embedding_mk_eq e with h | h
  · refine ⟨fun _ => A⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det A hAu, fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv A hAu]
    congr 2
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, h]
  · have hBu : IsUnit (A.map (starRingEnd ℂ)).det := by
      have := hAu.map (starRingEnd ℂ)
      rwa [RingHom.map_det] at this
    refine ⟨fun _ => (A.map (starRingEnd ℂ))⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det _ hBu,
      fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv _ hBu]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← RCLike.norm_conj (A.mulVec (fun i => e (x i)) j)]
    congr 1
    simp [Formalism.HermitianLatticesTheory.vecAt, h, Matrix.mulVec, dotProduct]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory

def provisionalShimX (Tau : Type) [Fintype Tau] (N j : ℕ) (lev : Finset ℕ) (hj : 1 ≤ j)
    (hjN : j < N) (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX Tau where
  N := N
  j := j
  j_pos := hj
  j_lt := hjN
  lev := lev
  lev_prime := hlev
  Comp := Unit
  vol := 0
  chern := 0
  chern_homog := fun _ _ _ _ => rfl
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl
  CurveHT := fun _ => Empty
  degHT := fun _ _ _ => 0
  CurveDR := fun _ => Empty
  degDR := fun _ _ _ => 0
  FibComp := fun _ => Empty
  fibInBd := fun _ _ => False
  Pt := Unit
  phiDR := fun _ _ _ => 0
  phiMod := fun _ _ _ => 0
  phiFr := fun _ _ _ => 0
  XC := Unit
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_rfl
  hLo := fun _ => 1
  hUp := fun _ => 1
  hLo_le := fun _ => ⟨one_pos, le_rfl⟩
  connN := fun _ => 0
  curvN := fun _ => 0
  compOf := fun _ => ()
  normDetInf := fun _ _ => 1
  compPt := fun _ => ()
  normDetT := fun _ _ _ => 1
  normDetH := fun _ _ _ => 1
  htDetT := fun _ _ _ => 0
  ALB := Unit
  arSelf := fun _ => 0
  arSelfC := fun _ _ => 0
  arSelf_sum := fun _ => by simp
  geo := fun _ => 0
  geoC := fun _ _ => 0
  geo_sum := fun _ => by simp
  arVol := fun _ => 0
  semipos := fun _ => True
  nefFib := fun _ => True
  arNef := fun _ => True
  Mbar := fun _ _ _ => ()

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoordMapBasisFun
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.ProvRowSide

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def stdHLat (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) : HLat K where
  V := Fin n → K
  ι := Fin n
  b := Pi.basisFun K (Fin n)
  X := fun _ => 1
  L := L

theorem stdHLat_frames (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) (v : InfinitePlace K) :
    IsUnit ((stdHLat K n L).X v).det := by
  show IsUnit (1 : Matrix (Fin n) (Fin n) ℂ).det
  simp

variable {K}

def coordMap (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W) :
    (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

set_option linter.unusedSectionVars false in
theorem coordMap_basisFun (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ} (c : Fin n → W)
    (i : Fin n) : coordMap e c (Pi.basisFun K (Fin n) i) = c i := by
  simp [coordMap, Pi.single_apply, apply_ite e, ite_smul]

theorem normAt_one (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ}
    (c : OrthonormalBasis (Fin n) ℂ W) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (fun _ => 1) (InfinitePlace.mk e) x = ‖coordMap e c x‖ := by
  have h1 : coordMap e c x = c.repr.symm (WithLp.toLp 2 (fun i => e (x i))) := by
    rw [← c.sum_repr_symm]; rfl
  rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  simp [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]

end Std

section WithRRDef

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

end WithRRDef

section Small

variable (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
  {n : ℕ} (c : OrthonormalBasis (Fin n) ℂ EE)

end Small

end GlobalTheory.ProvRowSide

end
end
