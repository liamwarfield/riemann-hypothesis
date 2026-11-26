module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPtMemMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerTriangularTwoBlockMulWeylTwoBlockEqTransvec
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FrameEval

namespace GlobalTheory.NonDomVanish

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frBor_univ {p A : TRing c.F} {j : Sp p.R ⟶ Xo.XF c} {y₀ : FrPt Xo c p.R} {π : p.R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S]
    {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    {a a' : A.R →ₐ[c.F] S} (ha : FrMap a u y) (ha' : FrMap a' u y') (h : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  obtain ⟨B, uB, uB', tB, q, q', hq, hq', hB, hU⟩ :=
    FrameEval.univFrame_borelPairs GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c p A j y₀ π X s u hj hu
  obtain ⟨b, e1, e2, e3⟩ := hU S a a' y y' t ha ha' h
  have k : FrMap b uB y := GlobalTheory.FlagTan.frMap_of_comp hq ha fun x => DFunLike.congr_fun e1 x
  have k' : FrMap b uB' y' := GlobalTheory.FlagTan.frMap_of_comp hq' ha' fun x => DFunLike.congr_fun e2 x
  have ht : t = fun i => Units.map (b : B.R →* S) (tB i) := funext fun i => Units.ext (e3 i).symm
  rw [GlobalTheory.FlagTan.evR_eq hf.1 k, GlobalTheory.FlagTan.evR_eq hf.1 k', hf.2 B tB uB uB' hB, map_mul, ht]
  congr 1
  simp only [← map_zpow, ← map_prod]
  rfl

section Mat

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S]

def trv (a b : n) (x : S) : Matrix n n S := 1 + single a b x

def lowerTriangularTwoBlockMatrix (a b : n) (s y : S) : Matrix n n S := 1 + single a a (s - 1) + single b a 1 + single b b (y - 1)

def weylTwoBlockMatrix (a b : n) (y : S) : Matrix n n S := 1 + single a a (y - 1) + single a b 1 - single b a 1 - single b b 1

def weylTwoBlockMatrixInv (a b : n) (y : S) : Matrix n n S := 1 - single a a 1 - single a b 1 + single b a 1 + single b b (y - 1)

theorem lowerTriangularTwoBlock_mul_weylTwoBlock_eq_transvection (a b : n) (hab : a ≠ b) (s y : S) (hsy : s * y = 1) :
    lowerTriangularTwoBlockMatrix a b s y * weylTwoBlockMatrix a b y = trv a b s := by
  have h1 : ∀ (c d : S) (i l : n), single i a c * single b l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i a b hab d
  have h2 : ∀ (c d : S) (i l : n), single i b c * single a l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i b a hab.symm d
  simp only [lowerTriangularTwoBlockMatrix, weylTwoBlockMatrix, trv, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    single_mul_single_same, h1, h2, zero_add, add_zero]
  ext r c
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hr : a = r <;> by_cases hc : a = c <;> by_cases hr' : b = r <;> by_cases hc' : b = c <;>
    simp_all <;> first | linear_combination hsy | linear_combination -hsy | ring

theorem weylTwoBlockMatrix_mul_weylTwoBlockMatrixInv (a b : n) (hab : a ≠ b) (y : S) : weylTwoBlockMatrix a b y * weylTwoBlockMatrixInv a b y = 1 := by
  have h1 : ∀ (c d : S) (i l : n), single i a c * single b l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i a b hab d
  have h2 : ∀ (c d : S) (i l : n), single i b c * single a l d = 0 := fun c d i l =>
    single_mul_single_of_ne c i b a hab.symm d
  simp only [weylTwoBlockMatrixInv, weylTwoBlockMatrix, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    single_mul_single_same, h1, h2, zero_add, add_zero]
  ext r c
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.zero_apply]
  by_cases hr : a = r <;> by_cases hc : a = c <;> by_cases hr' : b = r <;> by_cases hc' : b = c <;>
    simp_all <;> ring

theorem isUnit_det_trv (a b : n) (hab : a ≠ b) (x : S) : IsUnit (trv a b x).det := by
  have : trv a b x = transvection a b x := rfl
  rw [this, det_transvection_of_ne a b hab]
  exact isUnit_one

theorem isUnit_det_weylTwoBlockMatrix (a b : n) (hab : a ≠ b) (y : S) : IsUnit (weylTwoBlockMatrix a b y).det :=
  Matrix.isUnit_det_of_right_inverse (weylTwoBlockMatrix_mul_weylTwoBlockMatrixInv a b hab y)

variable {S' : Type} [CommRing S'] (g : S →+* S')

theorem trv_map (a b : n) (x : S) : (trv a b x).map g = trv a b (g x) := by
  ext r c; simp [trv, Matrix.single_apply, Matrix.one_apply, apply_ite g]

theorem weylTwoBlockMatrix_map_ringHom (a b : n) (y : S) : (weylTwoBlockMatrix a b y).map g = weylTwoBlockMatrix a b (g y) := by
  ext r c; simp [weylTwoBlockMatrix, Matrix.single_apply, Matrix.one_apply, apply_ite g]

theorem trv_zero (a b : n) : trv a b (0 : S) = 1 := by simp [trv]

theorem lowerTriangularTwoBlockMatrix_diag_apply {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] (a b : n) (hab : a ≠ b)
    (s y : S) (i : n) : lowerTriangularTwoBlockMatrix a b s y i i = if i = a then s else if i = b then y else 1 := by
  simp only [lowerTriangularTwoBlockMatrix, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hia : i = a
  · subst hia; simp [hab, Ne.symm hab]
  · by_cases hib : i = b
    · subst hib; simp [hia, hab, Ne.symm hab]
    · simp [hia, hib, Ne.symm hia, Ne.symm hib]

theorem lowerTriangularTwoBlockMatrix_apply_of_ne {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] (a b : n)
    (s y : S) (i j : n) (hij : i ≠ j) (h : ¬ (i = b ∧ j = a)) : lowerTriangularTwoBlockMatrix a b s y i j = 0 := by
  simp only [lowerTriangularTwoBlockMatrix, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases h1 : a = i <;> by_cases h2 : a = j <;> by_cases h3 : b = i <;> by_cases h4 : b = j <;> simp_all

end Mat

section Fam

variable {J : Type} [DecidableEq J] {m : J → ℕ} {S : Type} [CommRing S]

def famU (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S :=
  Function.update (fun _ => 1) τ₀ M

theorem famU_self (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) : famU τ₀ M τ₀ = M := by
  simp [famU]

theorem famU_of_ne {τ₀ τ : J} (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) (h : τ ≠ τ₀) : famU τ₀ M τ = 1 := by
  simp [famU, Function.update_of_ne h]

theorem famU_map {S' : Type} [CommRing S'] (g : S →+* S') (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) (τ : J) :
    (famU τ₀ M τ).map g = famU τ₀ (M.map g) τ := by
  by_cases h : τ = τ₀
  · subst h; simp [famU_self]
  · simp [famU_of_ne _ h, Matrix.map_one]

theorem isUnit_det_famU (τ₀ : J) (M : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) (hM : IsUnit M.det) (τ : J) :
    IsUnit (famU τ₀ M τ).det := by
  by_cases h : τ = τ₀
  · subst h; simpa [famU_self] using hM
  · simp [famU_of_ne _ h]

end Fam

theorem map_mul_alg {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    {k : Type} [Fintype k] [DecidableEq k] (φ : S →ₐ[R] S') (M N : Matrix k k S) :
    (M * N).map φ = M.map φ * N.map φ := Matrix.map_mul (f := φ.toRingHom)

theorem famU_one {J : Type} [DecidableEq J] {m : J → ℕ} {S : Type} [CommRing S] (τ₀ τ : J) :
    famU (m := m) τ₀ (1 : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) τ = 1 := by
  by_cases h : τ = τ₀
  · subst h; simp [famU_self]
  · simp [famU_of_ne _ h]

theorem famU_mul {J : Type} [DecidableEq J] {m : J → ℕ} {S : Type} [CommRing S] (τ₀ τ : J)
    (M N : Matrix (Fin (m τ₀)) (Fin (m τ₀)) S) : famU τ₀ M τ * famU τ₀ N τ = famU τ₀ (M * N) τ := by
  by_cases h : τ = τ₀
  · subst h; simp [famU_self]
  · simp [famU_of_ne _ h]

theorem poly_eq_zero_of_toLaurent_eq {R : Type} [CommRing R] (φ ψ : Polynomial R) (m : ℤ) (hm : m < 0)
    (h : Polynomial.toLaurent φ = LaurentPolynomial.T m * LaurentPolynomial.invert (Polynomial.toLaurent ψ)) :
    φ = 0 := by
  have key : ∀ ψ : Polynomial R,
      LaurentPolynomial.trunc (LaurentPolynomial.T m * LaurentPolynomial.invert (Polynomial.toLaurent ψ)) = 0 := by
    intro ψ
    induction ψ using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), mul_add, map_add (f := _), hp, hq, add_zero]
    | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
        map_mul (LaurentPolynomial.invert (R := R)), LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        mul_left_comm, ← LaurentPolynomial.T_add, LaurentPolynomial.trunc_C_mul_T, if_neg (by omega)]
  rw [← Polynomial.trunc_toLaurent φ, h, key]

theorem eq_zero_of_field {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e)
    (hfield : ∀ (L : Type) [Field L] [Algebra c.F L] (w : FrPt Xo c L), evR Xo c g w = 0) : g = 0 := by
  funext p y
  have hred : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  show g p y = 0
  refine IsNilpotent.eq_zero ?_
  rw [nilpotent_iff_mem_prime]
  intro P hP
  let φ : p.R →ₐ[c.F] P.ResidueField := IsScalarTower.toAlgHom c.F p.R P.ResidueField
  obtain ⟨w, hw⟩ := GlobalTheory.FlagTan.exists_frMap φ y
  have h4 := hfield _ w
  rw [GlobalTheory.FlagTan.evR_eq hg.1 hw] at h4
  exact Ideal.algebraMap_residueField_eq_zero.1 h4


open Classical in
theorem eq_zero_of_lt {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (τ₀ : E →+* ℂ)
    (a b : Fin (Dw.mult τ₀)) (hab : (b : ℕ) = a + 1) (hlt : e (some ⟨τ₀, a⟩) < e (some ⟨τ₀, b⟩)) : f = 0 := by
  have hne : a ≠ b := by intro h; rw [h] at hab; omega
  apply eq_zero_of_field hf
  intro L _ _ w
  obtain ⟨p, A, j, y₀, π, X, s, u, α, -, hj, hu, hα, -⟩ := GlobalTheory.FlagTan.exists_chart w w rfl
  obtain ⟨⟨hX, huniv⟩, u₀, hu₀, hchg⟩ := hu
  have calc4 := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c
  let ι : L →ₐ[c.F] Polynomial L := IsScalarTower.toAlgHom c.F L (Polynomial L)
  let M1 : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (Polynomial L) :=
    fun τ => (X τ).map (ι.comp α)
  have hM1 : ∀ τ, IsUnit (M1 τ).det := fun τ => by
    have := (hX τ).map (ι.comp α).toRingHom
    rwa [RingHom.map_det] at this
  let s1 : (Polynomial L)ˣ := Units.map ((ι.comp α) : A.R →* Polynomial L) s
  obtain ⟨α1, hα1, -⟩ := huniv (Polynomial L) (ι.comp (α.comp π))
    (fun τ => famU τ₀ (trv a b Polynomial.X) τ * M1 τ) s1
    (fun τ => by rw [Matrix.det_mul]; exact (isUnit_det_famU _ _ (isUnit_det_trv a b hne _) τ).mul (hM1 τ))
  obtain ⟨α2, hα2, -⟩ := huniv (Polynomial L) (ι.comp (α.comp π))
    (fun τ => famU τ₀ (weylTwoBlockMatrix a b Polynomial.X) τ * M1 τ) s1
    (fun τ => by rw [Matrix.det_mul]; exact (isUnit_det_famU _ _ (isUnit_det_weylTwoBlockMatrix a b hne _) τ).mul (hM1 τ))
  let ev0 : Polynomial L →ₐ[c.F] L := (Polynomial.aeval (0 : L)).restrictScalars c.F
  have hev0ι : ∀ q, ev0 (ι q) = q := fun q => by simp [ev0, ι]
  have hev0X : ev0 Polynomial.X = 0 := by simp [ev0]
  have hev : ev0.comp α1 = α := by
    obtain ⟨k, -, huq⟩ := huniv L (α.comp π) (fun τ => (X τ).map α) (Units.map (α : A.R →* L) s)
      (fun τ => by have := (hX τ).map α.toRingHom; rwa [RingHom.map_det] at this)
    have e1 := huq α ⟨rfl, fun τ => rfl, rfl⟩
    have e2 := huq (ev0.comp α1) ⟨?_, ?_, ?_⟩
    · exact e2.trans e1.symm
    · ext x
      have := congrArg (fun g => g x) hα1.1
      simp only [AlgHom.comp_apply] at this ⊢
      rw [this, hev0ι]
    · intro τ
      rw [show (ev0.comp α1 : A.R → L) = ev0 ∘ α1 from rfl, ← Matrix.map_map, hα1.2.1 τ, map_mul_alg,
        show (X τ).map α = ((X τ).map (ι.comp α)).map ev0 by rw [Matrix.map_map]; congr 1; funext x; simp [hev0ι]]
      rw [show (famU τ₀ (trv a b Polynomial.X) τ).map ev0 = 1 by
        rw [show (ev0 : Polynomial L → L) = (ev0.toRingHom : Polynomial L → L) from rfl, famU_map, trv_map]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hev0X, trv_zero, famU_one]]
      rw [one_mul]
    · show ev0 (α1 s) = α s
      rw [hα1.2.2]
      exact hev0ι _
  let tl : Polynomial L →ₐ[c.F] LaurentPolynomial L := (Polynomial.toLaurentAlg (R := L)).restrictScalars c.F
  let inv : LaurentPolynomial L →ₐ[c.F] LaurentPolynomial L :=
    ((LaurentPolynomial.invert (R := L)).toAlgHom).restrictScalars c.F
  have htl : ∀ q, tl q = Polynomial.toLaurent q := fun q => rfl
  have hinv : ∀ q, inv q = LaurentPolynomial.invert q := fun q => rfl
  have hinvι : ∀ q, inv (tl (ι q)) = tl (ι q) := fun q => by
    simp [htl, hinv, ι, Polynomial.toLaurent_C, LaurentPolynomial.invert_C]
  let β1 := tl.comp α1
  let β2 := inv.comp (tl.comp α2)
  have hβπ : ∀ x, β2 (π x) = β1 (π x) := fun x => by
    have e1 := congrArg (fun g => g x) hα1.1
    have e2 := congrArg (fun g => g x) hα2.1
    simp only [AlgHom.comp_apply] at e1 e2
    simp only [β1, β2, AlgHom.comp_apply, e1, e2, hinvι]
  have hβs : β2 s = β1 s := by
    simp only [β1, β2, AlgHom.comp_apply, hα1.2.2, hα2.2.2]
    exact hinvι _
  obtain ⟨z1, hz1⟩ := GlobalTheory.FlagTan.exists_frMap β1 u
  obtain ⟨z2, hz2⟩ := GlobalTheory.FlagTan.exists_frMap β2 u
  obtain ⟨w0, hw0⟩ := GlobalTheory.FlagTan.exists_frMap (β1.comp π) y₀
  have hw1 : FrMap β1 u₀ w0 := GlobalTheory.FlagTan.frMap_of_comp hu₀ hw0 (fun _ => rfl)
  have hw2 : FrMap β2 u₀ w0 := GlobalTheory.FlagTan.frMap_of_comp hu₀ hw0 (fun x => hβπ x)
  have c1 := ((calc4 A.R).2.2.1 _ β1 X s u₀ u w0 z1 hchg hw1).1 hz1
  have c2 := ((calc4 A.R).2.2.1 _ β2 X s u₀ u w0 z2 hchg hw2).1 hz2
  let Tu : (LaurentPolynomial L)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let Bf : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentPolynomial L) :=
    fun τ => famU τ₀ (lowerTriangularTwoBlockMatrix a b (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))) τ
  have hN : ∀ τ, (((X τ).map (ι.comp α)).map tl).map inv = ((X τ).map (ι.comp α)).map tl := fun τ => by
    simp only [Matrix.map_map]
    congr 1
    funext x
    exact hinvι _
  have hmat : ∀ τ, Bf τ * (X τ).map β2 = (X τ).map β1 := fun τ => by
    have e1 : (X τ).map β1 = ((X τ).map α1).map tl := by rw [Matrix.map_map]; rfl
    have e2 : (X τ).map β2 = (((X τ).map α2).map tl).map inv := by rw [Matrix.map_map, Matrix.map_map]; rfl
    rw [e1, e2, hα1.2.1 τ, hα2.2.1 τ, map_mul_alg, map_mul_alg, map_mul_alg, hN]
    rw [show ((famU τ₀ (weylTwoBlockMatrix a b Polynomial.X) τ).map tl).map inv =
        famU τ₀ (weylTwoBlockMatrix a b (LaurentPolynomial.T (-1))) τ by
      rw [show (tl : Polynomial L → LaurentPolynomial L) = (tl.toRingHom : Polynomial L → LaurentPolynomial L) from rfl,
        show (inv : LaurentPolynomial L → LaurentPolynomial L) =
          (inv.toRingHom : LaurentPolynomial L → LaurentPolynomial L) from rfl, famU_map, famU_map, weylTwoBlockMatrix_map_ringHom, weylTwoBlockMatrix_map_ringHom]
      simp [htl, hinv, Polynomial.toLaurent_X, LaurentPolynomial.invert_T]]
    rw [show (famU τ₀ (trv a b Polynomial.X) τ).map tl = famU τ₀ (trv a b (LaurentPolynomial.T 1)) τ by
      rw [show (tl : Polynomial L → LaurentPolynomial L) = (tl.toRingHom : Polynomial L → LaurentPolynomial L) from rfl,
        famU_map, trv_map]
      simp [htl, Polynomial.toLaurent_X]]
    rw [← mul_assoc, famU_mul, lowerTriangularTwoBlock_mul_weylTwoBlock_eq_transvection a b hne _ _ (by rw [← LaurentPolynomial.T_add]; simp)]
  have c3 : FrChg Bf 1 z2 z1 := by
    refine ((calc4 (LaurentPolynomial L)).1 _ Bf _ 1 w0 z2 z1 c2).2 ?_
    rw [one_mul, hβs]
    convert c1 using 1
    funext τ
    exact hmat τ
  let t : Ix Dw → (LaurentPolynomial L)ˣ := fun k => Option.elim k 1
    (fun q => if q = ⟨τ₀, a⟩ then Tu else if q = ⟨τ₀, b⟩ then Tu⁻¹ else 1)
  have hba : ¬ (b < a) := by intro h; have := Fin.lt_def.1 h; omega
  have hdiag : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), Bf τ i i = (t (some ⟨τ, i⟩) : LaurentPolynomial L) := by
    intro τ i
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [Bf, famU_self, t, Option.elim, lowerTriangularTwoBlockMatrix_diag_apply a b hne]
      by_cases hia : i = a
      · subst hia; simp [Tu]
      · by_cases hib : i = b
        · subst hib; simp [hne, Ne.symm hne, Tu]
        · simp [hia, hib]
    · simp [Bf, famU_of_ne _ hτ, t, hτ]
  have hlow : ∀ (τ : E →+* ℂ) (i j : Fin (Dw.mult τ)), i < j → Bf τ i j = 0 := by
    intro τ i j hij
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [Bf, famU_self]
      refine lowerTriangularTwoBlockMatrix_apply_of_ne a b (LaurentPolynomial.T 1 : LaurentPolynomial L) (LaurentPolynomial.T (-1)) i j (ne_of_lt hij) ?_
      rintro ⟨rfl, rfl⟩
      exact hba hij
    · simp [Bf, famU_of_ne _ hτ, Matrix.one_apply, ne_of_lt hij]
  have hbor : FrBor t z2 z1 := ((calc4 (LaurentPolynomial L)).2.2.2 t z2 z1).2 ⟨Bf, hdiag, hlow, by simpa [t] using c3⟩
  have hw := evR_frBor_univ hj ⟨⟨hX, huniv⟩, u₀, hu₀, hchg⟩ hf hz2 hz1 hbor
  rw [GlobalTheory.FlagTan.evR_eq hf.1 hz1, GlobalTheory.FlagTan.evR_eq hf.1 hz2] at hw
  have hTu : ∀ n : ℤ, ((Tu ^ n : (LaurentPolynomial L)ˣ) : LaurentPolynomial L) = LaurentPolynomial.T n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [LaurentPolynomial.T_zero]
    | succ k ih => rw [zpow_add_one, Units.val_mul, ih, LaurentPolynomial.T_add]
    | pred k ih => rw [zpow_sub_one, Units.val_mul, ih, sub_eq_add_neg, LaurentPolynomial.T_add]; rfl
  have hsa : (some ⟨τ₀, a⟩ : Ix Dw) ≠ some ⟨τ₀, b⟩ := by
    intro h; simp only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact hne h
  have hprod : ((∏ i, t i ^ e i : (LaurentPolynomial L)ˣ) : LaurentPolynomial L) =
      LaurentPolynomial.T (e (some ⟨τ₀, a⟩) - e (some ⟨τ₀, b⟩)) := by
    rw [Finset.prod_eq_mul (some ⟨τ₀, a⟩) (some ⟨τ₀, b⟩) hsa ?_ (by simp) (by simp)]
    · have hb' : (⟨τ₀, b⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≠ ⟨τ₀, a⟩ := by
        intro h; simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h; exact hne h.symm
      simp only [t, Option.elim, if_true, hb', if_false, inv_zpow', Units.val_mul, hTu]
      rw [← LaurentPolynomial.T_add]; ring_nf
    · intro k _ hk
      rcases k with _ | q
      · simp [t]
      · have h1 : q ≠ ⟨τ₀, a⟩ := fun h => hk.1 (by rw [h])
        have h2 : q ≠ ⟨τ₀, b⟩ := fun h => hk.2 (by rw [h])
        simp [t, h1, h2]
  rw [hprod] at hw
  have h0 : α1 (f A u) = 0 := poly_eq_zero_of_toLaurent_eq (α1 (f A u)) (α2 (f A u)) _ (by omega) hw
  rw [GlobalTheory.FlagTan.evR_eq hf.1 hα, ← hev, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory.NonDomVanish
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.VanishingBound

theorem keySec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hY.geo

theorem isSec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (la : AllWt.Weight (T.Q.Dw j)) (f : Rul Y.d.Xo₂ Y.d.c₂)
    (hf : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) :
    ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k) := by
  have hU := hY.unf σ hσ
  by_cases hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) la 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) la 0).1 (τ, i)
  · by_cases hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q
    · exact GlobalTheory.T.isSec_reading_decreasing_integer_exponents _ _ _ _ _ _ σ _ (Y.U σ) (keySec D T j Y e o hY σ hσ) hσ hU hpq _
        (AllWt.even_wtOf la 0) hdec f hf k
    · have hp : (T.Q.Dw j).p = 0 := by omega
      have hq : (T.Q.Dw j).q = 0 := by omega
      have hG : wtOf (T.Q.Dw j) la 0 = wtZ (fun _ => 0) 0 := by
        refine Prod.ext (funext fun x => ?_) ?_
        · simp only [wtOf, wtZ, hp, hq]
          split_ifs <;> first | (exfalso; omega) | simp
        · simp [wtOf, wtZ]
      rw [hG, AllWt.modelWt_wtZ]
      have hf' : f ∈ sec Y.d.Xo₂ Y.d.c₂ (fun _ => 0) 0 := by
        rw [← AllWt.secZ_nat, ← AllWt.exZ_wtZ, ← hG]
        exact hf
      exact hU.2.2.2.2.1 _ _ ⟨fun τ => fun a b _ => le_refl _, ⟨0, rfl⟩⟩ f hf' k
  · have hex : ∃ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ),
        (wtOf (T.Q.Dw j) la 0).1 (τ, m) < (wtOf (T.Q.Dw j) la 0).1 (τ, m + 1) := by
      by_contra hne
      push_neg at hne
      apply hdec
      intro τ i j' hij hj'
      revert hj'
      induction j', hij using Nat.le_induction with
      | base => intro _; exact le_refl _
      | succ n hn ih => intro hj'; exact (hne τ n hj').trans (ih (by omega))
    obtain ⟨τ, m, hm, hlt⟩ := hex
    have h0 : f = 0 := GlobalTheory.NonDomVanish.eq_zero_of_lt hf τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt
    subst h0
    rw [map_zero]
    exact ⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩


open scoped LaurentSeries in
theorem fjZero (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (la : AllWt.Weight (T.Q.Dw j)) (s) (hs : s ∈ vanBd TF.X Z la)
    (f : GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (hfs : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.suppOn Z) (hfsec : sec₀ TF.X Z _ f = H0.restr le_top s)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k)
    (hsec : ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k))
    (ξ) (hξ : ((Y.U σ).X k).IsIso ξ) (x) (hx : x ∈ ((Y.U σ).X k).dom) :
    ((Y.U σ).X k).fj (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) ξ 0 (rdU (Y.U σ) f k) x = 0 := by
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hU := hG.unf σ hσ
  letI : Algebra Y.d.c₂.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  have halg : ∀ x : Y.d.c₂.F, algebraMap Y.d.c₂.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)) :=
    fun _ => rfl
  obtain ⟨y, T₀, s', d, hbd, hd, hw⟩ :=
    GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) halg hσ hU k ξ hξ x hx _ _ TF.Y
  have hc : (algebraMap (PowerSeries ℂ) ℂ⸨X⸩).comp ((PowerSeries.C (R := ℂ)).comp σ) = algebraMap Y.d.c₂.F ℂ⸨X⸩ :=
    RingHom.ext fun t => (halg t).symm
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 none = 0 := rfl
  have hcoef : ∀ m ≤ (0:ℤ), (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff m = 0 := by
    intro m hm
    by_cases hZ : GlobalTheory.AllWt.LiesOn Z y
    · obtain ⟨v, hv, hval⟩ :=
        GlobalTheory.CuspOnTor.evR_mem_maximalIdeal _ _ _ _ _ _ TF.Y TF.X Z la s hs f hfsec (PowerSeries ℂ) ℂ⸨X⸩ _ y hc hZ hbd
      rw [hval]; exact GlobalTheory.CuspFrom.coeff_eq_zero hv hm
    · rw [hfs ℂ⸨X⸩ y ((GlobalTheory.AllWt.liesOff_iff Z y).2 hZ)]; rfl
  exact GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line _ _ _ _ _ ξ x s' d T₀ (fun j => (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff j) hsec
    (GlobalTheory.CuspFrom.freqNonneg _ hf1 hsec) hξ hx hd hcoef fun w hw' => ⟨(hw w hw').1, (hw w hw').2 _ hex _ f.2⟩

end GlobalTheory.HSApp.VanishingBound

namespace GlobalTheory.HSApp


open GlobalTheory.HSApp.VanishingBound in
theorem vanBd_le_space : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), vanBd TF.X Z la ≤ space TF.X Z Y.U la := by
  intro D T j Y e o hG hf Z TF la s hs
  obtain ⟨f, hfZ, hfs⟩ := GlobalTheory.T.exists_supportedRule_of_flagComponentSection _ _ _ _ _ _ _ TF.X Z (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) (H0.restr le_top s)
  have hsec := isSec D T j Y e o hG la f.1 f.2
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hcusp : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0) := by
    refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨f.2, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
    have h0 := fjZero D T j Y e o hG hf Z TF la s hs f hfZ hfs σ hσ k (hsec σ hσ k)
    have h3 := (GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ (hsec σ hσ k) (GlobalTheory.CuspFrom.isModerate _ hf1 (hsec σ hσ k)) h0).1.2
    exact ⟨⟨hsec σ hσ k, h3⟩, fun ξ hξ x hx => h0 ξ hξ x hx⟩
  exact ⟨⟨f.1, hcusp⟩, hfs⟩

end GlobalTheory.HSApp
