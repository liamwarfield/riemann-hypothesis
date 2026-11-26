module

public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.WeilBound.ThetaLifts.Reductions.SiegelMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.SiegelParMod
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open PositivityTheory.ThKEst PositivityTheory.ThKEst.Sieg

namespace PositivityTheory.ThKR.PMod

open PositivityTheory.ThKR.Sieg (Fr eich scalM msMat)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ring_facts : IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) ∧ LocallyCompactSpace (AF F ⊗[F] E) ∧
    SecondCountableTopology (AF F ⊗[F] E) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact ⟨GlobalTheory.Doubling.isTopologicalRing_tens, e.isEmbedding.t2Space, e.isClosedEmbedding.locallyCompactSpace,
    e.isEmbedding.secondCountableTopology⟩

theorem tr_RE : IsTopologicalRing (AF F ⊗[F] E) := ring_facts.1
theorem t2_space_adele_tensor : T2Space (AF F ⊗[F] E) := ring_facts.2.1
theorem lc_RE : LocallyCompactSpace (AF F ⊗[F] E) := ring_facts.2.2.1
theorem sc_RE : SecondCountableTopology (AF F ⊗[F] E) := ring_facts.2.2.2

attribute [local instance] tr_RE t2_space_adele_tensor lc_RE sc_RE msMat

local instance bsMat (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) := ⟨rfl⟩

def invTwo : Invertible (2 : AF F ⊗[F] E) where
  invOf := algebraMap F _ (1 / 2)
  invOf_mul_self := by
    rw [← map_ofNat (algebraMap F (AF F ⊗[F] E)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]
  mul_invOf_self := by
    rw [← map_ofNat (algebraMap F (AF F ⊗[F] E)) 2, ← map_mul, one_div, mul_inv_cancel₀ two_ne_zero, map_one]

attribute [local instance] invTwo

variable (σ : E →ₐ[F] E)

theorem sigR_inclR (x : E) : sigR (AF F) σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [sigR, inclR]

theorem sigR_algebraMap (x : AF F) : sigR (AF F) σ (algebraMap (AF F) (AF F ⊗[F] E) x) = algebraMap (AF F) _ x := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (x : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem continuous_sigR : Continuous (sigR (AF F) σ) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let L : (AF F ⊗[F] E) →ₗ[AF F] (AF F ⊗[F] E) :=
    { toFun := sigR (AF F) σ
      map_add' := map_add _
      map_smul' := fun c x => by
        rw [Algebra.smul_def, map_mul, sigR_algebraMap, ← Algebra.smul_def]
        rfl }
  exact IsModuleTopology.continuous_of_linearMap L

variable {σ} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

def colK {k : ℕ} (hk : k ≤ r) {R : Type} (M : Matrix (Fin n) (Fin r) R) : Matrix (Fin n) (Fin k) R :=
  M.submatrix id (Fin.castLE hk)

theorem cT_adMat {a b : Type} (M : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F M) = adMat F (cT (σ : E →+* E) M) := by
  ext i j
  simp [cT, adMat, sigR_inclR]

theorem gram_col {k : ℕ} (hk : k ≤ r) {R : Type} [CommRing R] (s : R →+* R) (A B : Matrix (Fin n) (Fin r) R)
    (J' : Matrix (Fin n) (Fin n) R) :
    cT s (colK hk A) * J' * colK hk B = (cT s A * J' * B).submatrix (Fin.castLE hk) (Fin.castLE hk) := by
  ext i j
  simp [colK, cT, Matrix.mul_apply]

theorem gram_adMat (A B : Matrix (Fin n) (Fin r) E) :
    (cT (sigR (AF F) σ) (adMat F A) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F J * adMat F B =
      adMat F (cT (σ : E →+* E) A * J * B) := by
  simp only [cT_adMat, adMat, JR, Matrix.map_mul]

theorem fr_k (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {k : ℕ} (hk : k ≤ r) :
    Fr (sigR (AF F) σ) (adMat F J) (colK hk (adMat F X)) (colK hk (adMat F Y)) := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  have cJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  refine ⟨sigR_sigR σ hσ, ?_, ?_, ?_, ?_⟩
  · change cT _ (adMat F J) = adMat F J
    rw [cT_adMat, cJ]
  · rw [gram_col, gram_adMat, hW.xx]
    ext i j
    simp [adMat]
  · rw [gram_col, gram_adMat, hW.yy]
    ext i j
    simp [adMat]
  · rw [gram_col, gram_adMat, hW.xy]
    ext i j
    simp [adMat, Matrix.one_apply]

def ek (r k : ℕ) : Fin r → ℝ := fun i => if i.val < k then 1 else 0

theorem char_scalM [IsTotallyReal F] (a b : ℕ) (u : (AF F ⊗[F] E)ˣ) :
    addEquivAddHaarChar (scalM a b u) = GlobalTheory.Doubling.absE F E u ^ (a * b) := by
  let g : GL (Fin a) (AF F ⊗[F] E) :=
    Units.map (Matrix.scalar (Fin a) : (AF F ⊗[F] E) →+* Matrix (Fin a) (Fin a) (AF F ⊗[F] E)).toMonoidHom u
  have e : scalM a b u = GlobalTheory.ModuLR.lrCE g 1 := by
    ext x : 1
    change u.1 • x = (Matrix.scalar (Fin a) u.1) * x * (1 : GL (Fin b) (AF F ⊗[F] E)).1
    rw [Units.val_one, Matrix.mul_one, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hd : Matrix.GeneralLinearGroup.det g = u ^ a := Units.ext (by
    simp [g, Matrix.scalar_apply, Matrix.det_diagonal])
  rw [e, GlobalTheory.ModuLR.chi_lr F E a b g 1, hd, map_one, map_one, one_pow, mul_one, map_pow, ← pow_mul]

section Conj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjC (b : G) : G ≃ₜ* G where
  toFun p := b * p * b⁻¹
  invFun p := b⁻¹ * p * b
  left_inv p := by group
  right_inv p := by group
  map_mul' p q := by group
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

theorem conjC_mul (b c : G) : conjC (b * c) = (conjC c).trans (conjC b) := by
  ext p
  simp [conjC, mul_assoc]

end Conj

theorem sum_castLE {R : Type} [AddCommMonoid R] {k r : ℕ} (hk : k ≤ r) (g : Fin r → R)
    (hg : ∀ l : Fin r, k ≤ l.val → g l = 0) : ∑ l, g l = ∑ l : Fin k, g (Fin.castLE hk l) := by
  let e : Fin k ↪ Fin r := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have h1 := Finset.sum_map Finset.univ e g
  rw [show (∑ l : Fin k, g (Fin.castLE hk l)) = ∑ x ∈ Finset.univ.map e, g x from h1.symm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => hg l ?_).symm
  by_contra h'
  exact hl (Finset.mem_map.2 ⟨⟨l.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem gram_colL {k : ℕ} (hk : k ≤ r) {R : Type} [CommRing R] (s : R →+* R) {m : ℕ} (A : Matrix (Fin n) (Fin r) R)
    (J' : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    cT s (colK hk A) * J' * B = (cT s A * J' * B).submatrix (Fin.castLE hk) id := by
  ext i j
  simp [colK, cT, Matrix.mul_apply]

theorem mul_colK {k : ℕ} (hk : k ≤ r) {R : Type} [CommRing R] {p : ℕ} (M : Matrix (Fin p) (Fin n) R)
    (A : Matrix (Fin n) (Fin r) R) : M * colK hk A = colK hk (M * A) := by
  ext i j
  simp [colK, Matrix.mul_apply]

theorem colK_of_minPar {k : ℕ} (hk : k ≤ r) {R : Type} [CommRing R] {M : Matrix (Fin n) (Fin n) R}
    {A : Matrix (Fin n) (Fin r) R} {B : Matrix (Fin r) (Fin r) R} (hB : B.BlockTriangular id) (e : M * A = A * B) :
    M * colK hk A = colK hk A * B.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
  rw [mul_colK, e]
  ext i j
  simp only [colK, Matrix.submatrix_apply, id, Matrix.mul_apply]
  exact sum_castLE hk _ fun l hl => by
    have hz : B l (Fin.castLE hk j) = 0 := hB (by have := j.2; rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [hz, mul_zero]

theorem exists_omega (h : IsCMExt F E σ) : ∃ ω : E, ω ≠ 0 ∧ σ ω = -ω := by
  by_contra hno
  push_neg at hno
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  have hfix : ∀ y, σ y = y := fun y => by
    by_contra hne
    exact hno (y - σ y) (sub_ne_zero.2 fun e => hne e.symm) (by rw [map_sub, hσ]; ring)
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
      (h.2.2.2 τ y).symm.trans (congrArg τ (hfix y)))))

theorem minPar_of_eich {k : ℕ} (hk : k ≤ r) {R : Type} [CommRing R] (A : Matrix (Fin n) (Fin r) R)
    (D : Matrix (Fin k) (Fin n) R) (hD : D * colK hk A = 0) :
    ∃ B : Matrix (Fin r) (Fin r) R, B.BlockTriangular id ∧ A - colK hk A * (D * A) = A * B := by
  set C := D * A with hCdef
  have hC : ∀ (l m : Fin k), C l (Fin.castLE hk m) = 0 := fun l m => by
    have := congrFun (congrFun hD l) m
    rw [mul_colK] at this
    exact this
  refine ⟨1 - Matrix.of fun l m => if hl : l.val < k then C ⟨l.val, hl⟩ m else 0, fun l m hlm => ?_, ?_⟩
  · have hne : l ≠ m := fun e => (lt_irrefl _ (e ▸ hlm))
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, if_neg hne]
    split_ifs with hl
    · have hm : m.val < k := lt_trans (Fin.lt_iff_val_lt_val.1 hlm) hl
      have := hC ⟨l.val, hl⟩ ⟨m.val, hm⟩
      rw [show Fin.castLE hk ⟨m.val, hm⟩ = m from Fin.ext rfl] at this
      rw [this, sub_zero]
    · simp
  · rw [Matrix.mul_sub, Matrix.mul_one]
    congr 1
    ext i m
    simp only [Matrix.mul_apply, Matrix.of_apply, colK, Matrix.submatrix_apply, id]
    rw [sum_castLE hk (fun l => A i l * if hl : l.val < k then C ⟨l.val, hl⟩ m else 0) fun l hl => by
      rw [dite_eq_right (by omega), mul_zero]]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [dite_eq_left (by simp)]
    rfl

theorem nMat_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {k : ℕ} (hk : k ≤ r)
    (x : PositivityTheory.ThKR.Sieg.Heis (fr_k h hJ hW hk).β) :
    ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular id ∧
      (fr_k h hJ hW hk).nMat x * adMat F X = adMat F X * B := by
  have hZ : cT (sigR (AF F) σ) (colK hk (adMat F X)) * adMat F J * x.1.1 = 0 := x.1.2.1
  have hZ' := (fr_k h hJ hW hk).zero hZ
  have hU : cT (sigR (AF F) σ) (colK hk (adMat F X)) * adMat F J * adMat F X = 0 := by
    rw [gram_colL, gram_adMat, hW.xx]
    ext i j
    simp [adMat]
  rw [(fr_k h hJ hW hk).nMat_apply, (fr_k h hJ hW hk).eich_mul_of _ hU]
  exact minPar_of_eich hk (adMat F X) _ hZ'

def projP {R : Type} [CommRing R] (s : R →+* R) (J' : Matrix (Fin n) (Fin n) R) (A B : Matrix (Fin n) (Fin r) R) :
    Matrix (Fin n) (Fin n) R :=
  1 - A * (cT s B * J') - B * (cT s A * J')

theorem fix_of_perp {k : ℕ} (hk : k ≤ r) {R : Type} [CommRing R] (s : R →+* R) (J' : Matrix (Fin n) (Fin n) R)
    (A B : Matrix (Fin n) (Fin r) R) (M : Matrix (Fin n) (Fin n) R) (d d' : Fin r → R)
    (hA : M * A = A * diagonal d) (hB : M * B = B * diagonal d') (hd : ∀ l : Fin r, k ≤ l.val → d l = 1)
    (hd' : ∀ l : Fin r, k ≤ l.val → d' l = 1) (hV : M * projP s J' A B = projP s J' A B) {m : ℕ}
    (Z : Matrix (Fin n) (Fin m) R) (h1 : cT s (colK hk A) * J' * Z = 0) (h2 : cT s (colK hk B) * J' * Z = 0) :
    M * Z = Z := by
  have hZ : Z = A * (cT s B * J' * Z) + B * (cT s A * J' * Z) + projP s J' A B * Z := by
    simp only [projP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  have e1 : diagonal d * (cT s B * J' * Z) = cT s B * J' * Z := by
    ext l i
    rw [Matrix.diagonal_mul]
    by_cases hl : l.val < k
    · have := congrFun (congrFun h2 ⟨l.val, hl⟩) i
      rw [gram_colL] at this
      have e : Fin.castLE hk ⟨l.val, hl⟩ = l := Fin.ext rfl
      simp only [Matrix.submatrix_apply, id, e, Matrix.zero_apply] at this
      rw [this, mul_zero]
    · rw [hd l (by omega), one_mul]
  have e2 : diagonal d' * (cT s A * J' * Z) = cT s A * J' * Z := by
    ext l i
    rw [Matrix.diagonal_mul]
    by_cases hl : l.val < k
    · have := congrFun (congrFun h1 ⟨l.val, hl⟩) i
      rw [gram_colL] at this
      have e : Fin.castLE hk ⟨l.val, hl⟩ = l := Fin.ext rfl
      simp only [Matrix.submatrix_apply, id, e, Matrix.zero_apply] at this
      rw [this, mul_zero]
    · rw [hd' l (by omega), one_mul]
  conv_lhs => rw [hZ]
  rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, hA, ← Matrix.mul_assoc M B, hB, ← Matrix.mul_assoc M, hV,
    Matrix.mul_assoc, e1, Matrix.mul_assoc B, e2, ← hZ]

theorem projP_adMat (A B : Matrix (Fin n) (Fin r) E) :
    projP (sigR (AF F) σ) (adMat F J) (adMat F A) (adMat F B) =
      adMat F (1 - A * (cT (σ : E →+* E) B * J) - B * (cT (σ : E →+* E) A * J)) := by
  have e : ∀ M : Matrix (Fin n) (Fin n) E, adMat F M = (inclR (F := F) (AF F)).mapMatrix M := fun M => rfl
  conv_rhs => rw [e, map_sub, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
  simp only [projP, cT_adMat, adMat, Matrix.map_mul]

theorem mul_adMat_of_onV {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {P : Matrix (Fin n) (Fin n) E}
    (hM : ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      M *ᵥ incV F z = incV F z)
    (hPX : cT (σ : E →+* E) X * J * P = 0) (hPY : cT (σ : E →+* E) Y * J * P = 0) : M * adMat F P = adMat F P := by
  ext i j
  have h1 : (cT (σ : E →+* E) X * J) *ᵥ (fun l => P l j) = 0 := by
    ext i'
    have := congrFun (congrFun hPX i') j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have h2 : (cT (σ : E →+* E) Y * J) *ᵥ (fun l => P l j) = 0 := by
    ext i'
    have := congrFun (congrFun hPY i') j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have := congrFun (hM _ h1 h2) i
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, incV, adMat] using this

theorem char_k (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (H : Subgroup (GAd σ J)) [LocallyCompactSpace H] (hHP : ∀ p ∈ H, p ∈ minPar σ J X)
    (hPH : ∀ p ∈ minPar σ J X, p ∈ H) {a : (Fin r → ℝ) → GAd σ J}
    (onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i))))
    (onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i))))
    (onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z)
    (haH : ∀ t, a t ∈ H) {k : ℕ} (hk : k ≤ r) (c : ℝ) :
    (mulEquivHaarChar (conjC (⟨a (c • ek r k), haH _⟩ : H)) : ℝ) =
      Real.exp (2 * Module.finrank ℚ F * c * (k * ((n : ℝ) - k))) := by
  have : IsTotallyReal F := h.1
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  set fr := fr_k h hJ hW hk
  set s := sigR (AF F) σ
  let j : H →* GL (Fin n) (AF F ⊗[F] E) := (matHom (AF F) σ J).comp H.subtype
  have hj : IsEmbedding j := (isEmbedding_matHom (AF F) σ J).comp IsEmbedding.subtypeVal
  have hU : ∀ p : H, cT s (j p).1 * adMat F J * (j p).1 = adMat F J := fun p => p.1.2
  have hP : ∀ p : H, ∃ B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E),
      (j p).1 * colK hk (adMat F X) = colK hk (adMat F X) * B := fun p => by
    obtain ⟨B, hB, e⟩ := hHP p.1 p.2
    exact ⟨_, colK_of_minPar hk hB e⟩
  have hN : ∀ x, ∃ p : H, (j p).1 = fr.nMat x := fun x => by
    let g : GL (Fin n) (AF F ⊗[F] E) := (MonoidHom.toHomUnits fr.nMat) x
    have hg : g ∈ HR (AF F) σ J := fr.nMat_unitary x
    let q : GAd σ J := ⟨g, hg⟩
    exact ⟨⟨q, hPH q (nMat_minPar h hJ hW hk x)⟩, rfl⟩
  have hu : s (rIdU F E c).1 = (rIdU F E c).1 := sigR_algebraMap σ _
  set b : H := ⟨a (c • ek r k), haH _⟩
  have hek : ∀ l : Fin r, l.val < k → (c • ek r k) l = c := fun l hl => by simp [ek, hl]
  have hek0 : ∀ l : Fin r, ¬ l.val < k → (c • ek r k) l = 0 := fun l hl => by simp [ek, hl]
  have e0 : (j b).1 = (matHom (AF F) σ J (a (c • ek r k))).1 := rfl
  have bX : (j b).1 * colK hk (adMat F X) = (rIdU F E c).1 • colK hk (adMat F X) := by
    rw [e0, mul_colK, onX]
    ext i l
    simp only [colK, Matrix.submatrix_apply, id, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    rw [hek _ (by simp), mul_comm]
    rfl
  have bY : (j b).1 * colK hk (adMat F Y) = (rIdU F E c)⁻¹.1 • colK hk (adMat F Y) := by
    rw [e0, mul_colK, onY]
    ext i l
    simp only [colK, Matrix.submatrix_apply, id, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    rw [hek _ (by simp), mul_comm]
    rfl
  have bZ : ∀ (m : ℕ) (Z : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT s (colK hk (adMat F X)) * adMat F J * Z = 0 →
      cT s (colK hk (adMat F Y)) * adMat F J * Z = 0 → (j b).1 * Z = Z := fun m Z h1 h2 => by
    rw [e0]
    have hPX : cT (σ : E →+* E) X * J * (1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)) = 0 := by
      simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hW.xx, hW.xy, Matrix.zero_mul, Matrix.one_mul,
        sub_zero, sub_self]
    have hPY : cT (σ : E →+* E) Y * J * (1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)) = 0 := by
      simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, yx_eq_one hσ hJ hW, hW.yy, Matrix.zero_mul,
        Matrix.one_mul, sub_zero, sub_self]
    refine fix_of_perp hk s (adMat F J) (adMat F X) (adMat F Y) _ _ _ (onX _) (onY _) (fun l hl => ?_) (fun l hl => ?_)
      ?_ Z h1 h2
    · rw [hek0 l (by omega), rId_zero', map_one]
    · rw [hek0 l (by omega), neg_zero, rId_zero', map_one]
    · rw [projP_adMat]
      exact mul_adMat_of_onV (onV _) hPX hPY
  obtain ⟨ω, hω0, hωσ⟩ := exists_omega h
  let ωR : (AF F ⊗[F] E)ˣ := Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 ω hω0)
  have hωR : s ωR.1 = -ωR.1 := by
    change s (inclR (F := F) (AF F) ω) = -inclR (F := F) (AF F) ω
    rw [sigR_inclR, hωσ, map_neg]
  have key := PositivityTheory.ThKR.Sieg.char_conj fr (continuous_sigR σ) ωR hωR hu j hj hU hP hN b bX bY bZ (conjC b)
    (fun p => rfl)
  rw [char_scalM, char_scalM] at key
  have hA := absE_rIdU h.2.2.1 c
  have key' := congrArg (fun x : ℝ≥0 => (x : ℝ)) key
  simp only [NNReal.coe_mul, NNReal.coe_pow] at key'
  rw [hA] at key'
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul] at key'
  have e2 : (mulEquivHaarChar (conjC b) : ℝ) = Real.exp (((n * k : ℕ) : ℝ) * (2 * Module.finrank ℚ F * c)) /
      Real.exp (((k * k : ℕ) : ℝ) * (2 * Module.finrank ℚ F * c)) := by
    rw [← key']
    field_simp
  rw [e2, ← Real.exp_sub]
  congr 1
  push_cast
  ring

theorem sum_range_rho (n k : ℕ) : ∑ i ∈ Finset.range k, ((n : ℝ) - 2 * i - 1) = k * ((n : ℝ) - k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem rho_scaled_basis_vector (n r k : ℕ) (hk : k ≤ r) (c : ℝ) : rho2 n (c • ek r k) = c * (k * ((n : ℝ) - k)) := by
  have e : ∀ i : Fin r, ((n : ℝ) - 2 * (i.val : ℝ) - 1) * (c • ek r k) i =
      if i.val < k then c * ((n : ℝ) - 2 * (i.val : ℝ) - 1) else 0 := by
    intro i
    simp only [ek, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  simp only [rho2, e]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then c * ((n : ℝ) - 2 * (i : ℝ) - 1) else 0) r,
    ← Finset.sum_filter]
  have : (Finset.range r).filter (· < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, ← Finset.mul_sum, sum_range_rho]

theorem ek_succ (i : Fin r) (c : ℝ) : c • ek r (i.val + 1) = c • ek r i.val + Pi.single i c := by
  funext j
  simp only [ek, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h1 : j = i
  · subst h1
    simp
  · have h3 : j.val ≠ i.val := fun e => h1 (Fin.ext e)
    by_cases h2 : j.val < i.val
    · simp [h1, h2, show j.val < i.val + 1 by omega]
    · simp [h1, h2, show ¬ j.val < i.val + 1 by omega]

theorem char_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (H : Subgroup (GAd σ J)) [LocallyCompactSpace H] (hHP : ∀ p ∈ H, p ∈ minPar σ J X)
    (hPH : ∀ p ∈ minPar σ J X, p ∈ H) {a : (Fin r → ℝ) → GAd σ J} (add : ∀ s t, a (s + t) = a s * a t)
    (onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i))))
    (onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i))))
    (onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z)
    (haH : ∀ t, a t ∈ H) (s : Fin r → ℝ) :
    (mulEquivHaarChar (conjC (⟨a s, haH s⟩ : H)) : ℝ) = Real.exp (2 * Module.finrank ℚ F * rho2 n s) := by
  have hmul : ∀ s t, mulEquivHaarChar (conjC (⟨a (s + t), haH _⟩ : H)) =
      mulEquivHaarChar (conjC (⟨a t, haH t⟩ : H)) * mulEquivHaarChar (conjC (⟨a s, haH s⟩ : H)) := fun s t => by
    rw [show (⟨a (s + t), haH _⟩ : H) = ⟨a s, haH s⟩ * ⟨a t, haH t⟩ from Subtype.ext (add s t), conjC_mul,
      mulEquivHaarChar_trans]
  let f : (Fin r → ℝ) →+ ℝ := AddMonoidHom.mk' (fun s => Real.log (mulEquivHaarChar (conjC (⟨a s, haH s⟩ : H))))
    fun s t => by
      rw [hmul, NNReal.coe_mul, Real.log_mul (NNReal.coe_pos.2 (mulEquivHaarChar_pos _)).ne' (NNReal.coe_pos.2 (mulEquivHaarChar_pos _)).ne', add_comm]
  let g : (Fin r → ℝ) →+ ℝ := AddMonoidHom.mk' (fun s => 2 * Module.finrank ℚ F * rho2 n s) fun s t => by
    simp only [rho2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hk : ∀ k, k ≤ r → ∀ c : ℝ, f (c • ek r k) = g (c • ek r k) := fun k hk c => by
    change Real.log (mulEquivHaarChar (conjC (⟨a (c • ek r k), haH _⟩ : H)) : ℝ) =
      2 * Module.finrank ℚ F * rho2 n (c • ek r k)
    rw [char_k h hJ hW H hHP hPH onX onY onV haH hk c, Real.log_exp, rho_scaled_basis_vector n r k hk]
    ring
  have hs : ∀ (i : Fin r) (c : ℝ), f (Pi.single i c) = g (Pi.single i c) := fun i c => by
    have e1 := congrArg f (ek_succ i c)
    have e2 := congrArg g (ek_succ i c)
    rw [map_add (f := _)] at e1 e2
    rw [hk _ (by omega) c, hk _ (by omega) c] at e1
    linarith
  have hfg : f s = g s := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single s, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hs i (s i)
  have e : Real.log (mulEquivHaarChar (conjC (⟨a s, haH s⟩ : H))) = 2 * Module.finrank ℚ F * rho2 n s := hfg
  rw [← e]
  exact (Real.exp_log (NNReal.coe_pos.2 (mulEquivHaarChar_pos _))).symm

theorem map_mul_torus_of (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (H : Subgroup (GAd σ J)) (hH : IsClosed (H : Set (GAd σ J))) (hHP : ∀ p ∈ H, p ∈ minPar σ J X)
    (hPH : ∀ p ∈ minPar σ J X, p ∈ H) {a : (Fin r → ℝ) → GAd σ J} (add : ∀ s t, a (s + t) = a s * a t)
    (onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i))))
    (onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i))))
    (onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z)
    (haH : ∀ t, a t ∈ H) (ν : Measure H) [ν.IsHaarMeasure] (s : Fin r → ℝ) :
    ν.map (· * (⟨a s, haH s⟩ : H)) = ENNReal.ofReal (Real.exp (2 * (Module.finrank ℚ F : ℝ) * rho2 n s)) • ν := by
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have a0 : a 0 = 1 := by
    have := add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have hb : (⟨a s, haH s⟩ : H)⁻¹ = ⟨a (-s), haH (-s)⟩ := by
    refine Subtype.ext ?_
    change (a s)⁻¹ = a (-s)
    rw [inv_eq_iff_mul_eq_one, ← add, add_neg_cancel, a0]
  rw [PositivityTheory.ThKR.Sieg.map_mul_right_of_char ν _ (conjC (⟨a s, haH s⟩ : H)⁻¹) (fun p => by simp [conjC])]
  have hc := char_torus h hJ hW H hHP hPH add onX onY onV haH (-s)
  rw [← hb] at hc
  have hr : rho2 n (-s) = -rho2 n s := by simp [rho2, Finset.sum_neg_distrib]
  rw [hr] at hc
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, hc, ← Real.exp_neg]
  congr 2
  ring

end PositivityTheory.ThKR.PMod

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.SiegelGood
set_option linter.unusedSectionVars false

noncomputable section

open Topology Set Matrix
open Formalism.UG (cT cT_mul cT_one)

namespace PositivityTheory.ThKR.Sieg

section Alg

variable {R : Type} [CommRing R] {s : R →+* R} {n k : ℕ} {J : Matrix (Fin n) (Fin n) R} {X Y : Matrix (Fin n) (Fin k) R}

theorem sub_one_pow_eq_zero {B : Matrix (Fin k) (Fin k) R} (hB : B.BlockTriangular id) (hd : ∀ i, B i i = 1) :
    (B - 1) ^ k = 0 := by
  have key : ∀ m (i j : Fin k), j.val < i.val + m → ((B - 1) ^ m) i j = 0 := by
    intro m
    induction m with
    | zero =>
      intro i j hij
      rw [pow_zero, Matrix.one_apply_ne]
      intro e
      subst e
      omega
    | succ m ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < i.val + m
      · rw [ih i l hl, zero_mul]
      · have hjl : j.val ≤ l.val := by omega
        rcases hjl.lt_or_eq with h' | h'
        · have hne : l ≠ j := fun e => by rw [e] at h'; exact lt_irrefl _ h'
          rw [Matrix.sub_apply, hB (show id j < id l from h'), Matrix.one_apply_ne hne, sub_zero, mul_zero]
        · have e : l = j := Fin.ext h'.symm
          rw [e, Matrix.sub_apply, hd, Matrix.one_apply_eq, sub_self, mul_zero]
  ext i j
  rw [key k i j (by omega), Matrix.zero_apply]

theorem cT_pow (P : Matrix (Fin k) (Fin k) R) (m : ℕ) : cT s (P ^ m) = cT s P ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, cT_one]
  | succ m ih => rw [pow_succ, cT_mul, ih, pow_succ']

theorem Fr.isNilpotent_sub_one (h : Fr s J X Y) {U : Matrix (Fin n) (Fin n) R} (hU : cT s U * J * U = J)
    {B : Matrix (Fin k) (Fin k) R} (hB : U * X = X * B) (hBt : B.BlockTriangular id) (hd : ∀ i, B i i = 1)
    (A : Matrix (Fin k) (Fin n) R) (hA : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → (U - 1) * Z = X * (A * Z)) :
    IsNilpotent (U - 1) := by
  obtain ⟨-, h2, h3, h4⟩ := h.par hU hB
  set Q := cT s X * J * (U * Y) with hQdef
  have hP : IsNilpotent (cT s (B - 1)) := ⟨k, by rw [← cT_pow, sub_one_pow_eq_zero hBt hd, cT_zero]⟩
  have hcB : cT s B = 1 + cT s (B - 1) := by rw [cT_sub, cT_one]; abel
  have hQ1 : Q - 1 = -(Q * cT s (B - 1)) := by
    have e := h3
    rw [hcB, Matrix.mul_add, Matrix.mul_one] at e
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, e, sub_self]
  have hcomm : Commute Q (cT s (B - 1)) := by
    rw [cT_sub, cT_one]
    exact (show Commute Q (cT s B) from h3.trans h2.symm).sub_right (Commute.one_right Q)
  have hQn : IsNilpotent (Q - 1) := by
    rw [hQ1]
    exact (hcomm.isNilpotent_mul_left hP).neg
  obtain ⟨a, ha⟩ := hQn
  have hXN : cT s X * J * (U - 1) = (Q - 1) * (cT s X * J) := by
    rw [Matrix.mul_sub, Matrix.mul_one, h4, Matrix.sub_mul, Matrix.one_mul]
  have hMN : ∀ m : ℕ, cT s X * J * (U - 1) ^ m = (Q - 1) ^ m * (cT s X * J) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.one_mul]
    | succ m ih => rw [pow_succ', ← Matrix.mul_assoc, hXN, Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← pow_succ']
  have hNX1 : (U - 1) * X = X * (B - 1) := by
    rw [Matrix.sub_mul, hB, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hNX : ∀ m : ℕ, (U - 1) ^ m * X = X * (B - 1) ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, hNX1, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h0 : cT s X * J * (U - 1) ^ a = 0 := by rw [hMN, ha, Matrix.zero_mul]
  refine ⟨k + (a + 1), ?_⟩
  rw [pow_add, pow_succ', hA _ h0, ← Matrix.mul_assoc, hNX, sub_one_pow_eq_zero hBt hd, Matrix.mul_zero,
    Matrix.zero_mul]

theorem Fr.mul_eq_self (h : Fr s J X Y) {b : Matrix (Fin n) (Fin n) R}
    (hb : b * (1 - X * (cT s Y * J) - Y * (cT s X * J)) = 1 - X * (cT s Y * J) - Y * (cT s X * J))
    (Z : Matrix (Fin n) (Fin n) R) (h1 : cT s X * J * Z = 0) (h2 : cT s Y * J * Z = 0) : b * Z = Z := by
  have h1' : cT s X * (J * Z) = 0 := by rw [← Matrix.mul_assoc]; exact h1
  have h2' : cT s Y * (J * Z) = 0 := by rw [← Matrix.mul_assoc]; exact h2
  have e : (1 - X * (cT s Y * J) - Y * (cT s X * J)) * Z = Z := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h1', h2', Matrix.mul_zero, sub_zero]
  rw [← e, ← Matrix.mul_assoc, hb]

end Alg

section Top

theorem eq_zero_of_isNilpotent_of_pow_mem {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (hN : IsNilpotent N)
    {C : Set (Matrix (Fin n) (Fin n) ℂ)} (hC : IsCompact C) (hp : ∀ j : ℕ, (1 + N) ^ j ∈ C) : N = 0 := by
  have step : ∀ m : ℕ, N ^ (m + 1 + 1) = 0 → N ^ (m + 1) = 0 := by
    intro m hm
    by_contra hne
    have hlin : ∀ j : ℕ, N ^ m * (1 + N) ^ j = N ^ m + (j : ℂ) • N ^ (m + 1) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, ← Matrix.mul_assoc, ih]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, ← pow_succ, hm, smul_zero,
          add_zero, Nat.cast_succ, add_smul, one_smul]
        abel
    obtain ⟨a, b, hab⟩ : ∃ a b, (N ^ (m + 1)) a b ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Matrix.ext hall)
    have hg : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => (N ^ m * M) a b :=
      (continuous_const.matrix_mul continuous_id).matrix_elem a b
    obtain ⟨R, hR⟩ := (hC.image hg).isBounded.exists_norm_le
    obtain ⟨j, hj⟩ := exists_nat_gt ((R + ‖(N ^ m) a b‖) / ‖(N ^ (m + 1)) a b‖)
    have h1 := hR _ ⟨_, hp j, rfl⟩
    simp only [hlin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h1
    have h2 : ‖(j : ℂ) * (N ^ (m + 1)) a b‖ ≤ R + ‖(N ^ m) a b‖ := by
      have e : (j : ℂ) * (N ^ (m + 1)) a b = ((N ^ m) a b + (j : ℂ) * (N ^ (m + 1)) a b) - (N ^ m) a b := by ring
      rw [e]
      exact (norm_sub_le _ _).trans (by linarith)
    rw [norm_mul, Complex.norm_natCast, ← le_div_iff₀ (norm_pos_iff.2 hab)] at h2
    exact absurd (hj.trans_le h2) (lt_irrefl _)
  have hall : ∀ m : ℕ, N ^ (m + 1) = 0 → N = 0 := by
    intro m
    induction m with
    | zero => intro h; rwa [zero_add, pow_one] at h
    | succ m ih => intro h; exact ih (step m h)
  obtain ⟨p, hp0⟩ := hN
  rcases p with _ | p
  · rw [← Matrix.mul_one N, ← pow_zero N, hp0, Matrix.mul_zero]
  · exact hall p hp0

end Top

end PositivityTheory.ThKR.Sieg

namespace PositivityTheory.ThKR

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Orb (archMat archMat_apply archMat_eq_archEquiv continuous_infEmb)
open scoped TensorProduct

section Adelic

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem map_cT_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {a b : Type} (P : Matrix a b E) :
    (Formalism.UG.cT (σ : E →+* E) P).map (inclR R) = Formalism.UG.cT (sigR R σ) (P.map (inclR R)) := by
  ext i j
  simp only [cT, Matrix.map_apply, Matrix.transpose_apply]
  exact (sigR_inclR R σ _).symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

theorem gram_adMat {a b : ℕ} (P : Matrix (Fin n) (Fin a) E) (Q : Matrix (Fin n) (Fin b) E) :
    Formalism.UG.cT (sigR (AF F) σ) (adMat F P) * JR (F := F) (AF F) J * adMat F Q = (Formalism.UG.cT (σ : E →+* E) P * J * Q).map (inclR (F := F) (AF F)) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_cT_inclR]
  rfl

theorem fr_adMat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    Sieg.Fr (sigR (AF F) σ) (JR (F := F) (AF F) J) (adMat F X) (adMat F Y) := by
  refine ⟨sigR_sigR (AF F) (sigma_sigma h), ?_, ?_, ?_, ?_⟩
  · have cJ : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    rw [JR, ← map_cT_inclR, cJ]
  · rw [gram_adMat, hW.xx, Matrix.map_zero _ (map_zero _)]
  · rw [gram_adMat, hW.yy, Matrix.map_zero _ (map_zero _)]
  · rw [gram_adMat, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

theorem unitary_matHom (g : GAd σ J) :
    Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (F := F) (AF F) J * (matHom _ σ J g).1 = JR (F := F) (AF F) J :=
  g.2

theorem projArch_eq_one_of_unipMin (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J))) {u : GAd σ J} (hu : u ∈ unipMin σ J X)
    (huK : u ∈ K) (w : InfinitePlace F) : projArch σ J w u = 1 := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨B, hBt, hd, hB, hz⟩ := hu
  have hfr := fr_adMat h hJ hW
  let P0 : Matrix (Fin n) (Fin n) E := 1 - Y * (Formalism.UG.cT (σ : E →+* E) X * J)
  have hM : Formalism.UG.cT (σ : E →+* E) X * J * P0 = 0 := by
    simp only [P0]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hW.xy, Matrix.one_mul, sub_self]
  have hcol : ∀ j, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ (fun i => P0 i j) = 0 := fun j =>
    funext fun k => congrFun (congrFun hM k) j
  choose a ha using fun j => hz (fun i => P0 i j) (hcol j)
  let A : Matrix (Fin r) (Fin n) (AF F ⊗[F] E) := Matrix.of fun k j => a j k
  have hUA : ((matHom _ σ J u).1 - 1) * P0.map (inclR (F := F) (AF F)) = adMat F X * A := by
    ext i j
    exact congrFun (ha j) i
  have hP0 : P0.map (inclR (F := F) (AF F)) =
      1 - adMat F Y * (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by
    simp only [P0]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul,
      map_cT_inclR]
    rfl
  have hA : ∀ Z : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J * Z = 0 →
      ((matHom _ σ J u).1 - 1) * Z = adMat F X * (A * Z) := by
    intro Z hZ
    have e : P0.map (inclR (F := F) (AF F)) * Z = Z := by
      rw [hP0, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hZ, Matrix.mul_zero, sub_zero]
    calc ((matHom _ σ J u).1 - 1) * Z = ((matHom _ σ J u).1 - 1) * (P0.map (inclR (F := F) (AF F)) * Z) := by rw [e]
      _ = adMat F X * (A * Z) := by rw [← Matrix.mul_assoc, hUA, Matrix.mul_assoc]
  have hnil := hfr.isNilpotent_sub_one (unitary_matHom u) hB hBt hd A hA
  let φ : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hmat : ∀ g : GAd σ J, archMat σ J τ (projArch σ J w g) = (matHom _ σ J g).1.map φ := fun g => by
    rw [archMat_apply, matHom_projArch]
    rfl
  have hN : IsNilpotent (archMat σ J τ (projArch σ J w u) - 1) := by
    have := hnil.map (φ.mapMatrix : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+* Matrix (Fin n) (Fin n) ℂ)
    rw [map_sub, map_one, RingHom.mapMatrix_apply] at this
    rwa [hmat]
  have hcA : Continuous fun y : GArch σ J w => archMat σ J τ y := by
    simp only [archMat_apply]
    exact (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).matrix_map (continuous_infEmb τ)
  have hc : Continuous fun g : GAd σ J => archMat σ J τ (projArch σ J w g) := hcA.comp (continuous_projArch σ J w)
  have h0 := Sieg.eq_zero_of_isNilpotent_of_pow_mem hN (hK.image hc) fun j =>
    ⟨u ^ j, K.pow_mem huK j, by simp only [add_sub_cancel, map_pow]⟩
  have h1 : archMat σ J τ (projArch σ J w u) = 1 := sub_eq_zero.1 h0
  apply (archEquiv J h τ).injective
  refine Subtype.ext (Units.ext ?_)
  rw [← archMat_eq_archEquiv J h, ← archMat_eq_archEquiv J h, h1, map_one]

theorem commute_of_good_position (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {b : GAd σ J} (hb : b ∈ infPts σ J) {dX dY : Fin r → AF F ⊗[F] E}
    (hbX : (matHom _ σ J b).1 * adMat F X = adMat F X * diagonal dX)
    (hbY : (matHom _ σ J b).1 * adMat F Y = adMat F Y * diagonal dY)
    (hbV : ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
      (matHom _ σ J b).1 *ᵥ (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i))
    {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J))) (hG : GoodPosition σ J X Y K)
    {m : GAd σ J} (hm : m ∈ minPar σ J X) (hmK : m ∈ K) : b * m = m * b := by
  obtain ⟨l, hl, hlK, u, hu, huK, rfl⟩ := hG m hm hmK
  have hfr := fr_adMat h hJ hW
  let P : Matrix (Fin n) (Fin n) E := 1 - X * (Formalism.UG.cT (σ : E →+* E) Y * J) - Y * (Formalism.UG.cT (σ : E →+* E) X * J)
  have hPX : Formalism.UG.cT (σ : E →+* E) X * J * P = 0 := by
    simp only [P]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 :=
    (show Sieg.Fr (σ : E →+* E) J X Y from ⟨sigma_sigma h, Matrix.ext fun i j => hJ.1 i j, hW.xx, hW.yy, hW.xy⟩).yx
  have hPY : Formalism.UG.cT (σ : E →+* E) Y * J * P = 0 := by
    simp only [P]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc _ Y, yx, hW.yy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hbP : (matHom _ σ J b).1 * P.map (inclR (F := F) (AF F)) = P.map (inclR (F := F) (AF F)) := by
    ext i j
    exact congrFun (hbV (fun k => P k j) (funext fun k => congrFun (congrFun hPX k) j)
      (funext fun k => congrFun (congrFun hPY k) j)) i
  have hPad : P.map (inclR (F := F) (AF F)) = 1 - adMat F X * (Formalism.UG.cT (sigR (AF F) σ) (adMat F Y) * JR (F := F) (AF F) J) -
      adMat F Y * (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (F := F) (AF F) J) := by
    simp only [P]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, map_cT_inclR, map_cT_inclR]
    rfl
  rw [hPad] at hbP
  have hlb : b * l = l * b := by
    obtain ⟨d, d', hd, hd'⟩ := hl
    apply matHom_injective _ σ J
    apply Units.ext
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    exact hfr.comm (unitary_matHom l) hd hd' hbX hbY (by rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; simp [mul_comm])
      (by rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; simp [mul_comm]) fun Z h1 h2 => hfr.mul_eq_self hbP Z h1 h2
  have hub : b * u = u * b := by
    have hw := projArch_eq_one_of_unipMin h hJ hW hK hu huK
    refine GAd_ext σ J (fun w => by rw [map_mul, map_mul, hw, mul_one, one_mul]) fun v => by
      rw [map_mul, map_mul, mem_infPts_iff_forall.1 hb v, mul_one, one_mul]
  rw [← mul_assoc, hlb, mul_assoc, hub, mul_assoc]

end Adelic

end PositivityTheory.ThKR

end
end

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open PositivityTheory.ThKEst PositivityTheory.ThKEst.Sieg

namespace PositivityTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}


variable (σ J X Y) in
structure IsTorus (a : (Fin r → ℝ) → GAd σ J) : Prop where
  add : ∀ s t, a (s + t) = a s * a t
  cont : Continuous a
  tor : ∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)
  onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i)))
  onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i)))
  onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
    (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z

theorem exists_isTorus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ a, IsTorus σ J X Y a := by
  obtain ⟨a, h1, h2, h3, h4⟩ := exists_torus h hJ hW
  exact ⟨a, ⟨h1, h2, h3, fun t => (h4 t).1, fun t => (h4 t).2.1, fun t => (h4 t).2.2⟩⟩

theorem mul_mem_minPar {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) : p * q ∈ minPar σ J X :=
  mul_mem_minimal_parabolic hp hq

theorem inv_mem_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X :=
  inv_mem_minimal_parabolic h hJ hW hp


variable (X) in
def minParSub (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : Subgroup (GAd σ J) where
  carrier := minPar σ J X
  one_mem' := one_mem_minPar σ J X
  mul_mem' := mul_mem_minPar
  inv_mem' := inv_mem_minPar h hJ hW

theorem isClosed_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minPar σ J X) :=
  isClosed_minimal_parabolic h hJ hW

theorem minParOne_subset : minParOne σ J X ⊆ minPar σ J X := fun _ ⟨B, hB, e, _⟩ => ⟨B, hB, e⟩

theorem IsTorus.mem {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (t : Fin r → ℝ) : a t ∈ minPar σ J X :=
  ⟨_, Matrix.blockTriangular_diagonal _, ha.onX t⟩

def IsTorus.sub {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (t : Fin r → ℝ) : minParSub X h hJ hW :=
  ⟨a t, ha.mem t⟩

theorem exists_tau (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) :
    ∃ τ : minParSub X h hJ hW → Fin r → ℝ, Continuous τ ∧ (∀ p q, τ (p * q) = τ p + τ q) ∧
      (∀ t, τ (ha.sub h hJ hW t) = t) ∧ (∀ p (hp : p ∈ minParOne σ J X), τ ⟨p, minParOne_subset hp⟩ = 0) ∧
      ∀ p : minParSub X h hJ hW, p.1 * (a (τ p))⁻¹ ∈ minParOne σ J X :=
  exists_torus_section h hJ hW (minParSub X h hJ hW) (fun _ => Iff.rfl) ha.add ha.onX (ha.sub h hJ hW) (fun _ => rfl)

theorem map_mul_torus (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {a : (Fin r → ℝ) → GAd σ J}
    (ha : IsTorus σ J X Y a) (ν : Measure (minParSub X h hJ hW)) [ν.IsHaarMeasure] (s : Fin r → ℝ) :
    ν.map (· * ha.sub h hJ hW s) = ENNReal.ofReal (Real.exp (2 * (Module.finrank ℚ F : ℝ) * rho2 n s)) • ν :=
  PMod.map_mul_torus_of h hJ hW (minParSub X h hJ hW) (isClosed_minPar h hJ hW) (fun _ hp => hp) (fun _ hp => hp)
    ha.add ha.onX ha.onY ha.onV ha.mem ν s

theorem commute_of_goodPosition (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {K : Subgroup (GAd σ J)} (hK : IsCompact (K : Set (GAd σ J)))
    (hG : GoodPosition σ J X Y K) {m : GAd σ J} (hm : m ∈ minPar σ J X) (hmK : m ∈ K) (t : Fin r → ℝ) :
    a t * m = m * a t :=
  commute_of_good_position h hJ hW (ha.tor t).1 (ha.onX t) (ha.onY t) (ha.onV t) hK hG hm hmK

end PositivityTheory.ThKR

end
