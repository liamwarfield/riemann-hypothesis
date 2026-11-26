module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConjScalarIdeleUnipotentCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLevi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLevi
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

namespace GlobalTheory.CentralLevi

theorem exists_unit_smul_of_central : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  intro F E _ _ _ _ _ σ n J r m X Y Z J₀ f g hg hc
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ f

  let Dα : GL (Fin (r + 1)) (AF F ⊗[F] E) → GL (Fin (r + 1)) (AF F ⊗[F] E) := fun α =>
    ⟨cT (sigR (AF F) σ) (α⁻¹).1, cT (sigR (AF F) σ) α.1,
      by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one],
      by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one]⟩
  have hmem : ∀ α, lv α ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r} := fun α => by
    refine Subgroup.mem_iInf.2 fun k => Subgroup.mem_iInf.2 fun hk => ?_
    rw [Finset.mem_singleton] at hk
    subst hk
    exact ⟨⟨α, trivial, hlv.onC α⟩, ⟨Dα α, trivial, hlv.onD α⟩⟩
  obtain ⟨B, -, hB⟩ := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg (Fin.last r)) (Finset.mem_singleton_self _)).1
  change GL (Fin (r + 1)) (AF F ⊗[F] E) at B
  change (matHom _ σ J g).1 * adMat F X = adMat F X * B.1 at hB
  have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, f.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcomm : ∀ α : GL (Fin (r + 1)) (AF F ⊗[F] E), B.1 * α.1 = α.1 * B.1 := fun α => by
    have e := congrArg (fun h => (matHom _ σ J h).1 * adMat F X) (hc (lv α) (hmem α))
    simp only [map_mul, Units.val_mul] at e
    have e1 : (matHom _ σ J g).1 * (matHom _ σ J (lv α)).1 * adMat F X = adMat F X * (B.1 * α.1) := by
      rw [Matrix.mul_assoc, hlv.onC, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have e2 : (matHom _ σ J (lv α)).1 * (matHom _ σ J g).1 * adMat F X = adMat F X * (α.1 * B.1) := by
      rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hlv.onC, Matrix.mul_assoc]
    have := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) (e1.symm.trans (e.trans e2))
    simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul] using this
  obtain ⟨c, hcB⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := B.1) fun t =>
    (hcomm ⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩).symm
  have hu : IsUnit c := by
    have h1 := congrFun (congrFun (Units.mul_inv B) 0) 0
    rw [← hcB, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h1
    exact ⟨⟨c, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, ?_⟩
  rw [hB, ← hcB, IsUnit.unit_spec]
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

end GlobalTheory.CentralLevi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSmulOfCentralParabolicLeviStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r m : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ → ∀ g ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, (∀ k ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, g * k = k * g) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F X = (l : AF F ⊗[F] E) • adMat F X := by
  first | exact @GlobalTheory.CentralLevi.exists_unit_smul_of_central | exact GlobalTheory.CentralLevi.exists_unit_smul_of_central | (intros; apply GlobalTheory.CentralLevi.exists_unit_smul_of_central <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadical
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

section Ring

variable {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) {a b c : ℕ}

theorem gram_comb (X₁ Y₁ : Matrix (Fin n) (Fin a) R) (X₂ Y₂ : Matrix (Fin n) (Fin b) R)
    (X₃ Y₃ : Matrix (Fin n) (Fin c) R) (R₁ : Matrix (Fin a) (Fin n) R) (R₂ : Matrix (Fin b) (Fin n) R)
    (R₃ : Matrix (Fin c) (Fin n) R)
    (h11 : gr s A Y₁ Y₁ = gr s A X₁ X₁) (h12 : gr s A Y₁ Y₂ = gr s A X₁ X₂) (h13 : gr s A Y₁ Y₃ = gr s A X₁ X₃)
    (h21 : gr s A Y₂ Y₁ = gr s A X₂ X₁) (h22 : gr s A Y₂ Y₂ = gr s A X₂ X₂) (h23 : gr s A Y₂ Y₃ = gr s A X₂ X₃)
    (h31 : gr s A Y₃ Y₁ = gr s A X₃ X₁) (h32 : gr s A Y₃ Y₂ = gr s A X₃ X₂) (h33 : gr s A Y₃ Y₃ = gr s A X₃ X₃) :
    gr s A (Y₁ * R₁ + Y₂ * R₂ + Y₃ * R₃) (Y₁ * R₁ + Y₂ * R₂ + Y₃ * R₃) =
      gr s A (X₁ * R₁ + X₂ * R₂ + X₃ * R₃) (X₁ * R₁ + X₂ * R₂ + X₃ * R₃) := by
  simp only [gr_add_left, gr_add_right, gr_mul_left, gr_mul_right, h11, h12, h13, h21, h22, h23, h31, h32, h33]

theorem comb_mul {p : ℕ} (Y₁ : Matrix (Fin n) (Fin a) R) (Y₂ : Matrix (Fin n) (Fin b) R)
    (Y₃ : Matrix (Fin n) (Fin c) R) (R₁ : Matrix (Fin a) (Fin n) R) (R₂ : Matrix (Fin b) (Fin n) R)
    (R₃ : Matrix (Fin c) (Fin n) R) (X : Matrix (Fin n) (Fin p) R) :
    (Y₁ * R₁ + Y₂ * R₂ + Y₃ * R₃) * X = Y₁ * (R₁ * X) + Y₂ * (R₂ * X) + Y₃ * (R₃ * X) := by
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem cT_smul' {p q : Type} (x : R) (M : Matrix p q R) : cT s (x • M) = s x • cT s M := by
  ext i k; simp [cT]

end Ring

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {j m : ℕ} (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
  (J₀ : Matrix (Fin m) (Fin m) E)

def uMat (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  adMat F C * adMat F (cT (σ : E →+* E) D * J) +
    (adMat F Z + adMat F C * b) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
    (adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c) * adMat F (cT (σ : E →+* E) C * J)

variable {σ J C D Z J₀}

theorem adMat_mul' {p q r : ℕ} (X : Matrix (Fin p) (Fin q) E) (Y : Matrix (Fin q) (Fin r) E) :
    adMat F X * adMat F Y = adMat F (X * Y) := (Matrix.map_mul).symm

theorem adMat_add' {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) E) : adMat F X + adMat F Y = adMat F (X + Y) :=
  (Matrix.map_add _ (map_add _) X Y).symm

theorem adMat_one' {p : ℕ} : adMat F (1 : Matrix (Fin p) (Fin p) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_zero' {p q : ℕ} : adMat F (0 : Matrix (Fin p) (Fin q) E) = 0 := Matrix.map_zero _ (map_zero _)

theorem uMat_mul_C (hF : Fr σ J C D Z J₀) (b c) : uMat σ J C D Z J₀ b c * adMat F C = adMat F C := by
  have e1 : adMat F (cT (σ : E →+* E) D * J) * adMat F C = 1 := by rw [adMat_mul', hF.dc, adMat_one']
  have e2 : adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * adMat F C = 0 := by
    rw [adMat_mul', Matrix.mul_assoc, hF.zc, Matrix.mul_zero, adMat_zero']
  have e3 : adMat F (cT (σ : E →+* E) C * J) * adMat F C = 0 := by rw [adMat_mul', hF.cc, adMat_zero']
  rw [uMat, comb_mul, e1, e2, e3]; simp

theorem uMat_mul_Z (hF : Fr σ J C D Z J₀) (b c) :
    uMat σ J C D Z J₀ b c * adMat F Z = adMat F Z + adMat F C * b := by
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have e1 : adMat F (cT (σ : E →+* E) D * J) * adMat F Z = 0 := by rw [adMat_mul', hF.dz, adMat_zero']
  have e2 : adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * adMat F Z = 1 := by
    rw [adMat_mul', Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hu, adMat_one']
  have e3 : adMat F (cT (σ : E →+* E) C * J) * adMat F Z = 0 := by rw [adMat_mul', hF.cz, adMat_zero']
  rw [uMat, comb_mul, e1, e2, e3]; simp

theorem uMat_mul_D (hF : Fr σ J C D Z J₀) (b c) :
    uMat σ J C D Z J₀ b c * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c := by
  have e1 : adMat F (cT (σ : E →+* E) D * J) * adMat F D = 0 := by rw [adMat_mul', hF.dd, adMat_zero']
  have e2 : adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * adMat F D = 0 := by
    rw [adMat_mul', Matrix.mul_assoc, hF.zd, Matrix.mul_zero, adMat_zero']
  have e3 : adMat F (cT (σ : E →+* E) C * J) * adMat F D = 1 := by rw [adMat_mul', hF.cd, adMat_one']
  rw [uMat, comb_mul, e1, e2, e3]; simp

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ} {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E}
  {J₀ : Matrix (Fin m) (Fin m) E}

theorem uMat_unitary (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E))
    (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J * uMat σ J C D Z J₀ b c = adMat F J := by
  set s := sigR (AF F) σ with hs
  set p := plus σ J₀ b with hp
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have key : cT s p * adMat F J₀ = b := by
    rw [hp, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc, adMat_mul',
      Matrix.nonsing_inv_mul _ hu, adMat_one', Matrix.mul_one]
  have key2 : adMat F J₀ * p = cT s b := by
    rw [hp, plus, ← Matrix.mul_assoc, adMat_mul', Matrix.mul_nonsing_inv _ hu, adMat_one', Matrix.one_mul]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 0 := by
    intro p q X Y h; rw [gr_adMat, h]; exact adMat_zero'
  have g1 : ∀ (X Y : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) X * J * Y = 1 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 1 := by
    intro X Y h; rw [gr_adMat, h]; exact adMat_one'
  have gzz : gr s (adMat F J) (adMat F Z) (adMat F Z) = adMat F J₀ := by rw [gr_adMat, hF.zz]
  have hcc := g0 C C hF.cc
  have hdd := g0 D D hF.dd
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have hzc := g0 Z C hF.zc
  have hzd := g0 Z D hF.zd
  have hcd := g1 C D hF.cd
  have hdc := g1 D C hF.dc
  have hsum : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    rw [adMat_mul', adMat_mul', adMat_mul', adMat_add', adMat_add', hF.sum, adMat_one']
  have := gram_comb s (adMat F J) (adMat F C) (adMat F C) (adMat F Z) (adMat F Z + adMat F C * b)
    (adMat F D) (adMat F D - adMat F Z * p + adMat F C * c) (adMat F (cT (σ : E →+* E) D * J))
    (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J))) (adMat F (cT (σ : E →+* E) C * J)) rfl
    (by simp only [gr_add_right, gr_mul_right, hcc, hcz]; simp)
    (by simp only [gr_add_right, gr_sub_right, gr_mul_right, hcc, hcz, hcd]; simp)
    (by simp only [gr_add_left, gr_mul_left, hcc, hzc]; simp)
    (by simp only [gr_add_right, gr_add_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz]; simp)
    (by
      simp only [gr_add_right, gr_add_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hzd, hcd]
      simp [key2])
    (by simp only [gr_add_left, gr_sub_left, gr_mul_left, hcc, hzc, hdc]; simp)
    (by
      simp only [gr_add_right, gr_add_left, gr_sub_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hdz, hdc]
      simp [key])
    (by
      simp only [gr_add_right, gr_add_left, gr_sub_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz,
        hdz, hdc, hcd, hdd, hzd]
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_zero, zero_add, add_zero, zero_sub,
        sub_neg_eq_add, key]
      simp only [Matrix.neg_mul, sub_neg_eq_add]
      rw [← hc]
      abel)
  rw [hsum] at this
  simpa [gr, uMat, hp, Formalism.UG.cT_one] using this

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ} {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E}
  {J₀ : Matrix (Fin m) (Fin m) E}

theorem uInv_mul (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    (adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J) * uMat σ J C D Z J₀ b c = 1 := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hF.herm.2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F J), uMat_unitary hF b c hc, adMat_mul',
    Matrix.nonsing_inv_mul _ hu, adMat_one']

def uPt (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
    (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) : GAd σ J :=
  let g : GL (Fin n) (AF F ⊗[F] E) :=
    ⟨uMat σ J C D Z J₀ b c, adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J,
      mul_eq_one_comm.mp (uInv_mul hF b c hc), uInv_mul hF b c hc⟩
  let x : HR (AF F) σ J := ⟨g, uMat_unitary hF b c hc⟩
  x

theorem uPt_mat (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    (matHom _ σ J (uPt hF b c hc)).1 = uMat σ J C D Z J₀ b c := rfl

theorem uPt_inv (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    ((matHom _ σ J (uPt hF b c hc))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 =
      adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ b c) * adMat F J := rfl

theorem uPt_crd (hF : Fr σ J C D Z J₀) (b c) (hc : c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0) :
    Crd σ J C D Z J₀ (uPt hF b c hc) b c :=
  ⟨uMat_mul_C hF b c, uMat_mul_Z hF b c, uMat_mul_D hF b c⟩

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ} {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E}
  {J₀ : Matrix (Fin m) (Fin m) E}

theorem cT_mul_plus (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) :
    cT (sigR (AF F) σ) (b * plus σ J₀ b) = b * plus σ J₀ b := by
  rw [Formalism.UG.cT_mul, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc]

theorem sigR_half : sigR (AF F) σ (inclR (F := F) (AF F) (2⁻¹ : E)) = inclR (F := F) (AF F) (2⁻¹ : E) := by
  have h : σ (2⁻¹ : E) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  simp [sigR, inclR, h]

theorem half_add_half : inclR (F := F) (AF F) (2⁻¹ : E) + inclR (F := F) (AF F) (2⁻¹ : E) = 1 := by
  rw [← map_add (f := _), show (2⁻¹ : E) + 2⁻¹ = 1 by norm_num, map_one]

theorem skew_crd (hF : Fr σ J C D Z J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (s : skewA σ j) :
    ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * plus σ J₀ b)) +
      cT (sigR (AF F) σ) ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * plus σ J₀ b)) +
      b * plus σ J₀ b = 0 := by
  have hs : (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s = 0 := mem_skewA.mp s.2
  rw [cT_sub', cT_smul', cT_mul_plus hF, sigR_half]
  have e : ∀ (S T X : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (h : AF F ⊗[F] E),
      S - h • X + (T - h • X) + X = (S + T) - (h + h) • X + X := by
    intro S T X h; rw [add_smul]; abel
  rw [e, hs, half_add_half, one_smul]; abel

end GlobalTheory.ResidueEisenstein.ChartU

namespace GlobalTheory.ResidueEisenstein.ChartU

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

theorem chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∃ φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × GlobalTheory.ResidueEisenstein.ModConj.skewA σ j → GAd σ J, Continuous φ ∧ ∀ b s, GlobalTheory.SphEis.Crd σ J C D Z J₀ (φ (b, s)) b ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * GlobalTheory.SphEis.plus σ J₀ b)) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsg : Continuous (sigR (AF F) σ) := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  have hcT : ∀ {X : Type} [TopologicalSpace X] {p q : ℕ} {f : X → Matrix (Fin p) (Fin q) (AF F ⊗[F] E)},
      Continuous f → Continuous fun x => cT (sigR (AF F) σ) (f x) := fun hf => (hf.matrix_map hsg).matrix_transpose
  let cF : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j → Matrix (Fin j) (Fin j) (AF F ⊗[F] E) := fun p =>
    (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (p.1 * plus σ J₀ p.1)
  refine ⟨fun p => uPt hF p.1 (cF p) (skew_crd hF p.1 p.2), ?_, fun b s => uPt_crd hF _ _ _⟩
  have hb : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => p.1 := continuous_fst
  have hpl : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => plus σ J₀ p.1 :=
    continuous_const.matrix_mul (hcT hb)
  have hbp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => p.1 * plus σ J₀ p.1 :=
    hb.matrix_mul hpl
  have hh : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j =>
      inclR (F := F) (AF F) (2⁻¹ : E) • (p.1 * plus σ J₀ p.1) := by
    have := hbp.const_smul (inclR (F := F) (AF F) (2⁻¹ : E)); exact this
  have hs : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j =>
      (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous cF := hs.sub hh
  have hM : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j => uMat σ J C D Z J₀ p.1 (cF p) :=
    ((continuous_const.matrix_mul continuous_const).add
      ((continuous_const.add (continuous_const.matrix_mul hb)).matrix_mul continuous_const)).add
      (((continuous_const.sub (continuous_const.matrix_mul hpl)).add (continuous_const.matrix_mul hc)).matrix_mul
        continuous_const)
  have hMi : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × skewA σ j =>
      adMat F J⁻¹ * cT (sigR (AF F) σ) (uMat σ J C D Z J₀ p.1 (cF p)) * adMat F J :=
    (continuous_const.matrix_mul (hcT hM)).matrix_mul continuous_const
  rw [(isEmbedding_matHom (AF F) σ J).continuous_iff]
  exact Units.continuous_iff.mpr ⟨hM.congr fun p => (uPt_mat hF _ _ _).symm, hMi.congr fun p => (uPt_inv hF _ _ _).symm⟩

end GlobalTheory.ResidueEisenstein.ChartU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadicalStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_chart_isotropicUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∃ φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × GlobalTheory.ResidueEisenstein.ModConj.skewA σ j → GAd σ J, Continuous φ ∧ ∀ b s, GlobalTheory.SphEis.Crd σ J C D Z J₀ (φ (b, s)) b ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * GlobalTheory.SphEis.plus σ J₀ b)) := by
  first | exact @GlobalTheory.ResidueEisenstein.ChartU.chart | exact GlobalTheory.ResidueEisenstein.ChartU.chart | (intros; apply GlobalTheory.ResidueEisenstein.ChartU.chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScale
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus

noncomputable section

namespace GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_skewA_iff {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ ∀ i k, c i k + sigR (AF F) σ (c k i) = 0 := by
  rw [mem_skewA]
  constructor
  · intro h i k
    have := congrFun (congrFun h i) k
    simpa [cT] using this
  · intro h
    ext i k
    simpa [cT] using h i k

theorem cT_apply (σ : E →ₐ[F] E) {j : ℕ} (M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) (i k : Fin j) :
    cT (sigR (AF F) σ) M i k = sigR (AF F) σ (M k i) := by
  simp [cT]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR, ← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact cA_cA σ hσ z

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  rw [← GlobalTheory.ImaginaryModulus.cA_eq_sigR]
  exact GlobalTheory.ImaginaryModulus.cA_inclR σ e

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = cA σ :=
    funext fun z => (GlobalTheory.ImaginaryModulus.cA_eq_sigR σ z).symm
  rw [this]
  exact continuous_cA σ

theorem continuous_cT (σ : E →ₐ[F] E) (j : ℕ) :
    Continuous (fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M) := by
  have hs := continuous_sigR σ
  exact continuous_pi fun i => continuous_pi fun k =>
    hs.comp ((continuous_apply i).comp (continuous_apply k))

def split (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) :
    (skewA σ j × skewA σ j) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) where
  toFun p := (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
  invFun M := (⟨inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.sub_apply, cT_apply, smul_eq_mul, map_mul, map_sub, sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2]
      ring⟩,
    ⟨inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M), by
      rw [mem_skewA_iff]
      intro i k
      simp only [Matrix.smul_apply, Matrix.add_apply, cT_apply, smul_eq_mul, map_mul, map_add (f := _), sigR_inclR,
        sigR_sigR hσ, map_inv₀ σ 2, map_ofNat σ 2, map_inv₀ σ δ, hδ, inv_neg, map_neg]
      ring⟩)
  left_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    rw [mem_skewA_iff] at hx hy
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have hx' : ∀ i k, sigR (AF F) σ (x k i) = -x i k := fun i k => eq_neg_of_add_eq_zero_right (hx i k)
    have hy' : ∀ i k, sigR (AF F) σ (y k i) = -y i k := fun i k => eq_neg_of_add_eq_zero_right (hy i k)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * ((x i k + inclR (F := F) (AF F) δ * y i k) -
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i)) = x i k
      rw [map_add (f := _), map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination x i k * hh
    · ext i k
      show inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * ((x i k + inclR (F := F) (AF F) δ * y i k) +
        sigR (AF F) σ (x k i + inclR (F := F) (AF F) δ * y k i))) = y i k
      rw [map_add (f := _), map_mul, hx', hy', sigR_inclR, hδ, map_neg]
      linear_combination (y i k * inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹) * hh + y i k * hc
  right_inv M := by
    have hh : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
      rw [show (2 : AF F ⊗[F] E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ (two_ne_zero), map_one]
    have hc : inclR (F := F) (AF F) δ * inclR (F := F) (AF F) δ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    ext i k
    show inclR (F := F) (AF F) (2⁻¹ : E) * (M i k - sigR (AF F) σ (M k i)) + inclR (F := F) (AF F) δ *
      (inclR (F := F) (AF F) (2⁻¹ : E) * (inclR (F := F) (AF F) δ⁻¹ * (M i k + sigR (AF F) σ (M k i)))) = M i k
    linear_combination M i k * hh + inclR (F := F) (AF F) (2⁻¹ : E) * (M i k + sigR (AF F) σ (M k i)) * hc
  map_add' p q := by
    show ((p.1 + q.1 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + _ • ((p.2 + q.2 : skewA σ j) : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = _
    push_cast
    rw [smul_add]
    abel
  continuous_toFun := by
    show Continuous fun p : skewA σ j × skewA σ j => (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))
    exact (continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul (inclR (F := F) (AF F) δ))
  continuous_invFun := by
    have hc := continuous_cT σ j
    have h1 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • (M - cT (sigR (AF F) σ) M) :=
      (continuous_id.sub hc).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    have h2 : Continuous fun M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        inclR (F := F) (AF F) (2⁻¹ : E) • inclR (F := F) (AF F) δ⁻¹ • (M + cT (sigR (AF F) σ) M) :=
      ((continuous_id.add hc).const_smul (inclR (F := F) (AF F) δ⁻¹)).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))
    exact (h1.subtype_mk _).prodMk (h2.subtype_mk _)

theorem split_apply (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (j : ℕ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ)
    (p : skewA σ j × skewA σ j) :
    split σ hσ j δ hδ0 hδ p = (p.1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) +
      inclR (F := F) (AF F) δ • (p.2 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := rfl

end GlobalTheory.ResidueEisenstein.ModConj.SkewSplit

namespace GlobalTheory.ResidueEisenstein.ModConj


open GlobalTheory.ResidueEisenstein.ModConj.SkewSplit in
theorem addEquivAddHaarChar_skewA_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) [LocallyCompactSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [SecondCountableTopology (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [MeasurableSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [BorelSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] (l : (AF F ⊗[F] E)ˣ) (L : GlobalTheory.ResidueEisenstein.ModConj.skewA σ j ≃ₜ+ GlobalTheory.ResidueEisenstein.ModConj.skewA σ j), (∀ s, (L s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))) → addEquivAddHaarChar L = absE F E l ^ (j * j) := by
  intro F E _ _ _ _ _ σ hcm j _ _ _ _ l L hL
  haveI : IsTotallyReal F := hcm.1
  have hσ := GlobalTheory.ImaginaryModulus.sig_sig hcm
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.ImaginaryModulus.exists_anti hcm
  obtain ⟨-, hlc, hsc, ht2⟩ := topAE F E
  haveI : LocallyCompactSpace (AF F ⊗[F] E) := hlc
  haveI : SecondCountableTopology (AF F ⊗[F] E) := hsc
  haveI : T2Space (AF F ⊗[F] E) := ht2
  haveI : LocallyCompactSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin j → Fin j → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin j → Fin j → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : T2Space (skewA σ j) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (skewA σ j × skewA σ j) := Prod.borelSpace
  set Φ := split σ hσ j δ hδ0 hδ
  set M : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) ≃ₜ+ Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    (Φ.symm.trans (GlobalTheory.ModuLR.prodCE L L)).trans Φ
  set a : (AF F ⊗[F] E)ˣ := l * GlobalTheory.Doubling.conjUnit σ l
  have ha : (a : AF F ⊗[F] E) = l * sigR (AF F) σ l := rfl
  have hM : ∀ z, M z = (a : AF F ⊗[F] E) • z := by
    intro z
    obtain ⟨p, rfl⟩ := Φ.surjective z
    show Φ (GlobalTheory.ModuLR.prodCE L L (Φ.symm (Φ p))) = (a : AF F ⊗[F] E) • Φ p
    rw [ContinuousAddEquiv.symm_apply_apply, GlobalTheory.ModuLR.prodCE_apply, split_apply, split_apply, hL, hL, ha,
      smul_add, smul_comm (inclR (F := F) (AF F) δ)]
  set g : GL (Fin j) (AF F ⊗[F] E) := Units.map (Matrix.scalar (Fin j) : (AF F ⊗[F] E) →+* _).toMonoidHom a
  have hg : Matrix.GeneralLinearGroup.det g = a ^ j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val]
    show (Matrix.scalar (Fin j) (a : AF F ⊗[F] E)).det = _
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hT : M = GlobalTheory.ModuLR.lrCE g 1 := by
    ext u i k
    rw [hM, GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.mul_one]
    show ((a : AF F ⊗[F] E) • u) i k = (Matrix.scalar (Fin j) (a : AF F ⊗[F] E) * u) i k
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have h1 : addEquivAddHaarChar M = absE F E a ^ (j * j) := by
    rw [hT, GlobalTheory.ModuLR.chi_lr F E j j g 1, hg, map_one, map_one, one_pow, mul_one, map_pow, ← pow_mul]
  have h2 : addEquivAddHaarChar M = addEquivAddHaarChar L * addEquivAddHaarChar L := by
    rw [GlobalTheory.ModuLR.addEquivAddHaarChar_transport Φ, GlobalTheory.ModuLR.addEquivAddHaarChar_prodCE]
  have h3 : absE F E a = absE F E l * absE F E l := by
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit]
  have h4 : addEquivAddHaarChar L * addEquivAddHaarChar L = absE F E l ^ (j * j) * absE F E l ^ (j * j) := by
    rw [← h2, h1, h3, mul_pow]
  exact (mul_self_inj (by positivity) (by positivity)).1 h4

end GlobalTheory.ResidueEisenstein.ModConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharSkewHermitianNormScaleStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaarChar_skewHermitian_normScale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) [LocallyCompactSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [SecondCountableTopology (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [MeasurableSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] [BorelSpace (GlobalTheory.ResidueEisenstein.ModConj.skewA σ j)] (l : (AF F ⊗[F] E)ˣ) (L : GlobalTheory.ResidueEisenstein.ModConj.skewA σ j ≃ₜ+ GlobalTheory.ResidueEisenstein.ModConj.skewA σ j), (∀ s, (L s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) = ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))) → addEquivAddHaarChar L = absE F E l ^ (j * j) := by
  first | exact @GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale | exact GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale | (intros; apply GlobalTheory.ResidueEisenstein.ModConj.addEquivAddHaarChar_skewA_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotent
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section
namespace GlobalTheory.ResidueEisenstein.ModConj


set_option maxHeartbeats 1000000 in
theorem modulus_conj_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ b, IsFlowJ σ J X Y b → ∀ ν : Measure (unipRad σ J X), ν.IsHaarMeasure → ∀ (t : ℝ) (f : GAd σ J → ℝ≥0∞), Measurable f → ∫⁻ u : unipRad σ J X, f (b t * u * (b t)⁻¹) ∂ν = ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * t))) * ∫⁻ u : unipRad σ J X, f u ∂ν := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW b hb ν hν t f hf
  classical
  obtain ⟨m, Z, J₀, hF⟩ := GlobalTheory.SphEis.exists_fr_of_isotropic F E σ h n J hJ (r + 1) X Y hW.xx hW.yy hW.xy
  obtain ⟨lv, hlv⟩ := GlobalTheory.SphEis.exists_isLv F E σ n J (r + 1) m X Y Z J₀ hF
  have hlaw := GlobalTheory.SphEis.crd_law F E σ n J (r + 1) m X Y Z J₀ hF lv hlv
  have hmem := hb.mem t
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_unit_smul_of_central_parabolicLevi F E σ n J r m X Y Z J₀ hF (b t) hmem (fun k hk => hb.comm t k hk)
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E),
      (matHom _ σ J (b t)).1 * adMat F Y = adMat F Y * γ := by
    have h1 := hmem
    simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf] at h1
    obtain ⟨B, -, e⟩ := (h1 (Fin.last r) (Finset.mem_singleton_self _)).2
    exact ⟨B.1, e⟩
  obtain ⟨δ, hδdet, hδJ, hconj⟩ := GlobalTheory.T.leviConj_scalarIdele_unipotentCoordinates F E σ n J (r + 1) m X Y Z J₀ hF (b t) l γ hl hγ
  have habs : ((absE F E l : ℝ≥0) : ℝ) ^ (r + 1) = Real.exp t := by
    obtain ⟨β, hβ, hβt⟩ := hb.onX t
    have hL : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
    have e1 : adMat F X * β.1 = (l : AF F ⊗[F] E) • adMat F X := hβ.symm.trans hl
    have hβ' : β.1 = (l : AF F ⊗[F] E) • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := by
      have e2 := congrArg (adMat F (cT (σ : E →+* E) Y * J) * ·) e1
      simp only [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_smul] at e2
      rw [e2]
    have hdet : Matrix.GeneralLinearGroup.det β = l ^ (r + 1) := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hβ', Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
        Units.val_pow_eq_pow_val]
    rw [← hβt, hdet, map_pow, NNReal.coe_pow]

  have hFD : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨eE⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AF F ⊗[F] E) := eE.secondCountableTopology
  haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  haveI : T2Space (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin (r + 1) → Fin m → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → AF F ⊗[F] E))
  letI : MeasurableSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) := ⟨rfl⟩
  have hsc : Continuous (sigR (AF F) σ) := by
    have h0 := IsModuleTopology.continuous_of_linearMap (R := AF F) (LinearMap.baseChange (AF F) σ.toLinearMap)
    refine h0.congr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [LinearMap.baseChange_tmul, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hcT : ∀ {p q : ℕ}, Continuous fun M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E) => cT (sigR (AF F) σ) M :=
    fun {p q} => (continuous_id.matrix_map hsc).matrix_transpose
  have hSk : IsClosed (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E))) :=
    isClosed_eq (continuous_id.add hcT) continuous_const
  haveI : LocallyCompactSpace (skewA σ (r + 1)) := hSk.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hff := GlobalTheory.SphEis.frame_facts F E σ n J (r + 1) m X Y Z J₀ hF
  haveI : LocallyCompactSpace (unipRad σ J X) := GlobalTheory.UAut.locallyCompact_unipRad h hJ hff.1
  haveI i1 : SecondCountableTopology (skewA σ (r + 1)) :=
    TopologicalSpace.Subtype.secondCountableTopology (skewA σ (r + 1) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)))
  have i2 : BorelSpace (skewA σ (r + 1)) := inferInstance
  have i3 : T2Space (skewA σ (r + 1)) := inferInstance
  have i4 : SecondCountableTopology (unipRad σ J X) := inferInstance
  have i5 : BorelSpace (unipRad σ J X) := inferInstance
  have i6 : T2Space (unipRad σ J X) := inferInstance

  have cTadd : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (M + N) = cT (sigR (AF F) σ) M + cT (sigR (AF F) σ) N := fun M N => Matrix.ext fun i k => by simp [cT]
  have cTsub : ∀ {p q : ℕ} (M N : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (M - N) = cT (sigR (AF F) σ) M - cT (sigR (AF F) σ) N := fun M N => Matrix.ext fun i k => by simp [cT]
  have cTsmul : ∀ {p q : ℕ} (a : AF F ⊗[F] E) (M : Matrix (Fin p) (Fin q) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) (a • M) = sigR (AF F) σ a • cT (sigR (AF F) σ) M := fun a M => Matrix.ext fun i k => by simp [cT]
  have hJ0 : cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := GlobalTheory.SphEis.UnipCrd.cT_inv_herm σ J₀ hF.herm₀
  have hpx : ∀ x y : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E),
      cT (sigR (AF F) σ) (x * GlobalTheory.SphEis.plus σ J₀ y) = y * GlobalTheory.SphEis.plus σ J₀ x := fun x y => by
    simp only [GlobalTheory.SphEis.plus, GlobalTheory.SphEis.crdLaw_cT_mul, GlobalTheory.SphEis.UnipCrd.cT_cT σ h, GlobalTheory.SphEis.UnipCrd.cT_adMat, hJ0,
      Matrix.mul_assoc]
  set hf2 : AF F ⊗[F] E := inclR (F := F) (AF F) (2⁻¹ : E) with hhf2
  have hh : hf2 + hf2 = 1 := by
    rw [hhf2, ← map_add (f := _), ← map_one (inclR (F := F) (AF F))]; congr 1; norm_num
  have hsh : sigR (AF F) σ hf2 = hf2 := by
    rw [hhf2]; simp [sigR, inclR, map_ofNat]
  have hcond : ∀ (x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (s : skewA σ (r + 1)),
      ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) +
        cT (sigR (AF F) σ) ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) +
        x * GlobalTheory.SphEis.plus σ J₀ x = 0 := fun x s => by
    have hs : (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s = 0 := s.2
    rw [cTsub, cTsmul, hsh, hpx]
    rw [show (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) +
        (cT (sigR (AF F) σ) s - hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) + x * GlobalTheory.SphEis.plus σ J₀ x =
        ((s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + cT (sigR (AF F) σ) s) +
          (1 - (hf2 + hf2)) • (x * GlobalTheory.SphEis.plus σ J₀ x) by rw [sub_smul, one_smul, add_smul]; abel, hs, hh, sub_self, zero_smul, add_zero]

  obtain ⟨φ, hφc, hφ⟩ := GlobalTheory.T.exists_continuous_chart_isotropicUnipotentRadical F E σ n J (r + 1) m X Y Z J₀ hF
  have hφmem : ∀ p, φ p ∈ unipRad σ J X := by
    rintro ⟨x, s⟩
    obtain ⟨u, hu, hcu⟩ := GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd F E σ n J (r + 1) m X Y Z J₀ hF x _ (hcond x s)
    have e := (hlaw (φ (x, s)) u x _ 0 0 (hφ x s)).2.1 hcu
    rw [e]
    exact hu
  let βc : GAd σ J → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) := fun u =>
    adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Z)
  let κc : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun u =>
    adMat F (cT (σ : E →+* E) Y * J) * ((matHom _ σ J u).1 * adMat F Y)
  have hβc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → βc u = x := fun u x c hu => by
    simp only [βc]
    rw [hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hF.dz, hF.dc]
    simp
  have hκc : ∀ u x c, GlobalTheory.SphEis.Crd σ J X Y Z J₀ u x c → κc u = c := fun u x c hu => by
    simp only [κc]
    rw [hu.onD]
    simp only [Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hF.dd, hF.dz, hF.dc]
    simp
  have hβcont : Continuous βc := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  have hκcont : Continuous κc := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  have hPcont : Continuous fun x : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) => x * GlobalTheory.SphEis.plus σ J₀ x :=
    continuous_id.matrix_mul (continuous_const.matrix_mul hcT)
  have hinvmem : ∀ u : unipRad σ J X, κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) ∈ skewA σ (r + 1) := fun u => by
    obtain ⟨x, c, hc, hcc⟩ := GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2
    rw [hβc _ _ _ hc, hκc _ _ _ hc, mem_skewA, cTadd, cTsmul, hsh, hpx]
    rw [show c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x) + (cT (sigR (AF F) σ) c + hf2 • (x * GlobalTheory.SphEis.plus σ J₀ x)) =
        (c + cT (sigR (AF F) σ) c + x * GlobalTheory.SphEis.plus σ J₀ x) + ((hf2 + hf2) - 1) • (x * GlobalTheory.SphEis.plus σ J₀ x) by rw [sub_smul, one_smul, add_smul]; abel,
      hcc, hh, sub_self, zero_smul, add_zero]
  have hinvc : Continuous fun u : unipRad σ J X => κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) :=
    (hκcont.comp continuous_subtype_val).add ((hPcont.comp (hβcont.comp continuous_subtype_val)).const_smul hf2)
  let Φ : Unit × (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) × skewA σ (r + 1)) ≃ₜ unipRad σ J X :=
    { toFun := fun p => ⟨φ p.2, hφmem p.2⟩
      invFun := fun u => ((), (βc u, ⟨κc u + hf2 • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)), hinvmem u⟩))
      left_inv := fun p => by
        obtain ⟨⟨⟩, x, s⟩ := p
        have e1 := hβc _ _ _ (hφ x s)
        have e2 := hκc _ _ _ (hφ x s)
        refine Prod.ext rfl (Prod.ext e1 (Subtype.ext ?_))
        change κc (φ (x, s)) + hf2 • (βc (φ (x, s)) * GlobalTheory.SphEis.plus σ J₀ (βc (φ (x, s)))) = s
        rw [e1, e2, sub_add_cancel]
      right_inv := fun u => by
        obtain ⟨x, c, hc, -⟩ := GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J (r + 1) m X Y Z J₀ hF u u.2
        apply Subtype.ext
        have h1 := hφ (βc u) ⟨_, hinvmem u⟩
        have e3 : ((⟨_, hinvmem u⟩ : skewA σ (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) -
            inclR (F := F) (AF F) (2⁻¹ : E) • (βc u * GlobalTheory.SphEis.plus σ J₀ (βc u)) = κc u := add_sub_cancel_right _ _
        rw [e3] at h1
        have hu' : GlobalTheory.SphEis.Crd σ J X Y Z J₀ u (βc u) (κc u) := by
          rw [hβc _ _ _ hc, hκc _ _ _ hc]; exact hc
        change φ (βc u, ⟨_, hinvmem u⟩) = u
        exact (hlaw _ u _ _ 0 0 h1).2.1 hu'
      continuous_toFun := Continuous.subtype_mk (hφc.comp continuous_snd) _
      continuous_invFun := continuous_const.prodMk ((hβcont.comp continuous_subtype_val).prodMk
        (hinvc.subtype_mk hinvmem)) }

  have hplusc : Continuous (GlobalTheory.SphEis.plus σ J₀ : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → _) :=
    continuous_const.matrix_mul hcT

  have hT : ∀ q' : unipRad σ J X, ∃ (l' : Unit) (f₁ : Unit → Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E))
      (g₁ : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) → skewA σ (r + 1)), Continuous f₁ ∧ Continuous g₁ ∧
      ∀ l a c, Φ (l, a, c) * q' = Φ (l * l', a + f₁ l, c + g₁ (l, a)) := by
    intro q'
    obtain ⟨⟨⟨⟩, x', s'⟩, rfl⟩ := Φ.surjective q'
    have hgmem : ∀ a : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E),
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x') ∈ skewA σ (r + 1) := fun a => by
      rw [mem_skewA, cTsmul, hsh, cTsub, hpx, hpx, ← smul_add]
      simp
    have hgc : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ p.2 - p.2 * GlobalTheory.SphEis.plus σ J₀ x') :=
      ((continuous_const.matrix_mul (hplusc.comp continuous_snd)).sub (continuous_snd.matrix_mul continuous_const)).const_smul hf2
    have hgc' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        (⟨_, hgmem p.2⟩ : skewA σ (r + 1)) := hgc.subtype_mk _
    have hgc'' : Continuous fun p : Unit × Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) =>
        s' + (⟨_, hgmem p.2⟩ : skewA σ (r + 1)) := continuous_const.add hgc'
    refine ⟨(), fun _ => x', fun p => s' + ⟨_, hgmem p.2⟩, continuous_const, hgc'', fun l a c => ?_⟩
    obtain ⟨⟩ := l
    apply Subtype.ext
    change φ (a, c) * φ (x', s') = φ (a + x', c + (s' + ⟨_, hgmem a⟩))
    have h1 := (hlaw _ _ a _ x' _ (hφ a c)).1 (hφ x' s')
    have h2 := hφ (a + x') (c + (s' + ⟨_, hgmem a⟩))
    simp only [← hhf2] at h1 h2
    have hQ : a * GlobalTheory.SphEis.plus σ J₀ x' = hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x') + hf2 • (a * GlobalTheory.SphEis.plus σ J₀ x') := by
      rw [← add_smul, hh, one_smul]
    have hLR : ((c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (a * GlobalTheory.SphEis.plus σ J₀ a)) +
        ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) - hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ x')) - a * GlobalTheory.SphEis.plus σ J₀ x' =
        (((c + (s' + ⟨_, hgmem a⟩) : skewA σ (r + 1))) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) -
          hf2 • ((a + x') * GlobalTheory.SphEis.plus σ J₀ (a + x')) := by
      rw [show (((c + (s' + ⟨_, hgmem a⟩) : skewA σ (r + 1))) : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) =
      (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) + ((s' : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) +
        hf2 • (x' * GlobalTheory.SphEis.plus σ J₀ a - a * GlobalTheory.SphEis.plus σ J₀ x')) from rfl]
      rw [GlobalTheory.SphEis.crdLaw_plus_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      conv_lhs => rw [hQ]
      simp only [smul_add, smul_sub]
      abel
    rw [← hLR] at h2
    exact (hlaw _ _ _ _ 0 0 h1).2.1 h2

  have hconjmem : ∀ u ∈ unipRad σ J X, b t * u * (b t)⁻¹ ∈ unipRad σ J X :=
    (GlobalTheory.ResidueEisenstein.frame_levi_facts F E σ n J r X Y h hJ hW).1 (b t) hmem
  let α : unipRad σ J X →* unipRad σ J X :=
    { toFun := fun u => ⟨b t * u * (b t)⁻¹, hconjmem u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  have hαc : Continuous α :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

  let lI : GL (Fin (r + 1)) (AF F ⊗[F] E) :=
    Units.map (Matrix.scalar (Fin (r + 1)) : AF F ⊗[F] E →+* Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)).toMonoidHom l
  have hlI : (lI : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) = (l : AF F ⊗[F] E) • 1 := by
    simp [lI, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hdetlI : Matrix.GeneralLinearGroup.det lI = l ^ (r + 1) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hlI, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      Units.val_pow_eq_pow_val]
  let sA : Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) →+ Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E) :=
    (GlobalTheory.ModuLR.lrCE lI δ).toAddEquiv.toAddMonoidHom
  have hsA : ∀ a, sA a = (l : AF F ⊗[F] E) • (a * δ.1) := fun a => by
    change lI.1 * a * δ.1 = _
    rw [hlI, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  let u2 : (AF F ⊗[F] E)ˣ := l * Units.map (sigR (AF F) σ).toMonoidHom l
  have hu2 : (u2 : AF F ⊗[F] E) = (l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E) := rfl
  have hsu2 : sigR (AF F) σ (u2 : AF F ⊗[F] E) = u2 := by
    rw [hu2, map_mul, GlobalTheory.SphEis.UnipCrd.sigR_invol σ h, mul_comm]
  have hsu2' : sigR (AF F) σ ((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (u2⁻¹ : (AF F ⊗[F] E)ˣ) := by
    refine Units.eq_inv_of_mul_eq_one_left ?_
    conv_lhs => rw [← hsu2]
    rw [← map_mul, Units.mul_inv, map_one]
  have hsk : ∀ a : AF F ⊗[F] E, sigR (AF F) σ a = a → ∀ s ∈ skewA σ (r + 1), a • s ∈ skewA σ (r + 1) := fun a ha s hs => by
    rw [mem_skewA, cTsmul, ha, ← smul_add, (mem_skewA.1 hs), smul_zero]
  let Lc : skewA σ (r + 1) ≃ₜ+ skewA σ (r + 1) :=
    { toFun := fun s => ⟨(u2 : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)), hsk _ hsu2 _ s.2⟩
      invFun := fun s => ⟨((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        hsk _ hsu2' _ s.2⟩
      left_inv := fun s => Subtype.ext (by simp [smul_smul])
      right_inv := fun s => Subtype.ext (by simp [smul_smul])
      map_add' := fun s s' => Subtype.ext (by simp [smul_add])
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.const_smul (u2 : AF F ⊗[F] E)) _
      continuous_invFun := Continuous.subtype_mk
        (continuous_subtype_val.const_smul (((u2⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E))) _ }
  let sC : skewA σ (r + 1) →+ skewA σ (r + 1) := Lc.toAddEquiv.toAddMonoidHom
  have hsC : ∀ s, (sC s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) =
      ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (s : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)) :=
    fun s => rfl
  have hδJ' : ∀ M : Matrix (Fin m) (Fin (r + 1)) (AF F ⊗[F] E),
      δ.1 * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) δ.1 * M)) = adMat F J₀⁻¹ * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hδJ]
  have hαΦ : ∀ (l' : Unit) a c, α (Φ (l', a, c)) = Φ (l', sA a, sC c) := by
    intro l' a c
    obtain ⟨⟩ := l'
    apply Subtype.ext
    change b t * φ (a, c) * (b t)⁻¹ = φ (sA a, sC c)
    have h1 := hconj _ _ _ (hφ a c)
    have h2 := hφ (sA a) (sC c)
    simp only [← hhf2] at h1 h2
    have e3 : sA a * GlobalTheory.SphEis.plus σ J₀ (sA a) =
        ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • (a * GlobalTheory.SphEis.plus σ J₀ a) := by
      rw [hsA]
      simp only [GlobalTheory.SphEis.plus, cTsmul, GlobalTheory.SphEis.crdLaw_cT_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_assoc, hδJ']
      rw [mul_comm (sigR (AF F) σ (l : AF F ⊗[F] E))]
    rw [e3, hsC] at h2
    rw [← hsA] at h1
    rw [smul_sub, smul_comm ((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) hf2] at h1
    exact (hlaw _ _ _ _ 0 0 h1).2.1 h2

  set kA : ℝ≥0 := (absE F E l ^ ((r + 1) * m))⁻¹ with hkA
  set kC : ℝ≥0 := (absE F E l ^ ((r + 1) * (r + 1)))⁻¹ with hkC
  have hl0 : absE F E l ≠ 0 := fun h0 => by
    have e := map_mul (absE F E) l l⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at e
    exact zero_ne_one e.symm
  have hsA' : ∀ ν' : Measure (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)), ν'.IsAddHaarMeasure → ν'.map sA = kA • ν' := by
    intro ν' hν'
    have e := addEquivAddHaarChar_smul_map ν' (GlobalTheory.ModuLR.lrCE lI δ)
    rw [GlobalTheory.T.addHaarChar_leftRight_matrixMul_adeleTensor F E σ h (r + 1) m lI δ, hdetlI, hδdet, one_pow, mul_one, map_pow, ← pow_mul] at e
    change ν'.map (GlobalTheory.ModuLR.lrCE lI δ) = kA • ν'
    conv_rhs => rw [← e]
    rw [smul_smul, hkA, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  have hsC' : ∀ ν' : Measure (skewA σ (r + 1)), ν'.IsAddHaarMeasure → ν'.map sC = kC • ν' := by
    intro ν' hν'
    have e := addEquivAddHaarChar_smul_map ν' Lc
    rw [GlobalTheory.T.addHaarChar_skewHermitian_normScale F E σ h (r + 1) l Lc (fun s => rfl)] at e
    change ν'.map Lc = kC • ν'
    conv_rhs => rw [← e]
    rw [smul_smul, hkC, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  have hmap := GlobalTheory.ModulusCoord.map_haar_eq_smul_of_coords (unipRad σ J X) Unit
    (Matrix (Fin (r + 1)) (Fin m) (AF F ⊗[F] E)) (skewA σ (r + 1)) Φ hT α sA sC kA kC hαc
    (GlobalTheory.ModuLR.lrCE lI δ).continuous Lc.continuous hαΦ hsA' hsC' ν hν
  have hfm : Measurable fun u : unipRad σ J X => f u := hf.comp measurable_subtype_coe
  have hk : ((kA * kC : ℝ≥0) : ℝ) = Real.exp (-(((n : ℝ) - (r + 1)) * t)) := by
    have hn : (n : ℝ) = m + 2 * (r + 1) := by exact_mod_cast hF.dim.symm
    rw [hkA, hkC, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_pow, pow_mul, pow_mul, habs, hn,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc ∫⁻ u, f (b t * u * (b t)⁻¹) ∂ν = ∫⁻ u, (fun v : unipRad σ J X => f v) (α u) ∂ν := rfl
    _ = ∫⁻ v, f v ∂(ν.map α) := (lintegral_map hfm hαc.measurable).symm
    _ = ∫⁻ v, f v ∂((kA * kC) • ν) := by rw [hmap]
    _ = ((kA * kC : ℝ≥0) : ℝ≥0∞) * ∫⁻ v, f v ∂ν := by rw [lintegral_smul_measure]; rfl
    _ = _ := by rw [← hk, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.ResidueEisenstein.ModConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotentStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviCentreFlow_conj_scales_haar_isotropicUnipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ b, IsFlowJ σ J X Y b → ∀ ν : Measure (unipRad σ J X), ν.IsHaarMeasure → ∀ (t : ℝ) (f : GAd σ J → ℝ≥0∞), Measurable f → ∫⁻ u : unipRad σ J X, f (b t * u * (b t)⁻¹) ∂ν = ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * t))) * ∫⁻ u : unipRad σ J X, f u ∂ν := by
  first | exact @GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow | exact GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow | (intros; apply GlobalTheory.ResidueEisenstein.ModConj.modulus_conj_flow <;> assumption)
end
