module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviElem

open Matrix

section Abstract

variable {R : Type} [CommRing R]

def cols2 {n : ℕ} (x y : Fin n → R) : Matrix (Fin n) (Fin 2) R := Matrix.of fun i k => ![x i, y i] k

theorem conj_eq {n κ : Type} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ] (s : R →+* R)
    (P : Matrix n κ R) (Q : Matrix κ n R) (hPQ : P * Q = 1) (J : Matrix n n R) (D : Matrix κ κ R)
    (hK : Dᵀ * (Pᵀ * J * P.map s) * D.map s = Pᵀ * J * P.map s) :
    (P * D * Q)ᵀ * J * (P * D * Q).map s = J := by
  have h1 : (P * D * Q)ᵀ * J * (P * D * Q).map s = Qᵀ * (Dᵀ * (Pᵀ * J * P.map s) * D.map s) * Q.map s := by
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [h1, hK]
  have h2 : Qᵀ * (Pᵀ * J * P.map s) * Q.map s = (P * Q)ᵀ * J * (P * Q).map s := by
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [h2, hPQ]
  simp

def swap2 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

def blk {b : ℕ} (g : Matrix (Fin b) (Fin b) R) (t u : R) : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) R :=
  fromBlocks g 0 0 (diagonal ![t, u])

theorem levi_mat {b : ℕ} (s : R →+* R) (hs : ∀ z, s (s z) = z) (ι : Matrix (Fin (b + 2)) (Fin b) R)
    (x y : Fin (b + 2) → R) (J : Matrix (Fin (b + 2)) (Fin (b + 2)) R) (J₁ : Matrix (Fin b) (Fin b) R)
    (Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) R) (hQP : Q * fromCols ι (cols2 x y) = 1)
    (hK : (fromCols ι (cols2 x y))ᵀ * J * (fromCols ι (cols2 x y)).map s = fromBlocks J₁ 0 0 swap2)
    (l : Rˣ) (G : GL (Fin b) R) (hG : (G : Matrix (Fin b) (Fin b) R)ᵀ * J₁ * (G : Matrix (Fin b) (Fin b) R).map s = J₁) :
    ∃ m : GL (Fin (b + 2)) R, (m : Matrix _ _ R)ᵀ * J * (m : Matrix _ _ R).map s = J ∧
      (m : Matrix _ _ R) *ᵥ x = l.1 • x ∧ (m : Matrix _ _ R) *ᵥ y = s (l⁻¹).1 • y ∧
      (m : Matrix _ _ R) * ι = ι * (G : Matrix (Fin b) (Fin b) R) := by
  set P := fromCols ι (cols2 x y) with hP
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  set D := blk (G : Matrix (Fin b) (Fin b) R) l.1 (s (l⁻¹).1)
  set D' := blk ((G⁻¹ : GL (Fin b) R) : Matrix (Fin b) (Fin b) R) (l⁻¹).1 (s l.1)
  have hDD : D * D' = 1 := by
    simp only [D, D', blk, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      diagonal_mul_diagonal]
    rw [← fromBlocks_one]
    congr 1
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal, ← map_mul]
  have hDD' : D' * D = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hDD
  refine ⟨⟨P * D * Q, P * D' * Q, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · calc P * D * Q * (P * D' * Q) = P * D * (Q * P) * D' * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P, hDD, Matrix.mul_one, hPQ]
  · calc P * D' * Q * (P * D * Q) = P * D' * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P, hDD', Matrix.mul_one, hPQ]
  · refine conj_eq s P Q hPQ J D ?_
    rw [hK]
    simp only [D, blk, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.map_zero _ (map_zero s), diagonal_map (map_zero s),
      diagonal_transpose, hG]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap2, diagonal, Matrix.mul_apply, Fin.sum_univ_two, hs, ← map_mul]
  all_goals simp only [Units.val_mk]
  · have hx : P *ᵥ Pi.single (Sum.inr 0) 1 = x := by
      rw [mulVec_single_one]; ext i; simp [P, cols2, Matrix.col]
    have hDx : D *ᵥ Pi.single (Sum.inr 0) 1 = l.1 • Pi.single (Sum.inr 0) 1 := by
      rw [mulVec_single_one]; ext (i | i)
      · simp [D, blk, Matrix.col]
      · fin_cases i <;> simp [D, blk, diagonal, Matrix.col]
    rw [← hx, mulVec_mulVec, show P * D * Q * P = P * D by rw [Matrix.mul_assoc, hQP, Matrix.mul_one],
      ← mulVec_mulVec, hDx, mulVec_smul]
  · have hy : P *ᵥ Pi.single (Sum.inr 1) 1 = y := by
      rw [mulVec_single_one]; ext i; simp [P, cols2, Matrix.col]
    have hDy : D *ᵥ Pi.single (Sum.inr 1) 1 = s (l⁻¹).1 • Pi.single (Sum.inr 1) 1 := by
      rw [mulVec_single_one]; ext (i | i)
      · simp [D, blk, Matrix.col]
      · fin_cases i <;> simp [D, blk, diagonal, Matrix.col]
    rw [← hy, mulVec_mulVec, show P * D * Q * P = P * D by rw [Matrix.mul_assoc, hQP, Matrix.mul_one],
      ← mulVec_mulVec, hDy, mulVec_smul]
  · set E1 := fromRows (1 : Matrix (Fin b) (Fin b) R) (0 : Matrix (Fin 2) (Fin b) R) with hE1
    have hι : P * E1 = ι := by
      simp [P, E1, fromCols_mul_fromRows]
    have hDι : D * E1 = E1 * (G : Matrix (Fin b) (Fin b) R) := by
      rw [hE1, fromRows_mul]
      ext (i | i) j <;> simp [D, blk, Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
    have h3 : P * D * Q * (P * E1) = P * D * E1 := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (P * D), hQP, Matrix.mul_one]
    have fin : P * D * Q * ι = ι * (G : Matrix (Fin b) (Fin b) R) := by
      rw [← hι, h3, Matrix.mul_assoc, hDι, ← Matrix.mul_assoc]
    exact fin

end Abstract

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_gram {n : ℕ} {p q : Type} [Fintype p] [Fintype q] (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) p E) (B : Matrix (Fin n) q E) (j : p) (k : q) :
    (Aᵀ * J * B.map σ) j k = form σ J (fun i => A i j) (fun i => B i k) := by
  simp only [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_flip (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (herm : ∀ i j, σ (J j i) = J i j) (v w : Fin n → E) : form σ J v w = σ (form σ J w v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [herm]
  ring

theorem det_ne_of_sig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  set Dg : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fromBlocks 1 0 0 (-1)
  have hD : Dg * Dg = 1 := by simp [Dg, fromBlocks_multiply, fromBlocks_one]
  have h1 : Dg * Aᵀ * M * A.map star = 1 := by
    have : Dg * Aᵀ * M * A.map star = Dg * (Aᵀ * M * A.map star) := by simp only [Matrix.mul_assoc]
    rw [this, hA, hD]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv.trans (finCongr hrs))).1 h1
  exact Matrix.det_ne_zero_of_left_inverse (B := A.map star * Dg * Aᵀ) (by simpa [Matrix.mul_assoc] using h2)

theorem gram_block (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {b : ℕ} {Y : Spc F E (b + 2)}
    {Y₁ : Spc F E b} (herm : ∀ i j, σ (Y.J j i) = Y.J i j) {H : Plane E (b + 2) b} {i₀ i₁ : ℕ}
    (hA : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    (fromCols H.ι (cols2 H.x H.y))ᵀ * Y.J * (fromCols H.ι (cols2 H.x H.y)).map σ = fromBlocks Y₁.J 0 0 swap2 := by
  have hmap : (fromCols H.ι (cols2 H.x H.y)).map σ = fromCols (H.ι.map σ) ((cols2 H.x H.y).map σ) := by
    ext i (j | j) <;> rfl
  have ho : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by rw [mulVec_single_one]; rfl
  have orth' : ∀ j, form σ Y.J (fun i => H.ι i j) H.x = 0 ∧ form σ Y.J (fun i => H.ι i j) H.y = 0 := fun j => by
    rw [ho]; exact hA.orth _
  rw [hmap, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, hA.gram]
  congr 1
  · ext j k
    rw [form_gram, ho]
    fin_cases k
    · simpa [cols2] using (hA.orth (Pi.single j 1)).1
    · simpa [cols2] using (hA.orth (Pi.single j 1)).2
  · ext k j
    rw [form_gram, form_flip σ hσ herm]
    fin_cases k
    · simp [cols2, (orth' j).1]
    · simp [cols2, (orth' j).2]
  · ext k k'
    rw [form_gram]
    fin_cases k <;> fin_cases k' <;>
      simp [cols2, swap2, hA.xx, hA.yy, hA.xy, form_flip σ hσ herm H.y H.x]

theorem cA_invol {σ : E →ₐ[F] E} (hσ : ∀ z, σ (σ z) = z) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add u v hu hv => simp [map_add (f := _), hu, hv]

theorem levi_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∃ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, ∀ l g₀, IsLevi H l g₀ (m l g₀) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hK' : (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)))ᵀ * incM F G.V.J *
      (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))).map (cA σ).toRingHom =
      fromBlocks (incM F G₁.V.J) 0 0 swap2 := by
    rw [← hPf]
    have h1 : (P.map f).map (cA σ).toRingHom = (P.map σ).map f := by
      ext i j; simp [hcf]
    have h2 : incM F G.V.J = G.V.J.map f := rfl
    rw [h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, hKdef, fromBlocks_map]
    congr 1
    · simp
    · simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]
  have key : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J), ∃ m : GL (Fin (b + 2)) (AE F E),
      (m : Matrix _ _ (AE F E))ᵀ * incM F G.V.J * (m : Matrix _ _ (AE F E)).map (cA σ).toRingHom = incM F G.V.J ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.x = l.1 • incV F H.x ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.y = (cA σ).toRingHom (l⁻¹).1 • incV F H.y ∧
      (m : Matrix _ _ (AE F E)) * incM F H.ι = incM F H.ι * (g₀.1 : Matrix (Fin b) (Fin b) (AE F E)) :=
    fun l g₀ => levi_mat (cA σ).toRingHom (cA_invol hσ) (incM F H.ι) (incV F H.x) (incV F H.y) (incM F G.V.J)
      (incM F G₁.V.J) (Q.map f) hQP' hK' l g₀.1 g₀.2
  choose m hm using key
  exact ⟨fun l g₀ => ⟨m l g₀, (hm l g₀).1⟩, fun l g₀ => ⟨(hm l g₀).2.1, (hm l g₀).2.2.1, (hm l g₀).2.2.2⟩⟩

end Field

end GlobalTheory.LeviElem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPow
noncomputable section

open NumberField MeasureTheory
open scoped Classical ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem vacuum_smul_realA : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
    ∀ g ∈ GinfC X.A, X.om (g, 1) X.vac = (∏ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det ^ P.n τ) • X.vac := by
  intro D cc δ t0 Q P X hX hb g hg
  have hW := hX.2.weil
  have hθ := hX.2.inf
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  have cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V hV τ => by
    have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [this]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hmt1 : Formalism.L2.Theta.mt X.B 1 = 1 := by simp [Formalism.L2.Theta.mt]
  have hc1 : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B 1) = 1 := fun τ => by
    rw [hmt1, compAt, Matrix.map_one _ (by simp) (by simp)]
  have hA0 : ∀ τ, (gramAt D X.A τ).det ≠ 0 := fun τ => by
    rw [gramAt, hX.1.gramA, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]; exact one_ne_zero
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.A hA0 g hg
  have hy : IsDetRoot X.B 1 1 := by simp [IsDetRoot]
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1)
    (cart X.A hX.1.gramA) (cart X.B hX.1.gramB) g hg 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
    (fun τ => by rw [one_mul, mul_one]) x 1 hx hy X.vac hX.2.vac_theta hX.2.vac_fock]
  congr 1
  let c : D.what₂.Tau → ℤ := fun τ => -((P.n τ : ℤ) + P.d)
  have hν : ∀ τ, HasInfExp D (X.χB * (η ^ X.B.rank)⁻¹) τ ((c τ : ℤ) : ℚ) := by
    intro τ
    have := GlobalTheory.VacuumCharacter.hasInfExp_twist (hb τ) (e2 τ) X.B.rank
    convert this using 1
    rw [X.rkB]
    simp only [c]
    push_cast
    ring
  rw [Circle.coe_mul, Circle.coe_inv, hxv _ c hν, map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := X.A.rank) (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)
    (by simp)
  obtain ⟨d1, -⟩ := hd (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)) (compAt X.θ τ (Formalism.L2.Theta.mt X.B 1))
    (by rw [one_mul, mul_one])
  have hpd : p = P.d := by
    have : (p : ℂ) = X.B.rank := by
      rw [Matrix.trace_one, Fintype.card_fin] at hp
      linear_combination -hp / 2
    exact_mod_cast this.trans (congrArg (Nat.cast) X.rkB)
  have e1' : ((1 / 2 : ℂ) • (1 + 1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ) * 1 + (1 / 2 : ℂ) • (1 - 1)) = 1 := by
    rw [mul_one]; module
  have inv : (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * (compAt X.θ τ (Formalism.L2.Theta.mt X.A g⁻¹)).det = 1 := by
    rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [d1, hc1, e1', Matrix.det_one, one_pow, one_mul, hpd, eq_inv_of_mul_eq_one_right inv]
  simp only [c]
  rw [zpow_neg, inv_inv, zpow_add₀ g0, zpow_natCast, zpow_natCast, inv_pow]
  field_simp

end GlobalTheory.NormDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPowStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pair_real_points_smul_adelic_vacuum_det_pow : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
    ∀ g ∈ GinfC X.A, X.om (g, 1) X.vac = (∏ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det ^ P.n τ) • X.vac := by
  first | exact @GlobalTheory.NormDict.vacuum_smul_realA | exact GlobalTheory.NormDict.vacuum_smul_realA | (intros; apply GlobalTheory.NormDict.vacuum_smul_realA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionInverseTransposeMaximalMinorProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionInverseTransposeMaximalMinorProduct
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem substF_invT_minor_det {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} (X : Data P)
    (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ) (τ : D.what₂.Tau) (s : Fin P.a → Fin P.d) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det) =
      MvPolynomial.C ((G τ)⁻¹.det) * MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det := by
  set M := Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)
  set φ := GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
  set H : Matrix (Fin P.a) (Fin P.a) (MvPolynomial (FVar D X.B.rank X.A.rank) ℂ) :=
    Matrix.of fun i'' i' => MvPolynomial.C ((G τ)⁻¹ (Fin.cast X.rkA.symm i') (Fin.cast X.rkA.symm i''))
  have hH : H.det = MvPolynomial.C ((G τ)⁻¹.det) := by
    have e1 : H = (MvPolynomial.C : ℂ →+* MvPolynomial (FVar D X.B.rank X.A.rank) ℂ).mapMatrix
        (((G τ)⁻¹.transpose).submatrix (finCongr X.rkA.symm) (finCongr X.rkA.symm)) := by
      ext i j; simp [H]
    rw [e1, ← RingHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
  have hM : ((φ.comp (MvPolynomial.rename X.var)).mapMatrix M) = (MvPolynomial.rename X.var).mapMatrix M * H := by
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, M, H, Matrix.of_apply, AlgHom.comp_apply,
      MvPolynomial.rename_X, φ, GlobalTheory.CompactHowe.substF_X, Data.var]
    rw [Finset.sum_eq_single (Fin.cast X.rkB.symm (s i))]
    · simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
      exact Fintype.sum_equiv (finCongr X.rkA) _ _ (fun l => by simp [mul_comm])
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  have := AlgHom.map_det (φ.comp (MvPolynomial.rename X.var)) M
  rw [AlgHom.comp_apply] at this
  rw [this, hM, Matrix.det_mul, hH, ← AlgHom.map_det, mul_comm]

end GlobalTheory.NormDict

namespace GlobalTheory.NormDict

theorem substF_invT_minorPol : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P)
    (T : Tup D P.a P.d P.n) (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ),
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (minorPol D T)) =
      (∏ τ, ((G τ)⁻¹.det) ^ P.n τ) • MvPolynomial.rename X.var (minorPol D T) := by
  intro D cc δ t0 Q P X T G
  rw [minorPol, map_prod, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  simp only [substF_invT_minor_det, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

end GlobalTheory.NormDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionInverseTransposeMaximalMinorProductStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substitution_inverse_transpose_maximalMinorProduct : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P)
    (T : Tup D P.a P.d P.n) (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ),
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (minorPol D T)) =
      (∏ τ, ((G τ)⁻¹.det) ^ P.n τ) • MvPolynomial.rename X.var (minorPol D T) := by
  first | exact @GlobalTheory.NormDict.substF_invT_minorPol | exact GlobalTheory.NormDict.substF_invT_minorPol | (intros; apply GlobalTheory.NormDict.substF_invT_minorPol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinors
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem om_real_fock_eq : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
  ∀ g ∈ GinfC X.A, ∀ T, X.om (g, 1) (X.fock T) = X.fock T := by
  intro D cc δ t0 Q P X hX hB g hg T
  set G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.A g) with hG
  have hmt : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B (1 : GA D X.B)) = 1 := fun τ => by
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one]
  have hmove := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * G τ) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 * 1) g 1
    (fun τ => by simp) (fun τ => by simp) (fun τ => by simp [hG]) (fun τ => by rw [hmt])
    X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))).2
  have hsub := GlobalTheory.FockBaseChange.pureTensorO_subst D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) G
    (fun _ => 1) (fun _ => 1) X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  have hdet : ∀ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * ((G τ)⁻¹).det = 1 := fun τ => by
    have e := GlobalTheory.WeilVacMove.compAt_mt_mul_inv X.θ τ X.A g
    have hu : IsUnit (G τ) := IsUnit.of_mul_eq_one _ e
    rw [← Matrix.det_mul]
    rw [show compAt X.θ τ (Formalism.L2.Theta.mt X.A g) = G τ from rfl,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.det_one]
  change X.om (g, 1) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))) = pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))
  rw [hmove, GlobalTheory.T.norm_pair_real_points_smul_adelic_vacuum_det_pow P X hX hB g hg, GlobalTheory.FiniteFock.pureTensorO_smul, hsub, GlobalTheory.T.substitution_inverse_transpose_maximalMinorProduct P X T G, map_smul, smul_smul,
    ← Finset.prod_mul_distrib]
  simp only [← mul_pow, hdet, one_pow, Finset.prod_const_one, one_smul]

end GlobalTheory.NormDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRealFixesFockMaximalMinorsStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_real_fixes_fock_maximal_minors : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
  ∀ g ∈ GinfC X.A, ∀ T, X.om (g, 1) (X.fock T) = X.fock T := by
  first | exact @GlobalTheory.NormDict.om_real_fock_eq | exact GlobalTheory.NormDict.om_real_fock_eq | (intros; apply GlobalTheory.NormDict.om_real_fock_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResRdApply
noncomputable section
namespace GlobalTheory.FlatPair
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def resRd {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) :
    Rul Xo c →+* (↥(U.X k).dom → ℂ) where
  toFun f := fun y => rdU U f k y.1
  map_one' := by
    funext y
    haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, y.2, dif_pos, Pi.one_apply]
    exact congrArg toC (evalAt_one _ _ (U.un k ⟨y.1, y.2⟩) (hT _ _))
  map_mul' f g := by
    funext y
    exact congrFun (congrFun (AllWt.rdU_mul U f g) k) y.1
  map_zero' := by
    funext y
    simp
  map_add' f g := by
    funext y
    simp

theorem resRd_apply {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) (f : Rul Xo c)
    (y : ↥(U.X k).dom) : resRd U hT k f y = rdU U f k y.1 := rfl

theorem resRd_smul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) (a : c.F) (f : Rul Xo c) :
    resRd U hT k (a • f) = σ a • resRd U hT k f := by
  funext y
  simp [resRd_apply, map_smulₛₗ]

def holAlg (X : Data E r) : Subalgebra ℂ (↥X.dom → ℂ) where
  carrier := {g | ∃ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom ∧ ∀ y, g y = F y.1}
  mul_mem' := by
    rintro g g' ⟨F, hF, hg⟩ ⟨F', hF', hg'⟩
    exact ⟨F * F', hF.mul hF', fun y => by simp [hg, hg']⟩
  add_mem' := by
    rintro g g' ⟨F, hF, hg⟩ ⟨F', hF', hg'⟩
    exact ⟨F + F', hF.add hF', fun y => by simp [hg, hg']⟩
  algebraMap_mem' a := ⟨fun _ => a, differentiableOn_const a, fun y => rfl⟩

end GlobalTheory.FlatPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutside
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem beta_unrAt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (beta G i j) w := by
  intro D T L sc G μ₀ hL i j w hw
  have hi := i.2
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := by omega
  have hχ : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hw)
  have hη : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) L.eta w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  have hp : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (L.eta ^ n) w := fun n x hx =>
    (map_pow Circle.toUnits _ n).trans
      (show GlobalTheory.LFun.locChar (F := D.host.F) (E := D.host.E) L.eta w x ^ n = 1 by rw [hη x hx, one_pow])
  exact hχ.mul (hp _)

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaUnramifiedOutsideStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_unramified_outside : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (beta G i j) w := by
  first | exact @GlobalTheory.FunObj.beta_unrAt_off | exact GlobalTheory.FunObj.beta_unrAt_off | (intros; apply GlobalTheory.FunObj.beta_unrAt_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRational
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.BCT.LocVal

theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (x : E) :
    cj w (algebraMap E (w.adicCompletion E) x) = algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := by
  have key : ∀ u : Pl E, u = w → ∀ f : u.adicCompletion E →+* w.adicCompletion E, Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ k : E, s (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k) := by
    intro u hu f hf hk
    subst hu
    exact ⟨f, hf, hk⟩
  have hex := key _ ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).2 hw) (GlobalTheory.CuspRep.conjLoc ((IsCMField.complexConj E).toRingEquiv) w)
    (GlobalTheory.CuspRep.conjLoc_spec _ w).1 (GlobalTheory.CuspRep.conjLoc_spec _ w).2.1
  unfold cj
  rw [dite_eq_left hex]
  exact hex.choose_spec.2 x

theorem map_mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) (w : Pl E) :
    Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val * 1 * (γ : GL (Fin n) E).val = 1 :=
      γ.2
    change cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) * 1 *
      (algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val = 1
    have e : cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) =
        (algebraMap E (w.adicCompletion E)).mapMatrix
          (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val) := by
      ext i j
      simp [cT, Matrix.map_apply, cj_algebraMap w hw]
    rw [e, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT _ _), hγ, map_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  intro E _ _ _ _ n γ w
  unfold locPt toSub
  rw [dite_eq_left (map_mem_UL γ w)]

end GlobalTheory.BCT.LocVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRationalStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalPoint_eq_map_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E), ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  first | exact @GlobalTheory.BCT.LocVal.main | exact GlobalTheory.BCT.LocVal.main | (intros; apply GlobalTheory.BCT.LocVal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutside
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem alpha_unrAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) → GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j) w := by
  intro D T L sc G μ₀ hL t i j w hS hQ
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hS (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : (L.xiH t).UnrAt w := by
    by_contra hc
    rcases (hL.Q_ram t _).1 hc with h | ⟨P, h, hc'⟩
    · exact hQ _ h rfl
    · exact hQ P h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have h1 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 hmu
  have h2 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 hxi
  have h3 := (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  have h4 : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (L.eta ^ n) w := fun n => by
    induction n with
    | zero => rw [pow_zero]; exact fun _ _ => Units.ext rfl
    | succ n ih => rw [pow_succ]; exact ih.mul h3
  exact (h1.mul h2).mul (h4 _)

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutsideStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_unramified_outside : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) → GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j) w := by
  first | exact @GlobalTheory.FunObj.alpha_unrAt | exact GlobalTheory.FunObj.alpha_unrAt | (intros; apply GlobalTheory.FunObj.alpha_unrAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleScalarSecondSlotConjStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingSmulRightConj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.ActRight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (s : 𝓞 E) : H.bar (H.bar s) = s := by
  apply Subtype.ext
  show ((H.bar (H.bar s) : 𝓞 E) : E) = (s : E)
  rw [H.bar_eq, H.bar_eq]
  simp

theorem weilEq_act_adj (H : Host E) (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ)
    (A : PAT H (Sp (𝓞 K))) (a : 𝓞 E) :
    WeilEq A.t.PP.L (A.t.act.act (H.bar a)) (𝟙 _) A.t.PP.L (𝟙 _) (A.t.act.act a)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have key := (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hl (𝓞 K) A.pol A.pol A.pol A.pol
    (A.t.act.act (H.bar a)) (𝟙 _) (𝟙 _) (A.t.act.act a) (A.t.act.hom _) inferInstance inferInstance
    (A.t.act.hom a) ℂ (σ₁.comp (algebraMap (𝓞 K) K))).1
  apply key
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  have h := A.t.adj (H.bar a)
  rwa [bar_bar] at h

theorem weilEq_act_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g →
    ∀ r s : 𝓞 E,
    WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (A.t.act.act s ≫ g) A.t.PP.L (A.t.act.act (r * H.bar s)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g _ _ r s h n x y c hn hx hy
  haveI := A.t.act.hom s
  haveI := A.t.act.hom r
  have hy' : (y ≫ A.t.act.act s) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx' : (x ≫ A.t.act.act r) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h1 := h n x (y ≫ A.t.act.act s) c hn hx hy'
  have h2 := weilEq_act_adj H K σ₁ A s n (x ≫ A.t.act.act r) y c hn hx' hy
  rw [← Category.assoc, h1, A.t.act.mul, ← Category.assoc, h2]
  simp only [Category.comp_id]

end GlobalTheory.CM.ActRight
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g →
    ∀ r s : 𝓞 E,
    WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (A.t.act.act s ≫ g) A.t.PP.L (A.t.act.act (r * H.bar s)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  first | exact @GlobalTheory.CM.ActRight.weilEq_act_right | exact GlobalTheory.CM.ActRight.weilEq_act_right | (intros; apply GlobalTheory.CM.ActRight.weilEq_act_right <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLattice
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CommPhase

theorem kap_add (D : D7) (T : Tor D) {N N' : ℕ} (x y z : VC D N N') :
    Formalism.MainNotions.TaylorLogMetric.kap D T x (y + z) = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Formalism.MainNotions.TaylorLogMetric.kap D T x z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.kap, GlobalTheory.NormSum.VacMove.hf_add_right, Complex.add_im, Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem kap_eq_one_of_int (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (m : ℤ)
    (h : (Hf D T x y).im = m) : Formalism.MainNotions.TaylorLogMetric.kap D T x y = 1 := by
  rw [Formalism.MainNotions.TaylorLogMetric.kap, h]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (((m : ℝ)) : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem chars : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  intro D δ hc 𝔪 a d x hx
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d)
  have hint : ∀ y ∈ La0 D (tor0 D ⊤ δ) a d, ∃ m : ℤ, (Hf D (tor0 D ⊤ δ) x y).im = m :=
    (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc a d _ k0).2.2.1 x hx
  set Lp := La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)
  set S := (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf Lp
  have hwd : ∀ u v : Lp, (QuotientAddGroup.leftRel S) u v →
      Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d) := by
    intro u v huv
    rw [QuotientAddGroup.leftRel_apply] at huv
    have hm : ((-u + v : Lp) : VC D a d) ∈ La0 D (tor0 D ⊤ δ) a d := AddSubgroup.mem_addSubgroupOf.mp huv
    obtain ⟨m, hm⟩ := hint _ hm
    have h1 := kap_eq_one_of_int D (tor0 D ⊤ δ) x _ m hm
    have hv : (v : VC D a d) = (u : VC D a d) + ((-u + v : Lp) : VC D a d) := by
      push_cast; abel
    rw [hv, kap_add, h1, mul_one]
  let χ : AddChar (Lp ⧸ S) ℂ :=
    { toFun := fun q => Quotient.liftOn' q (fun y : Lp => Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d)) hwd
      map_zero_eq_one' := by
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((0 : Lp) : VC D a d) = 1
        exact kap_eq_one_of_int D (tor0 D ⊤ δ) x _ 0 (by simp [Hf])
      map_add_eq_mul' := by
        intro q r
        induction q using QuotientAddGroup.induction_on
        induction r using QuotientAddGroup.induction_on
        rename_i u v
        show Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((u + v : Lp) : VC D a d) =
          Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (u : VC D a d) * Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (v : VC D a d)
        push_cast
        exact kap_add _ _ _ _ _ }
  exact ⟨χ, fun y => rfl⟩

end GlobalTheory.CommPhase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAddCharThetaCommutatorPhaseSkewLatticeStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addChar_thetaCommutatorPhase_skewLattice : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}, ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), ∃ χ : AddChar ((La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) ℂ, ∀ y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), χ (y : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) = Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x (y : VC D a d) := by
  first | exact @GlobalTheory.CommPhase.chars | exact GlobalTheory.CommPhase.chars | (intros; apply GlobalTheory.CommPhase.chars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

theorem smooth_of_relSnc :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X)
      (σ : ∀ i, (L i).Sec), RelSnc f d L σ → SmoothOfRelativeDimension d f := by
  intro R _ X f d s L σ h
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose C hC using h.chart
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) (fun x => (C x).U) ?_
    fun x => ?_
  · rw [← top_le_iff]
    rintro x -
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hC x⟩
  · exact GlobalTheory.ChartSmooth.smooth_of_etale f (C x).affine (C x).t (C x).etale

end GlobalTheory.LogPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → SmoothOfRelativeDimension d f := by
  first | exact @GlobalTheory.LogPair.smooth_of_relSnc | exact GlobalTheory.LogPair.smooth_of_relSnc | (intros; apply GlobalTheory.LogPair.smooth_of_relSnc <;> assumption)
end
end
