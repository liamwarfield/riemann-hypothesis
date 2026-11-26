module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockEmb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqId
namespace GlobalTheory.SquareDistanceExpansion

open Matrix

theorem expand {R : Type} [CommRing R] {n : ℕ} (X Y X' Y' : Matrix (Fin n) (Fin n) R) :
    (1 + X + Y) * (1 + X' + Y') = 1 + X + Y + X' + Y' + X * X' + X * Y' + Y * X' + Y * Y' := by
  noncomm_ring

theorem sq_id {R : Type} [CommRing R] {d : ℕ} (H H' : Matrix (Fin d) (Fin d) R) :
    H * H' - 1 = (H - 1) + (H' - 1) + (H - 1) * (H' - 1) := by
  noncomm_ring

theorem prod_eq {R : Type} [CommRing R] {n d : ℕ} (a c : Matrix (Fin n) (Fin d) R)
    (α γ : Matrix (Fin d) (Fin n) R) (M N : Matrix (Fin d) (Fin d) R) :
    a * M * α * (c * N * γ) = a * M * (α * c) * N * γ := by
  simp only [Matrix.mul_assoc]

theorem dist {R : Type} [CommRing R] {n d : ℕ} (a : Matrix (Fin n) (Fin d) R)
    (α : Matrix (Fin d) (Fin n) R) (A B : Matrix (Fin d) (Fin d) R) :
    a * (A + B + A * B) * α = a * A * α + a * B * α + a * A * B * α := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem main : (let d1 : {R : Type} → [CommRing R] → {n d : ℕ} → Matrix (Fin n) (Fin d) R → Matrix (Fin n) (Fin d) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin d) R → Matrix (Fin d) (Fin d) R → Matrix (Fin n) (Fin n) R := @(fun {R : Type} [CommRing R] {n d : ℕ} (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) ↦ (1 : Matrix (Fin n) (Fin n) R) + a * (H - (1 : Matrix (Fin d) (Fin d) R)) * α + b * (K - (1 : Matrix (Fin d) (Fin d) R)) * β); ∀ {R : Type} [inst : CommRing R] {n d : ℕ} {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}, α * a = (1 : Matrix (Fin d) (Fin d) R) → β * b = (1 : Matrix (Fin d) (Fin d) R) → α * b = (0 : Matrix (Fin d) (Fin d) R) → β * a = (0 : Matrix (Fin d) (Fin d) R) → ∀ (H K H' K' : Matrix (Fin d) (Fin d) R), d1 a b α β H K * d1 a b α β H' K' = d1 a b α β (H * H') (K * K')) := by
  dsimp only
  intro R _ n d a b α β hαa hβb hαb hβa H K H' K'
  have e1 := prod_eq a a α α (H - 1) (H' - 1)
  have e2 := prod_eq a b α β (H - 1) (K' - 1)
  have e3 := prod_eq b a β α (K - 1) (H' - 1)
  have e4 := prod_eq b b β β (K - 1) (K' - 1)
  rw [hαa, Matrix.mul_one] at e1
  rw [hαb, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e2
  rw [hβa, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e3
  rw [hβb, Matrix.mul_one] at e4
  rw [expand, e1, e2, e3, e4, sq_id H H', sq_id K K', dist a α (H - 1) (H' - 1),
    dist b β (K - 1) (K' - 1)]
  abel

end GlobalTheory.SquareDistanceExpansion
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct
open Matrix
open Formalism.UG (cT)

namespace GlobalTheory.BlockFormsEmb

section Alg
variable {R : Type} [CommRing R] {n d : ℕ}

theorem cT_add' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A + B) = cT s A + cT s B :=
  Matrix.ext fun i j => by simp [cT]

theorem cT_sub' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A - B) = cT s A - cT s B :=
  Matrix.ext fun i j => by simp [cT]

def blk (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) R := 1 + a * (H - 1) * α + b * (K - 1) * β

variable {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}

theorem blk_one : blk a b α β 1 1 = 1 := by simp [blk]

theorem blk_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (H K H' K' : Matrix (Fin d) (Fin d) R) :
    blk a b α β H K * blk a b α β H' K' = blk a b α β (H * H') (K * K') := by
  first
  | exact @_root_.GlobalTheory.SquareDistanceExpansion.main
  | exact _root_.GlobalTheory.SquareDistanceExpansion.main
  | (apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareDistanceExpansion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareDistanceExpansion.main ..)

theorem blk_unitary (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R)
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT s α = Jm * b) (hβ : cT s β = Jm * a) (ha : cT s a * Jm = β) (hb : cT s b * Jm = α)
    (H K : Matrix (Fin d) (Fin d) R) (h1 : cT s K * H = 1) (h2 : cT s H * K = 1) :
    cT s (blk a b α β H K) * Jm * blk a b α β H K = Jm := by
  have key : cT s (blk a b α β H K) * Jm = Jm * blk a b α β (cT s K) (cT s H) := by
    unfold blk
    rw [cT_add', cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_sub', cT_sub',
      Formalism.UG.cT_one, hα, hβ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, ha, hb]
    abel
  rw [key, Matrix.mul_assoc, blk_mul hαa hβb hαb hβa, h1, h2, blk_one, Matrix.mul_one]

end Alg

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.BlockForms

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [sigR, inclR]

theorem cT_adMat (σ : E →ₐ[F] E) {m p : Type} (Z : Matrix m p E) :
    cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
  Matrix.ext fun i j => by simp only [cT, adMat, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]; rfl

theorem adMat_mul' {m p q : Type} [Fintype p] (A : Matrix m p E) (B : Matrix p q E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {m : Type} [Fintype m] [DecidableEq m] : adMat F (1 : Matrix m m E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_zero' {m p : Type} : adMat F (0 : Matrix m p E) = 0 := Matrix.map_zero _ (map_zero _)

theorem sigR_sigR' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem blkCols_gram {n r l d : ℕ} (h : l + d ≤ r) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (Z W : Matrix (Fin n) (Fin r) E) :
    cT (σ : E →+* E) (blkCols h Z) * J * blkCols h W =
      (cT (σ : E →+* E) Z * J * W).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
        (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := by
  first
  | rfl
  | (ext i j; simp [Matrix.mul_apply, blkCols, cT])

def embMat (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
    (a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E))
    (g : GlobalTheory.CuspRep.GA E d) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  blk a b α β (g.1.map Φ.symm) (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm))

variable (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
  {a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)} {α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E)}

theorem map_symm_mul (A B : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)) :
    (A * B).map Φ.symm = A.map Φ.symm * B.map Φ.symm := Matrix.map_mul (f := Φ.symm.toRingHom)

theorem map_symm_one : (1 : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)).map Φ.symm = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem embMat_one : embMat σ Φ a b α β 1 = 1 := by
  simp only [embMat, inv_one, Units.val_one, map_symm_one, Formalism.UG.cT_one, blk_one]

theorem embMat_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (g g' : GlobalTheory.CuspRep.GA E d) : embMat σ Φ a b α β (g * g') = embMat σ Φ a b α β g * embMat σ Φ a b α β g' := by
  unfold embMat
  rw [blk_mul hαa hβb hαb hβa, Units.val_mul, _root_.mul_inv_rev, Units.val_mul, map_symm_mul, map_symm_mul, Formalism.UG.cT_mul]

theorem embMat_unitary (hσ : ∀ x, σ (σ x) = x) (Jm : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT (sigR (AF F) σ) α = Jm * b) (hβ : cT (sigR (AF F) σ) β = Jm * a)
    (ha : cT (sigR (AF F) σ) a * Jm = β) (hb : cT (sigR (AF F) σ) b * Jm = α) (g : GlobalTheory.CuspRep.GA E d) :
    cT (sigR (AF F) σ) (embMat σ Φ a b α β g) * Jm * embMat σ Φ a b α β g = Jm := by
  have hcc : ∀ A : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), cT (sigR (AF F) σ) (cT (sigR (AF F) σ) A) = A :=
    fun A => Matrix.ext fun i j => by simp only [cT, Matrix.transpose_apply, Matrix.map_apply]; exact sigR_sigR' σ hσ _
  have hgg : (g⁻¹).1.map Φ.symm * g.1.map Φ.symm = 1 := by
    rw [← map_symm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_symm_one]
  unfold embMat
  refine blk_unitary _ Jm hαa hβb hαb hβa hα hβ ha hb _ _ ?_ ?_
  · rw [hcc, hgg]
  · rw [← Formalism.UG.cT_mul, hgg, Formalism.UG.cT_one]

end Main

theorem exists_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (l d : ℕ) (h : l + d ≤ r), ∃ ι : GlobalTheory.CuspRep.GA E d →* GAd σ J, GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW l d h
  obtain ⟨Φ, j, hc1, hc2, hj, hΦ⟩ := GlobalTheory.HeckeBridge.exists_tensor_adele_equiv F E σ hcm
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJT : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : ∀ {m p : Type} (Z : Matrix m p E), cT (σ : E →+* E) (cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun _ _ => hσ _
  have hyx : cT (σ : E →+* E) Yf * J * Xf = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcc, hJT, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have he : Function.Injective (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := fun i k e =>
    Fin.ext (by have := congrArg Fin.val e; simp only at this; omega)
  have q1 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Xf = 1 := by
    rw [blkCols_gram, hyx, Matrix.submatrix_one _ he]
  have q2 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Yf = 1 := by
    rw [blkCols_gram, hW.xy, Matrix.submatrix_one _ he]
  have q3 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Yf = 0 := by
    rw [blkCols_gram, hW.yy, Matrix.submatrix_zero]; rfl
  have q4 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Xf = 0 := by
    rw [blkCols_gram, hW.xx, Matrix.submatrix_zero]; rfl
  have hαa : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Xf) = 1 := by
    rw [← adMat_mul', q1, adMat_one']
  have hβb : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Yf) = 1 := by
    rw [← adMat_mul', q2, adMat_one']
  have hαb : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Yf) = 0 := by
    rw [← adMat_mul', q3, adMat_zero']
  have hβa : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Xf) = 0 := by
    rw [← adMat_mul', q4, adMat_zero']
  have hα : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) = adMat F J * adMat F (blkCols h Yf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have hβ : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J)) = adMat F J * adMat F (blkCols h Xf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have ha : cT (sigR (AF F) σ) (adMat F (blkCols h Xf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  have hb : cT (sigR (AF F) σ) (adMat F (blkCols h Yf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  let M := embMat σ Φ (adMat F (blkCols h Xf)) (adMat F (blkCols h Yf))
    (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J))
  have hMmul : ∀ g g', M (g * g') = M g * M g' := embMat_mul σ Φ hαa hβb hαb hβa
  have hMone : M 1 = 1 := embMat_one σ Φ
  have hMu : ∀ g, cT (sigR (AF F) σ) (M g) * JR (AF F) J * M g = JR (AF F) J :=
    embMat_unitary σ Φ hσ (adMat F J) hαa hβb hαb hβa hα hβ ha hb
  let U : GlobalTheory.CuspRep.GA E d → GL (Fin n) (AF F ⊗[F] E) := fun g =>
    ⟨M g, M g⁻¹, by rw [← hMmul, mul_inv_cancel, hMone], by rw [← hMmul, inv_mul_cancel, hMone]⟩
  let ι : GlobalTheory.CuspRep.GA E d →* GAd σ J :=
    { toFun := fun g => (⟨U g, hMu g⟩ : HR (AF F) σ J)
      map_one' := Subtype.ext (Units.ext hMone)
      map_mul' := fun g g' => Subtype.ext (Units.ext (hMmul g g')) }
  exact ⟨ι, Φ, j, hc1, hc2, hj, hΦ, fun g => rfl⟩

end GlobalTheory.BlockFormsEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationGauss
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

section Complex

end Complex

section Adelic

open scoped Classical
open GlobalTheory.RealLift.KLineProof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rho [IsTotallyReal F] (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ (fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) ⟨w, IsTotallyReal.isReal w⟩).comp (AlgHom.fst ℝ _ _)

theorem trace_rho [IsTotallyReal F] (v : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) v = ∑ w, rho w v := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}),
    Finset.sum_empty, add_zero]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w) _ _ fun w => ?_
  rw [Algebra.trace_self_apply]
  rfl

theorem rho_evI [IsTotallyReal F] (w : InfinitePlace F) (a : AF F) :
    ((rho w (evI F a) : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  rfl

theorem piInf_algebraMap [IsTotallyReal F] {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = ((rho w (evI F a) : ℝ) : ℂ) := by
  rw [rho_evI]
  change piInf τ (a ⊗ₜ[F] (1 : E)) = _
  rw [piInf_tmul, map_one, mul_one]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  change piInf τ ((1 : AF F) ⊗ₜ[F] e) = _
  rw [piInf_tmul, map_one, map_one, one_mul]

theorem rho_trace [IsTotallyReal F] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : rho w (evI F (Algebra.trace (AF F) (AE F E) z)) = 2 * (piInf τ z).re := by
  have h1 : z + cA σ z = algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) :=
    GlobalTheory.GaussMean.OneVec.add_sigR (AF F) hCM z
  have h2 := congrArg (fun y => (piInf τ y).re) h1
  simp only [map_add (f := _), piInf_cA hCM, piInf_algebraMap, Complex.ofReal_re, Complex.add_re] at h2
  rw [← h2]
  simp [two_mul]

end Adelic

end GlobalTheory.ThK.EvAt0.PlaneQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfin
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatPt

open GlobalTheory.BCT.TrKer GlobalTheory.BCT.FinPart

theorem coord_pInf_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (e : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) e)) = v.embedding e := by
  have hv : (InfinitePlace.mk v.embedding) = v := InfinitePlace.mk_embedding v
  have h : (InfinitePlace.mk v.embedding).embedding = v.embedding := by rw [hv]
  simp only [coord, h, if_true, Pi.evalRingHom_apply]
  rw [pInf_algebraMap, hv]

theorem ratGL_mem_UA {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) :
    ratGL E n γ.1 ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  change cT (conjAd E) (ratGL E n γ.1).val * 1 * (ratGL E n γ.1).val = 1
  have hc : cT (conjAd E) (ratGL E n γ.1).val =
      (algebraMap E (Ad E)).mapMatrix (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val) := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact conjAd_algebraMap _
  have hr : (ratGL E n γ.1).val = (algebraMap E (Ad E)).mapMatrix γ.1.val := rfl
  rw [hc, hr, mul_one, ← map_mul, ← map_one (algebraMap E (Ad E)).mapMatrix, ← hγ, mul_one]

theorem ratPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  intro E _ _ _ n γ
  refine ⟨⟨ratGL E n γ.1, ratGL_mem_UA γ⟩, ⟨γ.1, rfl⟩, ?_, ?_⟩
  · set r : UA E n := ⟨ratGL E n γ.1, ratGL_mem_UA γ⟩
    have hpr : GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = ratF E n γ.1 := by
      apply Units.ext
      ext i j
      rfl
    have hi : (finPt γ).1⁻¹ * r ∈ infU E n := by
      rw [infU, MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_mul, map_inv, map_inv]
      change (pU (finPt γ))⁻¹ * GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = 1
      rw [pU_finPt, hpr, inv_mul_cancel]
    have he : r = (finPt γ).1 * (⟨_, hi⟩ : infU E n).1 := by
      simp only [mul_inv_cancel_left]
    rw [he, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (algebraMap E (Ad E) (γ.1.val i j))) = v.embedding (γ.1.val i j)
    exact coord_pInf_algebraMap v _

end GlobalTheory.BCT.RatPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfinStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  exact @GlobalTheory.BCT.RatPt.ratPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvd
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemOrth

theorem idemAt_orth {D : D7} {a b : AE D} {i j : Formalism.L2.DIV.Pl D.host.E} {n : ℕ} (ha : Formalism.L2.NTheta.IsIdemAt a i)
    (hb : Formalism.L2.NTheta.IsIdemAt b j) (hi : ((n : ℕ) : 𝓞 D.host.E) ∈ i.asIdeal)
    (hj : ((n : ℕ) : 𝓞 D.host.E) ∉ j.asIdeal) : (a + cA D a) * (b + cA D b) = 0 := by
  obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, a4⟩ := ha
  obtain ⟨⟨b1, b2, v', ε', hε', b3⟩, b4⟩ := hb
  by_cases hv : v = v'
  · exfalso
    rw [← hv] at hε'
    have hab : a + cA D a = b + cA D b := a3.trans (GlobalTheory.PlaceDatum.placeIdem_eq hε hε' ▸ b3.symm)
    have hn : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hj (h ▸ zero_mem _)
    have h1 := not_not.1 (mt (b4 _ hn).2 hj)
    have h2 := GlobalTheory.MovedIdem.finPart_conj_mem h1
    have hs : star ((((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹) = (((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_natCast (R := D.host.E) n
    rw [hs] at h2
    have h3 := not_not.1 (mt (a4 1 one_ne_zero).2 ((Ideal.ne_top_iff_one _).1 i.isPrime.ne_top))
    have h4 : incA D (((1 : 𝓞 D.host.E) : D.host.E)⁻¹) = 1 := by
      rw [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one]
    rw [h4, mul_one] at h3
    have h5 := GlobalTheory.SplitLatBasis.mul_mem_intAE D h3 (add_mem h1 h2)
    rw [← RingHom.map_add (f := _), ← RingHom.map_mul, ← add_mul, ← mul_assoc, ← hab, mul_add, a1, a2, add_zero] at h5
    exact (a4 _ hn).1 hi h5
  · rw [a3, b3, ← RingHom.map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε hε' hv, RingHom.map_zero]

theorem sum_orth {R ι : Type} [CommRing R] (c : R →+* R) (p q : ι → R) (s t : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ t, (p i + c (p i)) * (q j + c (q j)) = 0) :
    (∑ i ∈ s, p i + c (∑ i ∈ s, p i)) * (∑ j ∈ t, q j + c (∑ j ∈ t, q j)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h i hi j hj

theorem idemSum_orth : ∀ (D : D7) (e e' : AE D) (P P' : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ), IsIdemSum e P → IsIdemSum e' P' → (∀ PP ∈ P, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ P', ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (e + cA D e) * (e' + cA D e') = 0 := by
  rintro D e e' P P' n ⟨⟨es, hes, rfl⟩, -⟩ ⟨⟨fs, hfs, rfl⟩, -⟩ hP hP'
  exact sum_orth (R := AE D) (cA D) es fs P P' fun i hi j hj =>
    idemAt_orth (hes i hi) (hfs j hj) (hP i hi) (hP' j hj)

end GlobalTheory.IdemOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvdStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_conjSum_orthogonal_dvd : ∀ (D : D7) (e e' : AE D) (P P' : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ), IsIdemSum e P → IsIdemSum e' P' → (∀ PP ∈ P, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ P', ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (e + cA D e) * (e' + cA D e') = 0 := by
  first | exact @GlobalTheory.IdemOrth.idemSum_orth | exact GlobalTheory.IdemOrth.idemSum_orth | (intros; apply GlobalTheory.IdemOrth.idemSum_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.PsiInfLinear

theorem continuous_ringEquiv_mixedSpace_symm (E : Type) [Field E] [NumberField E] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem psiInf_eq_exp_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F,
      psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  intro D ψ h
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := h
  have hform := hall θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
  let c : ℂ := 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℂ :=
    { toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  have hg : Continuous g := by
    show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[D.host.F] (1 : D.host.E))
    refine continuous_const.mul (continuous_finsetSum _ fun ρ _ => ?_)
    exact (hθ ρ).2.comp (continuous_ringEquiv_mixedSpace_symm D.host.F)
  refine ⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩
  rw [hform x]
  congr 1
  show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[D.host.F] (1 : D.host.E))
  rw [e.symm_apply_apply]

end GlobalTheory.PsiInfLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanStandardChar_eq_exp_realLinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ Λ : mixedEmbedding.mixedSpace D.host.F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing D.host.F, psiInf D.host.F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x)) := by
  first | exact @GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | exact GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear | (intros; apply GlobalTheory.PsiInfLinear.psiInf_eq_exp_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.RowOneCell

def sz (u v : ℕ) (i j : Bool) : ℕ := cond i (cond j v 1) (cond j u 0)

def sigTwo (b : Bool → ℕ) (x y : ℕ) (h0 : b false = x) (h1 : b true = y) :
    (Σ j, Fin (b j)) ≃ Σ j, Two (Fin x) (Fin y) j :=
  Equiv.sigmaCongrRight fun j => match j with
    | false => finCongr h0
    | true => finCongr h1

def rowPart (u v : ℕ) : ∀ i, (Σ j, Fin (sz u v i j)) ≃ Two (Fin u) (Fin (v + 1)) i
  | false => (sigTwo (sz u v false) 0 u rfl rfl).trans (two (stdSum (Nat.zero_add u)))
  | true => (sigTwo (sz u v true) 1 v rfl rfl).trans (two (stdSum (Nat.add_comm 1 v)))

def colPart (u v : ℕ) : ∀ j, (Σ i, Fin (sz u v i j)) ≃ Two (Fin 1) (Fin (u + v)) j
  | false => (sigTwo (fun i => sz u v i false) 0 1 rfl rfl).trans (two (stdSum (Nat.zero_add 1)))
  | true => (sigTwo (fun i => sz u v i true) u v rfl rfl).trans (two (stdSum rfl))

theorem eq_sz {u v : ℕ} (b : Bool → Bool → ℕ)
    (hb : (∀ i, ∑ j, b i j = Fintype.card (Two (Fin u) (Fin (v + 1)) i)) ∧
      ∀ j, ∑ i, b i j = Fintype.card (Two (Fin 1) (Fin (u + v)) j)) (h : b true false = 1) :
    b = sz u v := by
  have r0 := hb.1 false
  have r1 := hb.1 true
  have c0 := hb.2 false
  have c1 := hb.2 true
  simp only [Fintype.sum_bool] at r0 r1 c0 c1
  have e0 : Fintype.card (Two (Fin u) (Fin (v + 1)) false) = u := Fintype.card_fin u
  have e1 : Fintype.card (Two (Fin u) (Fin (v + 1)) true) = v + 1 := Fintype.card_fin _
  have e2 : Fintype.card (Two (Fin 1) (Fin (u + v)) false) = 1 := Fintype.card_fin _
  have e3 : Fintype.card (Two (Fin 1) (Fin (u + v)) true) = u + v := Fintype.card_fin _
  rw [e0] at r0
  rw [e1] at r1
  rw [e2] at c0
  rw [e3] at c1
  funext i j
  cases i <;> cases j <;> simp only [sz, cond_true, cond_false] <;> omega

def extTensorEquiv {G H V W V' W' : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ H W} {ρ' : Representation ℂ G V'}
    {σ' : Representation ℂ H W'} (φ : ρ.Equiv ρ') (ψ : σ.Equiv σ') :
    (extTensor ρ σ).Equiv (extTensor ρ' σ') :=
  .mk (TensorProduct.congr φ.toLinearEquiv ψ.toLinearEquiv) fun g => by
    ext v w
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b) (φ.toIntertwiningMap.isIntertwining _ _ g.1 v)
      (ψ.toIntertwiningMap.isIntertwining _ _ g.2 w)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def colChar (v : ℕ) (χ₂ : kˣ →* ℂˣ) (j : Bool) : kˣ →* ℂˣ :=
  χ₂ * absPow k (cond j (1 / 2) (-(v : ℂ) / 2))

def colRep (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (j : Bool) :
    Representation ℂ (Levi k fun i => Fin (sz u v i j)) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin (sz u v false j)) χ₁) (detRep (Fin (sz u v true j)) (colChar v χ₂ j))).comp
    ((Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) false).prod
      (Pi.evalMonoidHom (fun i => GL (Fin (sz u v i j)) k) true))

theorem isSmooth_colRep {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) (u v : ℕ) (j : Bool) :
    IsSmooth (colRep χ₁ χ₂ u v j) := by
  refine isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
    ((isSmooth_ofChar_iff _).2 (h₂.mul (GlobalTheory.LocGL.isSmoothChar_absPow _)).detChar)) _ ?_
  exact (continuous_apply false).prodMk (continuous_apply true)

end GlobalTheory.SmGL.RowOneCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdeles
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

open scoped Nat

namespace GlobalTheory.AlgIntIdem

theorem natCast_dvd_pow_sub {E : Type} [Field E] [NumberField E] (x : 𝓞 E) (N t : ℕ)
    (hN : 0 < N) (ht : 0 < t) :
    (N : 𝓞 E) ∣ x ^ ((N ^ Module.finrank ℤ (𝓞 E))! * t) - x ^ (N ^ Module.finrank ℤ (𝓞 E))! := by
  set I : Ideal (𝓞 E) := Ideal.span {(N : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    simp only [I, ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ I) = N ^ Module.finrank ℤ (𝓞 E) := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      Ideal.absNorm_span_natCast]
  have h := GlobalTheory.IdealIdele.pow_factorial_mul (Ideal.Quotient.mk I x) t ht
  rw [hcard, ← map_pow, ← map_pow, Ideal.Quotient.eq] at h
  exact Ideal.mem_span_singleton.1 h

theorem idem : ∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w := by
  intro D x
  set d := Module.finrank ℤ (𝓞 D.host.E)
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  have hx : inc D (x : D.host.E) ∈ OhE D := VacMove.inc_int D x
  have key : ∀ N t : ℕ, 0 < N → 0 < t → ∃ w ∈ OhE D,
      inc D (x : D.host.E) ^ ((N ^ d)! * t) = inc D (x : D.host.E) ^ (N ^ d)! + (N : AE D) * w := by
    intro N t hN ht
    obtain ⟨w, hw, h⟩ := VacMove.inc_dvd D (natCast_dvd_pow_sub x N t hN ht)
    refine ⟨w, hw, ?_⟩
    rw [← h]
    push_cast
    rw [map_sub, map_pow, map_pow]
    ring
  obtain ⟨e, he, h⟩ := hcpl (fun N => inc D (x : D.host.E) ^ (N ^ d)!) (fun N => pow_mem hx _) (by
    intro N m hN hm
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial
      (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right N hm) d)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨w, hw, hh⟩ := key N t hN ht0
    exact ⟨w, hw, by simp only [ht, hh]⟩)
  refine ⟨e, he, ?_, fun N hN => ⟨(N ^ d)!, Nat.factorial_pos _, h N hN⟩⟩
  rw [← sub_eq_zero]
  refine hsep _ fun N hN => ?_
  obtain ⟨w, hw, hh⟩ := h N hN
  obtain ⟨c, hc, hc'⟩ := key N 2 hN two_pos
  refine ⟨c + (2 * inc D (x : D.host.E) ^ (N ^ d)! * w + N * w * w - w), ?_, ?_⟩
  · exact add_mem hc (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (pow_mem hx _)) hw)
      (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
  · rw [pow_mul] at hc'
    rw [hh]; linear_combination hc'

end GlobalTheory.AlgIntIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLimitPowersIntegralAdelesStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_limit_powers_integralAdeles : ∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w := by
  first | exact @GlobalTheory.AlgIntIdem.idem | exact GlobalTheory.AlgIntIdem.idem | (intros; apply GlobalTheory.AlgIntIdem.idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkData
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

noncomputable section

namespace GlobalTheory.Nef

theorem exists_stalk_fac {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X)
    (h : f (IsLocalRing.closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem exists_stalk_map {X Y : Scheme.{0}} (x : X) (g : X ⟶ Y) (y : Y) (hy : g x = y) :
    ∃ φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x, Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ g := by
  subst hy
  exact exists_stalk_fac (g x) (X.fromSpecStalk x ≫ g) (congrArg (fun z => g z) Scheme.fromSpecStalk_closedPoint)

theorem stalk_hom_eq {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} (φ ψ : X.presheaf.stalk x ⟶ R)
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map ψ ≫ X.fromSpecStalk x) : φ = ψ :=
  Spec.map_injective ((cancel_mono (X.fromSpecStalk x)).1 h)

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem unitSec_sqr : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h2 : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id, ← Hom.mul_def, ← h1, _root_.one_mul]
  change η[G].left ≫ (𝟙 G * 𝟙 G : G ⟶ G).left = η[G].left
  rw [← Over.comp_left, h2]

theorem sqr_hom : sqr G ≫ G.hom = G.hom := Over.w _

end

theorem stalkData_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m,
    StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  intro S G _ s
  obtain ⟨π, hπ⟩ := exists_stalk_map (unitSec G s) G.hom s (by
    rw [← Scheme.Hom.comp_apply, sec_hom]; rfl)
  obtain ⟨ε, hε⟩ := exists_stalk_map s (unitSec G) (unitSec G s) rfl
  obtain ⟨m, hm⟩ := exists_stalk_map (unitSec G s) (sqr G) (unitSec G s) (by
    rw [← Scheme.Hom.comp_apply, unitSec_sqr])
  refine ⟨π.hom, ε.hom, m.hom, ⟨hπ, hε, hm⟩, ?_, ?_, ?_⟩
  · have : π ≫ ε = 𝟙 _ := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hε, Category.assoc, sec_hom,
        Category.comp_id, Spec.map_id, Category.id_comp])
    exact congrArg CommRingCat.Hom.hom this
  · have : π ≫ m = π := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hm, Category.assoc, sqr_hom])
    exact congrArg CommRingCat.Hom.hom this
  · have : m ≫ ε = ε := stalk_hom_eq (unitSec G s) _ _ (by
      rw [Spec.map_comp, Category.assoc, hm, ← Category.assoc, hε, Category.assoc, unitSec_sqr])
    exact congrArg CommRingCat.Hom.hom this

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeUnitStalkDataStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupSchemeUnitStalkData : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m, StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  first | exact @GlobalTheory.Nef.stalkData_exists | exact GlobalTheory.Nef.stalkData_exists | (intros; apply GlobalTheory.Nef.stalkData_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOpBOfMemClosure
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeBij

open GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_one' {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

theorem spAct_mul' {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

def HasOpB (ψ : AddChar (AF F) ℂ) (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    Function.Surjective ei ∧ (∀ Φ ∈ schA F κ, e Φ ∈ schA F κ) ∧
    (∀ w, ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (spAct G w) (e Φ)) ∧
    (∀ v, (SB _).map (ev v) = SB _) ∧ (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0) ∧
    (∀ v w, ∀ φ ∈ SB (κ → Fv F v),
      ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (spAct G w) (ev v φ)) ∧
    (∀ᶠ v in cofinite, ev v (indO v) = indO v) ∧
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = indO v) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) ∧
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ))

theorem hasOpB_one (ψ : AddChar (AF F) ℂ) : HasOpB (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one'], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one'],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl, ?_⟩
  simpa using Set.bijOn_id (schA F κ : Set ((κ → AF F) → ℂ))

theorem hasOpB_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOpB ψ G) (hG' : HasOpB ψ G') :
    HasOpB ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp, hb⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp', hb'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul']
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul']
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]
  · rw [LinearMap.coe_comp]
    exact hb.comp hb'

theorem hasOpB_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOpB ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOpB ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOpB_one ψ) (fun _ _ _ _ hx hy => hasOpB_mul hx hy) hG

theorem bijOn_of_inv (e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (hm : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ)
    (hm' : ∀ Φ ∈ schA F κ, e' Φ ∈ schA F κ) (h1 : ∀ Φ ∈ schA F κ, e' (e Φ) = Φ) (h2 : ∀ Φ ∈ schA F κ, e (e' Φ) = Φ) :
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) :=
  Set.InvOn.bijOn (f' := e') ⟨fun Φ h => h1 Φ h, fun Φ h => h2 Φ h⟩ (fun Φ h => hm Φ h) (fun Φ h => hm' Φ h)

end GlobalTheory.SympChangeBij
end
end
