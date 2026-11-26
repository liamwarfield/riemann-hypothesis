module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CuspBlockLeft

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem yx_eq_one {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E} (hW : GlobalTheory.SiegelSet.IsWittFrame σ J X Y) :
    cT (σ : E →+* E) Y * J * X = 1 := by
  have h := congrArg (cT (σ : E →+* E)) hW.xy
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_one] at h
  have e1 : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j; simp [cT, sigma_sigma hcm]
  have e2 : cT (σ : E →+* E) J = J := by
    ext i j; simp [cT, hJ.1]
  rw [e1, e2, ← Matrix.mul_assoc] at h
  exact h

def selMat (l d k : ℕ) : Matrix (Fin d) (Fin (k + 1)) E := Matrix.of fun a i => if l + a.val = i.val then 1 else 0

section Frame

variable (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) {l d : ℕ} (h : l + d ≤ r) (k : Fin r)

theorem blk_init_one {Y X : Matrix (Fin n) (Fin r) E} (hM : cT (σ : E →+* E) Y * J * X = 1) :
    cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J * GlobalTheory.StdPar.initCols X k = selMat l d k.val := by
  ext a i
  have := congrFun (congrFun hM ⟨l + a.val, by omega⟩) (Fin.castLE k.2 i)
  rw [Matrix.one_apply] at this
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · simp [selMat, Fin.ext_iff]

theorem blk_init_zero {Y X : Matrix (Fin n) (Fin r) E} (hM : cT (σ : E →+* E) Y * J * X = 0) :
    cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J * GlobalTheory.StdPar.initCols X k = 0 := by
  ext a i
  have := congrFun (congrFun hM ⟨l + a.val, by omega⟩) (Fin.castLE k.2 i)
  exact this

theorem selMat_eq_zero (hk : k.val < l) : (selMat (E := E) l d k.val) = 0 := by
  ext a i
  have := i.2
  simp only [selMat, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg (by omega)]

theorem init_mul_selMat (hk : l + d ≤ k.val + 1) (Z : Matrix (Fin n) (Fin r) E) :
    GlobalTheory.StdPar.initCols Z k * (selMat (E := E) l d k.val)ᵀ = GlobalTheory.BlockForms.blkCols h Z := by
  ext c a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selMat, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (⟨l + a.val, by omega⟩ : Fin (k.val + 1))]
  · rw [if_pos rfl]; rfl
  · intro i _ hi
    rw [if_neg]
    intro e
    exact hi (Fin.ext e.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem selMat_mul_transpose (hk : l + d ≤ k.val + 1) :
    (selMat (E := E) l d k.val) * (selMat (E := E) l d k.val)ᵀ = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selMat, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_eq_single (⟨l + b.val, by omega⟩ : Fin (k.val + 1))]
  · simp only [if_true]
    by_cases hab : a = b
    · simp [hab]
    · rw [if_neg hab, if_neg]
      intro e; exact hab (Fin.ext (by simpa using e))
  · intro i _ hi
    rw [if_neg]
    intro e
    exact hi (Fin.ext e.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

end Frame

section Block

variable {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  (h : l + d ≤ r)

theorem cT_inclR {p q : Type} (M : Matrix p q E) :
    cT (sigR (AF F) σ) (M.map (inclR (F := F) (AF F))) = (cT (σ : E →+* E) M).map (inclR (F := F) (AF F)) := by
  ext i j
  simp [cT, sigR, inclR]

omit [NumberField E] in
theorem mul_adMat_expand {m : ℕ} (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (A A' : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))
    (hM : M = 1 + adMat F (GlobalTheory.BlockForms.blkCols h X) * (A - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
      adMat F (GlobalTheory.BlockForms.blkCols h Y) * (A' - 1) * adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J))
    (C : Matrix (Fin n) (Fin m) E) :
    M * adMat F C = adMat F C + adMat F (GlobalTheory.BlockForms.blkCols h X) * (A - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J * C) +
      adMat F (GlobalTheory.BlockForms.blkCols h Y) * (A' - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J * C) := by
  subst hM
  simp only [GlobalTheory.SiegelSet.adMat, Matrix.map_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]

omit [NumberField E] in
theorem mem_frameStab_of {kk : ℕ} (g : GAd σ J) (C : Matrix (Fin n) (Fin kk) E) (Z : Matrix (Fin n) (Fin d) E)
    (Q : Matrix (Fin d) (Fin kk) E) (A A₁ : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (hA : A * A₁ = 1)
    (hg : (matHom _ σ J g).1 * adMat F C = adMat F C + adMat F Z * (A - 1) * adMat F Q)
    (hQ : Q = 0 ∨ (C * Qᵀ = Z ∧ Q * Qᵀ = 1)) : g ∈ GlobalTheory.StdPar.frameStab σ J C ⊤ := by
  rcases hQ with hQ | ⟨hCQ, hQQ⟩
  · refine ⟨1, Subgroup.mem_top _, ?_⟩
    rw [hg, hQ]
    simp
  · set P := adMat F Qᵀ with hP
    have hQP : adMat F Q * P = 1 := by
      rw [hP, GlobalTheory.SiegelSet.adMat, GlobalTheory.SiegelSet.adMat, ← Matrix.map_mul, hQQ]
      simp
    have key : ∀ N N₁ : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), N + N₁ + N * N₁ = 0 →
        (1 + P * N * adMat F Q) * (1 + P * N₁ * adMat F Q) = 1 := by
      intro N N₁ hN
      have e : P * N * adMat F Q * (P * N₁ * adMat F Q) = P * (N * N₁) * adMat F Q := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (adMat F Q) P, hQP, Matrix.one_mul]
      calc (1 + P * N * adMat F Q) * (1 + P * N₁ * adMat F Q) = 1 + P * (N + N₁ + N * N₁) * adMat F Q := by
            rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, e,
              Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
            abel
        _ = 1 := by rw [hN, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    have hN : (A - 1) + (A₁ - 1) + (A - 1) * (A₁ - 1) = 0 := by
      have : (A - 1) + (A₁ - 1) + (A - 1) * (A₁ - 1) = A * A₁ - 1 := by noncomm_ring
      rw [this, hA, sub_self]
    have hB := key _ _ hN
    refine ⟨⟨_, _, hB, mul_eq_one_comm.mp hB⟩, Subgroup.mem_top _, ?_⟩
    show _ = adMat F C * (1 + P * (A - 1) * adMat F Q)
    rw [hg, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, GlobalTheory.SiegelSet.adMat,
      GlobalTheory.SiegelSet.adMat, ← Matrix.map_mul, hCQ]

theorem mem_levi_of (hcm : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : GlobalTheory.SiegelSet.IsWittFrame σ J X Y)
    (S : Finset (Fin r)) (hS : ∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) (g : GAd σ J)
    (A A₁ : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) (hA : A * A₁ = 1)
    (hg : (matHom _ σ J g).1 = 1 + adMat F (GlobalTheory.BlockForms.blkCols h X) * (A - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Y) * J) +
      adMat F (GlobalTheory.BlockForms.blkCols h Y) * (cT (sigR (AF F) σ) A₁ - 1) *
        adMat F (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h X) * J)) :
    g ∈ GlobalTheory.StdPar.levi σ J X Y S := by
  simp only [GlobalTheory.StdPar.levi, Subgroup.mem_iInf, Subgroup.mem_inf]
  intro k hk
  have hcase : k.val < l ∨ l + d ≤ k.val + 1 := by
    by_contra hc
    push_neg at hc
    exact hS k hc.1 (by omega) hk
  have hYX := yx_eq_one hcm hJ hW
  constructor
  · refine mem_frameStab_of g _ (GlobalTheory.BlockForms.blkCols h X) (selMat l d k.val) A A₁ hA ?_ ?_
    · rw [mul_adMat_expand h _ _ _ hg, blk_init_one σ J h k hYX, blk_init_zero σ J h k hW.xx]
      simp
    · rcases hcase with hc | hc
      · exact Or.inl (selMat_eq_zero k hc)
      · exact Or.inr ⟨init_mul_selMat h k hc X, selMat_mul_transpose k hc⟩
  · refine mem_frameStab_of g _ (GlobalTheory.BlockForms.blkCols h Y) (selMat l d k.val) (cT (sigR (AF F) σ) A₁)
      (cT (sigR (AF F) σ) A) (by rw [← Formalism.UG.cT_mul, hA, Formalism.UG.cT_one]) ?_ ?_
    · rw [mul_adMat_expand h _ _ _ hg, blk_init_zero σ J h k hW.yy, blk_init_one σ J h k hW.xy]
      simp
    · rcases hcase with hc | hc
      · exact Or.inl (selMat_eq_zero k hc)
      · exact Or.inr ⟨init_mul_selMat h k hc Y, selMat_mul_transpose k hc⟩

theorem mem_ratPts_of (g : GAd σ J) (M : Matrix (Fin n) (Fin n) E)
    (hM : (matHom _ σ J g).1 = M.map (inclR (F := F) (AF F)))
    (hinj : Function.Injective (inclR (F := F) (E := E) (AF F))) : g ∈ ratPts σ J := by
  haveI : Nontrivial (AF F ⊗[F] E) := ⟨⟨inclR (F := F) (AF F) 0, inclR (F := F) (AF F) 1, fun e => zero_ne_one (hinj e)⟩⟩
  have hdet : M.det ≠ 0 := by
    intro h0
    have hu : IsUnit (M.map (inclR (F := F) (AF F))).det := by
      rw [← hM]; exact Matrix.isUnits_det_units _
    have h1 := (inclR (F := F) (E := E) (AF F)).map_det M
    rw [h0, map_zero, RingHom.mapMatrix_apply] at h1
    rw [← h1] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, Units.ext hM.symm⟩
  show cT (σ : E →+* E) M * J * M = J
  apply Matrix.map_injective hinj
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  rw [hM, cT_inclR, JR, ← Matrix.map_mul, ← Matrix.map_mul] at hg
  exact hg

end Block

end GlobalTheory.CuspBlockLeft

namespace GlobalTheory.CuspBlockLeft

theorem cuspForm_blockEmb_left_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        ∀ (γ : GL (Fin d) E) (g : GlobalTheory.CuspRep.GA E d), ψ (ι (GlobalTheory.CuspRep.ratGL E d γ * g) * g₀) = ψ (ι g * g₀) := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW K _ S l d h ι hι _ hS _ _ ψ hψ g₀ _ γ g
  obtain ⟨Φ, j, -, -, hj, hΦ, hmat⟩ := hι
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  have hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F := F) (AF F) x := fun x => by
    rw [RingEquiv.symm_apply_eq, hΦE]
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := congrArg (fun z => (Φ z).1 w) hxy
    simp only [hΦE] at this
    exact (algebraMap E w.Completion).injective this
  have hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F := F) (AF F)) :=
    fun δ => by
      ext a b
      exact hΦs (δ.1 a b)

  have hlevi : ∀ g' : GlobalTheory.CuspRep.GA E d, ι g' ∈ GlobalTheory.StdPar.levi σ J Xf Yf S := fun g' =>
    GlobalTheory.CuspBlockLeft.mem_levi_of h hcm hJ hW S hS (ι g') (g'.1.map Φ.symm) ((g'⁻¹).1.map Φ.symm)
      (by rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; simp) (hmat g')
  have hratPt : ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
    refine GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) *
        (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) +
      GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) *
        (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J)) ?_ hinj
    rw [hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]
    simp [Matrix.map_add (f := _), Matrix.map_sub, Matrix.map_mul, Matrix.map_one]
  rw [map_mul, mul_assoc]
  exact hψ.1.leftM _ hratPt (hlevi _) _

end GlobalTheory.CuspBlockLeft
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

def iotaW (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
  (GlobalTheory.InertLocField.liftT (E := E) v).toAddMonoidHom.comp
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom.toAddMonoidHom

def conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) : w.adicCompletion E →+* w.adicCompletion E :=
  (toCompl (under_eq_of_isInertAt hw)).comp
    ((sigR (Fv F v) σ).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.toRingHom)

def glueW (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (1 - algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) • (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + P.map (iotaW hw)

def InLat {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (u : Fin d → K) : Prop :=
  ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u) i ∈ O

def InLat2 {K : Type} [Field K] (O : ValuationSubring K) {d : ℕ} (b : GL (Fin d) K) (z : Fin d ⊕ Fin d → K) : Prop :=
  InLat O b (z ∘ Sum.inl) ∧ InLat O b (z ∘ Sum.inr)

end GlobalTheory.InertBigCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqCompContinuousLinearEquivMixedSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqCompContinuousLinearEquivMixedSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem lintegral_sq_comp_linearEquiv_mixed (F : Type) [Field F] [NumberField F] (κ : Type)
    [Fintype κ] (n : ℕ)
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    ∃ c : ℝ≥0∞, ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ,
      ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 = c * ∫⁻ z, ‖h z‖ₑ ^ 2 := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := MeasurableAdd₂.toMeasurableAdd
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let eM := Q.toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n)))).IsAddHaarMeasure :=
    Q.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n))) =
      c • (volume : Measure (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨(c : ℝ≥0∞), fun h => ?_⟩
  have h1 : ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 =
      ∫⁻ z, ‖h z‖ₑ ^ 2 ∂(Measure.map eM (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    rw [lintegral_map_equiv]; rfl
  rw [h1, hc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqCompContinuousLinearEquivMixedSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sq_comp_continuousLinearEquiv_mixedSpace : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (n : ℕ)
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)),
    ∃ c : ℝ≥0∞, ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ,
      ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 = c * ∫⁻ z, ‖h z‖ₑ ^ 2 := by
  first | exact @GlobalTheory.lintegral_sq_comp_linearEquiv_mixed | exact GlobalTheory.lintegral_sq_comp_linearEquiv_mixed | (intros; apply GlobalTheory.lintegral_sq_comp_linearEquiv_mixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibniz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibniz
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelForm

theorem coefwise_del_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {v : V n} (g : ι → V n → ℂ) (Q : ι → V n → Alt n)
    (hg : ∀ k, DifferentiableAt ℝ (g k) v) (hQ : ∀ k S, DifferentiableAt ℝ (fun w => (bas n).repr (Q k w) S) v)
    (ξ : V n) :
    coefwise (fun f => del f v ξ) (fun w => ∑ k, g k w • Q k w) =
      ∑ k, (del (g k) v ξ • Q k v + g k v • coefwise (fun f => del f v ξ) (Q k)) := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (∑ k, g k x • Q k x) S) = fun x => ∑ k, g k x * (bas n).repr (Q k x) S :=
    funext fun x => by simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [FormMul.repr_coefwise, e,
    del_sum (A := fun k x => g k x * (bas n).repr (Q k x) S) (fun k _ => (hg k).mul (hQ k S)),
    ContinuousLinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [del_mul (hg k) (hQ k S), map_add (f := _), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    FormMul.repr_coefwise, smul_eq_mul, smul_eq_mul, add_comm]

theorem delAt_sum_smul : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) →
    (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) →
    GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v =
      ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  intro n ι _ v g Q hg hQ
  simp only [delAt, dOne, coefwise_del_sum_smul g Q hg hQ, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_add,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib]
  exact Finset.sum_comm

end GlobalTheory.CxForm.DelForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibnizStatement
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ) (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) → (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) → GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v = ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  first | exact @GlobalTheory.CxForm.DelForm.delAt_sum_smul | exact GlobalTheory.CxForm.DelForm.delAt_sum_smul | (intros; apply GlobalTheory.CxForm.DelForm.delAt_sum_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def wspToVV (lam : InfinitePlace E → DomWeight n) : Wsp lam →ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam :=
  PiTensorProduct.lift (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam)

def vvToWsp (lam : InfinitePlace E → DomWeight n) : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] Wsp lam :=
  (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Wsp lam) (PiTensorProduct.tprod ℂ)).exists.choose

theorem vvToWsp_tenMul (lam : InfinitePlace E → DomWeight n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    vvToWsp lam (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = PiTensorProduct.tprod ℂ u :=
  (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Wsp lam) (PiTensorProduct.tprod ℂ)).exists.choose_spec u

theorem wspToVV_tprod (lam : InfinitePlace E → DomWeight n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    wspToVV lam (PiTensorProduct.tprod ℂ u) = GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u := by
  simp [wspToVV]

theorem wInf_tprod (lam : InfinitePlace E → DomWeight n) (g : UA E n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    wInf lam g (PiTensorProduct.tprod ℂ u) =
      PiTensorProduct.tprod ℂ fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding g) (u v) :=
  PiTensorProduct.map_tprod _ _

theorem rep_tenMul (lam : InfinitePlace E → DomWeight n) (x : infU E n) (u : ∀ v, nablaSq ℂ n (lam v)) :
    GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) =
      GlobalTheory.CoefIrred.tenMul (K := ℂ) lam fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding x.1) (u v) :=
  GlobalTheory.DefU.rhoK_tenMul lam (GlobalTheory.DefU.cAll x.1) u

def wspEquivVV (lam : InfinitePlace E → DomWeight n) : Wsp lam ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam :=
  LinearEquiv.ofLinear (wspToVV lam) (vvToWsp lam)
    (by
      have hu := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) n lam (Formalism.L2.DIV.VV ℂ lam) (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam)).unique
        (y₁ := wspToVV lam ∘ₗ vvToWsp lam) (y₂ := LinearMap.id)
        (fun u => by simp [vvToWsp_tenMul, wspToVV_tprod]) (fun u => rfl)
      exact hu)
    (by
      apply PiTensorProduct.ext
      ext u
      simp [wspToVV_tprod, vvToWsp_tenMul])

theorem wspEquivVV_wInf (lam : InfinitePlace E → DomWeight n) (x : infU E n) (w : Wsp lam) :
    wspEquivVV lam (wInf lam x.1 w) = GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x (wspEquivVV lam w) := by
  have h : wspToVV lam ∘ₗ wInf lam x.1 = GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam x ∘ₗ wspToVV lam := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun u => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
    rw [wInf_tprod, wspToVV_tprod, wspToVV_tprod, rep_tenMul]
  exact LinearMap.congr_fun h w

def wInfU (lam : InfinitePlace E → DomWeight n) : Representation ℂ (infU E n) (Wsp lam) :=
  (wInf lam).comp (infU E n).subtype

theorem isIrreducible_wInfU (lam : InfinitePlace E → DomWeight n) : (wInfU lam).IsIrreducible :=
  (GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv id Function.surjective_id (wspEquivVV lam)
    (ρ := wInfU lam) (σ := GlobalTheory.DefU.Wt.rep (E := E) (n := n) lam)
    (fun x w => wspEquivVV_wInf lam x w)).2 (GlobalTheory.DefU.Wt.isIrreducible_rep E n lam)

theorem span_wInf_infU_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n),
    Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) = ⊤ := by
  intro E _ _ _ n lam
  exact GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible (infU E n) (Wsp lam) (wInfU lam) (isIrreducible_wInfU lam)

end GlobalTheory.BCT.TrKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTopStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) = ⊤ := by
  first | exact @GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | exact GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top | (intros; apply GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfLieIntertwineL2
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfLieIntertwineL2
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealWeil

theorem exists_weylAlg_conj {l : Type} [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : Sch l →ₗ[ℂ] Sch l) (hI : ∀ w f, A' (dRho w f) = dRho (L' w) (A' f))
    {B : Sch l →L[ℂ] Sch l} (hB : B ∈ weylAlg l) :
    ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f) := by
  refine weylAlg_induction (P := fun B => ∃ B' : Sch l →L[ℂ] Sch l, ∀ f, B (A' f) = A' (B' f))
    ⟨1, fun f => by simp⟩ ?_ ⟨0, fun f => by simp⟩ ?_ ?_ hB
  · rintro A w ⟨B', h⟩
    refine ⟨B' * dRho (L'.symm w), fun f => ?_⟩
    have e := hI (L'.symm w) f
    rw [LinearEquiv.apply_symm_apply] at e
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← e, h]
  · rintro A B ⟨A₁, h₁⟩ ⟨B₁, h₂⟩
    exact ⟨A₁ + B₁, fun f => by simp [h₁, h₂]⟩
  · rintro c A ⟨A₁, h⟩
    exact ⟨c • A₁, fun f => by simp [h]⟩

theorem norm_toLp_le_of_lintegral_le {l : Type} [Fintype l] (A' : Sch l →ₗ[ℂ] Sch l) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) (f : Sch l) :
    ‖(A' f).toLp 2 volume‖ ≤ C.toReal ^ (1 / 2 : ℝ) * ‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC)
    (f.eLpNorm_lt_top 2 volume).ne) ?_
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (A' f).continuous.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) f.continuous.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow (h f) (by norm_num)

end GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f)) →
    Continuous A' := by
  intro l _ L' A' C hC h2 hI
  refine WithSeminorms.continuous_of_continuous_comp (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ) A'
    fun i => ?_
  obtain ⟨B, hB, hle⟩ := GlobalTheory.RealWeil.exists_seminorm_le (l := l) i.1 i.2
  choose B' hB' using fun r => GlobalTheory.RealWeil.exists_weylAlg_conj L' A' hI (hB r)
  let c : NNReal := Real.toNNReal (C.toReal ^ (1 / 2 : ℝ))
  let q : Seminorm ℂ (GlobalTheory.RealWeil.Sch l) := ∑ r, c • (normSeminorm ℂ (GlobalTheory.RealWeil.L2 l)).comp
    ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).toLinearMap
  refine Seminorm.continuous_of_le (q := q) (Seminorm.continuous_finsetSum fun r _ => ?_) fun f => ?_
  · change Continuous fun f => (c : ℝ) * ‖(GlobalTheory.RealWeil.schwartzToL2 l) (B' r f)‖
    exact continuous_const.mul (continuous_norm.comp ((GlobalTheory.RealWeil.schwartzToL2 l).comp (B' r)).continuous)
  · have e : q f = ∑ r, (c : ℝ) * ‖(B' r f).toLp 2 volume‖ := by
      simp [q, GlobalTheory.RealWeil.schwartzToL2_apply, NNReal.smul_def, smul_eq_mul]
    rw [e]
    change SchwartzMap.seminorm ℂ i.1 i.2 (A' f) ≤ _
    refine (hle (A' f)).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [hB']
    refine (GlobalTheory.RealWeil.norm_toLp_le_of_lintegral_le A' C hC h2 _).trans (le_of_eq ?_)
    rw [show (c : ℝ) = C.toReal ^ (1 / 2 : ℝ) from Real.coe_toNNReal _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfLieIntertwineL2Statement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_lie_intertwine_l2 : ∀ (l : Type) [Fintype l] (L' : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (A' : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l) (C : ℝ≥0∞), C ≠ ⊤ →
    (∀ f, ∫⁻ x, ‖A' f x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖f x‖ₑ ^ 2) →
    (∀ w f, A' (GlobalTheory.RealWeil.dRho w f) = GlobalTheory.RealWeil.dRho (L' w) (A' f)) →
    Continuous A' := by
  first | exact @GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound | exact GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound | (intros; apply GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariant
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisDerivCM

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (x + x') y = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x' y := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem map_symplOHF_eq_zero {B : Type} [CommRing B] [Algebra F B] (p : AF F →ₐ[F] B)
    (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (x y : WOF F E nS nT)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (symplOHF σ JS JT ξ₀ x y) = 0 := by
  have h1 : p (symplOF σ JS JT ξ₀ x y) = 0 := by
    unfold symplOF hOF
    rw [GlobalTheory.WeilVacMove.sum_reorder (cAF σ) (fun k i => incAF F E (JS⁻¹ k i)) (fun j l => incAF F E (JT j l)) x y]
    refine GlobalTheory.FockCompare.map_trace_sesq_eq_zero p σ _ (fun k i => incAF F E (JS⁻¹ k i))
      (fun j l => incAF F E (JT j l)) xᵀ yᵀ (h.imp (fun h => ?_) fun h => ?_) <;>
    · ext i j
      exact congrFun (congrFun h j) i
  unfold symplOHF
  rw [map_mul, h1, mul_zero]

theorem symplOHF_fin_real (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u v : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) (hv : v.map (finPartF F E) = 0) :
    symplOHF σ JS JT ξ₀ u v = 0 ∧ symplOHF σ JS JT ξ₀ v u = 0 :=
  ⟨Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ u v (Or.inl hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ u v (Or.inr hv)),
    Prod.ext (map_symplOHF_eq_zero (fstA F) σ JS JT ξ₀ v u (Or.inr hu))
      (map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ v u (Or.inl hv))⟩

theorem heisOF_deriv_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f L _ hL u hu hf
  funext w
  have key : ∀ t : ℝ, B.ψ (symplOHF σ JS JT ξ₀ w u) * heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u) =
      heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    obtain ⟨h1, h2⟩ := symplOHF_fin_real σ JS JT ξ₀ u (L t) hu (hL t)
    have hfx := congrFun hf (w + L t)
    simp only [heisOF] at hfx ⊢
    conv_rhs => rw [← hfx]
    rw [symplOHF_add_left, symplOHF_add_left, h1, h2, add_zero, add_zero,
      show w + u + L t = w + L t + u by abel]
    ring
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + u)) 0 = _
  rw [← deriv_const_mul_field]
  exact congrArg (fun g : ℝ → ℂ => deriv g 0) (funext key)

end GlobalTheory.HeisDerivCM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariantStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ u : Formalism.IndefR.DatumF.WOF F E nS nT, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) f = f →
      Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) (fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0) = fun w => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  first | exact @GlobalTheory.HeisDerivCM.heisOF_deriv_fix | exact GlobalTheory.HeisDerivCM.heisOF_deriv_fix | (intros; apply GlobalTheory.HeisDerivCM.heisOF_deriv_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunction
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblBoxRho

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]


omit [DecidableEq α] in
theorem symp_dbl_toCols (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    symp (R := R) c ξ JA (dbl JB) x y =
      symp (R := R) c ξ JA JB x.toCols₁ y.toCols₁ - symp (R := R) c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.toCols₁_apply, Matrix.toCols₂_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg]

theorem star_apply_eq_neg (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (t : R) : star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ]
  simp

variable [Invertible (2 : R)]

theorem schr_boxFun (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) {κ : Type} [Fintype κ] (w₁ w₂ : (κ → R) × (κ → R))
    (φ₁ φ₂ : (κ → R) → ℂ) :
    schr ψ (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 (-w₂.2)) (boxFun φ₁ fun x => star (φ₂ x)) =
      boxFun (schr ψ w₁ φ₁) fun x => star (schr ψ w₂ φ₂ x) := by
  funext x
  have e : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
  have e1 : (x + Sum.elim w₁.1 w₂.1) ∘ Sum.inl = x ∘ Sum.inl + w₁.1 := rfl
  have e2 : (x + Sum.elim w₁.1 w₂.1) ∘ Sum.inr = x ∘ Sum.inr + w₂.1 := rfl
  have e3 : x ⬝ᵥ Sum.elim w₁.2 (-w₂.2) = (x ∘ Sum.inl) ⬝ᵥ w₁.2 - (x ∘ Sum.inr) ⬝ᵥ w₂.2 := by
    conv_lhs => rw [e]
    rw [sumElim_dotProduct_sumElim, dotProduct_neg, sub_eq_add_neg]
  simp only [schr, boxFun, e1, e2, e3, sumElim_dotProduct_sumElim, dotProduct_neg, star_mul', star_apply_eq_neg ψ hψ]
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

end Alg

theorem boxrho : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ ξ' : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)),
    IsDblCoord c ξ JA JB d dd → ∀ ψ : AddChar R ℂ, (∀ t, ‖ψ t‖ = 1) → ∀ (Λ : Set (Matrix α β E)) (f : (κ → R) → ℂ),
    (∀ w ∈ Λ, d.rho ψ w f = ψ (⅟(2 : R) * symp c ξ' JA JB w w) • f) →
    ∀ z : Matrix α (β ⊕ β) E, z.toCols₁ ∈ Λ → z.toCols₂ ∈ Λ →
      dd.rho ψ z (boxFun f (fun x => star (f x))) = ψ (⅟(2 : R) * symp c ξ' JA (dbl JB) z z) • boxFun f (fun x => star (f x)) := by
  intro R _ _ E _ _ c α β _ _ _ _ ξ ξ' JA JB κ _ d dd hD ψ hψ Λ f hf z h₁ h₂
  have hz : Matrix.fromCols z.toCols₁ z.toCols₂ = z := Matrix.fromCols_toCols z
  have he := hD z.toCols₁ z.toCols₂
  rw [hz] at he
  have e₁ := hf _ h₁
  have e₂ := hf _ h₂
  simp only [Darboux.rho] at e₁ e₂
  rw [Darboux.rho, he, schr_boxFun ψ hψ, e₁, e₂, symp_dbl_toCols]
  funext x
  simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul', star_apply_eq_neg ψ hψ, mul_sub]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.DblBoxRho
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenDoubledCoordsProductFunctionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergEigen_doubledCoords_productFunction : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ ξ' : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)),
    IsDblCoord c ξ JA JB d dd → ∀ ψ : AddChar R ℂ, (∀ t, ‖ψ t‖ = 1) → ∀ (Λ : Set (Matrix α β E)) (f : (κ → R) → ℂ),
    (∀ w ∈ Λ, d.rho ψ w f = ψ (⅟(2 : R) * symp c ξ' JA JB w w) • f) →
    ∀ z : Matrix α (β ⊕ β) E, z.toCols₁ ∈ Λ → z.toCols₂ ∈ Λ →
      dd.rho ψ z (boxFun f (fun x => star (f x))) = ψ (⅟(2 : R) * symp c ξ' JA (dbl JB) z z) • boxFun f (fun x => star (f x)) := by
  first | exact @GlobalTheory.DblBoxRho.boxrho | exact GlobalTheory.DblBoxRho.boxrho | (intros; apply GlobalTheory.DblBoxRho.boxrho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplMapSplitProj
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
open Formalism.UG (cT)
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockForms.LeviLoc

section Lin

variable (R : Type) [CommRing R] {l d n : ℕ}

variable {R}

theorem map_formula {T : Type} [CommRing T] (p : R →+* T) (s : R →+* R) (X Y : Matrix (Fin n) (Fin d) R)
    (X' Y' : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) (hQ : Q.map (p.comp s) = 1) :
    (1 + X * (P - 1) * Y' + Y * (cT s Q - 1) * X').map p = 1 + X.map p * (P.map p - 1) * Y'.map p := by
  have h1 : (cT s Q).map p = 1 := by
    rw [← Matrix.transpose_one, ← hQ]; rfl
  rw [Matrix.map_add _ (map_add p), Matrix.map_add _ (map_add p), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub _ (map_sub p), Matrix.map_sub _ (map_sub p), h1,
    Matrix.map_one _ (map_zero p) (map_one p), Matrix.map_one _ (map_zero p) (map_one p)]
  simp

end Lin

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
  {C : GL (Fin n) E} {l d : ℕ}


end Frame

section Adele

theorem gl_entry {R : Type} [CommRing R] {d : ℕ} {x y : GL (Fin d) R} (h : x = y) (a b : Fin d) : x.1 a b = y.1 a b := by
  rw [h]

open GlobalTheory.LFun GlobalTheory.CuspRep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem compFin_eq (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u z = Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (finTens F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

omit [NumberField E] in
theorem compFin_sigR (σ : E →ₐ[F] E) (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E u (sigR _ σ z) = sigR _ σ (compFin F E u z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]


theorem compFin_eq_zero (u : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = u → pLoc E w (finAdEquiv F E (finTens F E z)) = 0) :
    compFin F E u z = 0 := by
  have h1 : ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E)) * finTens F E z = 0 := by
    refine (finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun w => ?_)
    rw [map_mul, map_zero]
    change pLoc E w (_ * _) = pLoc E w 0
    rw [map_mul, map_zero]
    by_cases hw : w.under (𝓞 F) = u
    · rw [hz w hw, mul_zero]
    · have e : pLoc E w (finAdEquiv F E ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) = 0 := by
        refine Eq.trans (b := toCompl (rfl : w.under (𝓞 F) = _) _)
          (finAdEquiv_apply rfl ((singleFin u (1 : Fv F u)) ⊗ₜ[F] (1 : E))) ?_
        rw [Algebra.TensorProduct.map_tmul, evalV_singleFin_ne hw, TensorProduct.zero_tmul, map_zero]
      rw [e, zero_mul]
  have h2 := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)) h1
  rwa [map_mul, map_zero, Algebra.TensorProduct.map_tmul, evalV_singleFin_self, map_one,
    ← Algebra.TensorProduct.one_def, one_mul, ← compFin_eq] at h2



variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z))) {d : ℕ}
include hΦ

theorem fin_symm (a : Ad E) : finAdEquiv F E (finTens F E (Φ.symm a)) = pFin E a :=
  (congrArg Prod.snd (hΦ (Φ.symm a))).symm.trans (congrArg (pFin E) (Φ.apply_symm_apply a))

end Adele


end GlobalTheory.BlockForms.LeviLoc

end
end
