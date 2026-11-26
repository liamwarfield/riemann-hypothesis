module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasis
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.GoodLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem sigR_inclR (A : Type) [CommRing A] [Algebra F A] (e : E) :
    sigR A σ (inclR (F := F) A e) = inclR (F := F) A (σ e) := by
  simp [sigR, inclR]

theorem dual_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) (i : Fin r) :
    ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) *ᵥ z) i
      = hR (Fv F v) σ J (colV v A i) z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, colV, JR, sigR_inclR, mulVec, dotProduct, map_apply, Matrix.mul_apply,
    cT, transpose_apply, map_sum, map_mul, Finset.sum_mul, RingHom.coe_coe]
  rw [Finset.sum_comm]

theorem col_mulVec (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (w : Fin r → Fv F v ⊗[F] E) :
    A.map (inclR (F := F) (Fv F v)) *ᵥ w = ∑ i, w i • colV v A i := by
  ext a
  simp [mulVec, dotProduct, colV, Finset.sum_apply, mul_comm]

theorem hR_colV (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin n) (Fin r) E)
    (B : Matrix (Fin n) (Fin r) E) (i j : Fin r) :
    hR (Fv F v) σ J (colV v A i) (colV v B j)
      = inclR (F := F) (Fv F v) ((cT (σ : E →+* E) A * J * B) i j) := by
  rw [← dual_mulVec]
  conv_rhs => rw [Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_apply, colV, map_sum, map_mul]

theorem sigma_sigma (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]

theorem cT_mul_rect (s : E →+* E) {a b c : Type} [Fintype b] (P : Matrix a b E) (Q : Matrix b c E) :
    cT s (P * Q) = cT s Q * cT s P := by
  simp [cT, Matrix.map_mul, transpose_mul]

theorem gram_yx (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) : cT (σ : E →+* E) Y * J * X = 1 := by
  have hcT : cT (σ : E →+* E) J = J := by
    ext i j
    exact hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    exact sigma_sigma hCM _
  have h1 : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1 := by
    ext i j
    simp [cT, Matrix.one_apply, eq_comm]
  have := congrArg (cT (σ : E →+* E)) hW.xy
  rw [cT_mul_rect, cT_mul_rect, hcT, hcc, h1, ← Matrix.mul_assoc] at this
  exact this

def projP (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (X Y : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  1 - X.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) Y * J).map (inclR (F := F) (Fv F v))
    - Y.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) X * J).map (inclR (F := F) (Fv F v))

theorem projP_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (z : Fin n → Fv F v ⊗[F] E) :
    projP v σ J X Y *ᵥ z = z - ∑ i, hR (Fv F v) σ J (colV v Y i) z • colV v X i
      - ∑ i, hR (Fv F v) σ J (colV v X i) z • colV v Y i := by
  have hb : ∀ A B : Matrix (Fin n) (Fin r) E,
      (A.map (inclR (F := F) (Fv F v)) * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, hR (Fv F v) σ J (colV v B i) z • colV v A i := by
    intro A B
    rw [← mulVec_mulVec, col_mulVec]
    simp only [dual_mulVec]
  simp only [projP, sub_mulVec, one_mulVec, hb]

theorem leviMat_mulVec (v : HeightOneSpectrum (𝓞 F)) (X Y : Matrix (Fin n) (Fin r) E)
    (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (z : Fin n → Fv F v ⊗[F] E) :
    leviMat σ J (Fv F v) X Y M *ᵥ z =
      ∑ i, (hR (Fv F v) σ J (colV v Y i) (M *ᵥ colV v X i) * hR (Fv F v) σ J (colV v Y i) z) • colV v X i
      + ∑ i, (hR (Fv F v) σ J (colV v X i) (M *ᵥ colV v Y i) * hR (Fv F v) σ J (colV v X i) z) • colV v Y i
      + projP v σ J X Y *ᵥ (M *ᵥ (projP v σ J X Y *ᵥ z)) := by
  have hd : ∀ (A B : Matrix (Fin n) (Fin r) E) (i : Fin r),
      ((cT (σ : E →+* E) A * J).map (inclR (F := F) (Fv F v)) * M * B.map (inclR (F := F) (Fv F v))) i i
        = hR (Fv F v) σ J (colV v A i) (M *ᵥ colV v B i) := by
    intro A B i
    rw [← dual_mulVec, Matrix.mul_assoc]
    rfl
  have hmv : ∀ (A B : Matrix (Fin n) (Fin r) E) (d : Fin r → Fv F v ⊗[F] E),
      (A.map (inclR (F := F) (Fv F v)) * diagonal d * (cT (σ : E →+* E) B * J).map (inclR (F := F) (Fv F v))) *ᵥ z
        = ∑ i, (d i * hR (Fv F v) σ J (colV v B i) z) • colV v A i := by
    intro A B d
    rw [← mulVec_mulVec, ← mulVec_mulVec, col_mulVec]
    simp only [mulVec_diagonal, dual_mulVec]
  unfold leviMat
  simp only [add_mulVec]
  rw [hmv, hmv]
  simp only [hd]
  simp only [mulVec_mulVec, projP, Matrix.mul_assoc]

theorem hR_isom {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v) (a b : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J ((matHom _ σ J g).1 *ᵥ a) ((matHom _ σ J g).1 *ᵥ b) = hR (Fv F v) σ J a b := by
  have hg : cT (sigR (Fv F v) σ) (matHom _ σ J g).1 * JR (Fv F v) J * (matHom _ σ J g).1 = JR (Fv F v) J := g.2
  simp only [hR]
  rw [Formalism.UG.P.hform_mulVec, hg]

theorem levi_mem_stabLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ → ∀ (p m : GLoc σ J v), p ∈ stabLat σ J Λ → ∀ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → (matHom _ σ J m).1 = leviMat σ J (Fv F v) X Y (matHom _ σ J p).1 → m ∈ stabLat σ J Λ := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hW v Λ hΛ hA p m hp B _ _ hm
  obtain ⟨-, ⟨hint, heven⟩, hmax⟩ := hΛ
  have hxx : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v X j) = 0 := fun i j => by
    rw [hR_colV, hW.xx]; simp
  have hyy : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v Y j) = 0 := fun i j => by
    rw [hR_colV, hW.yy]; simp
  have hxy : ∀ i j, hR (Fv F v) σ J (colV v X i) (colV v Y j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, hW.xy, Matrix.one_apply]; split_ifs <;> simp
  have hyx : ∀ i j, hR (Fv F v) σ J (colV v Y i) (colV v X j) = if i = j then 1 else 0 := fun i j => by
    rw [hR_colV, gram_yx hCM hJ hW, Matrix.one_apply]; split_ifs <;> simp
  have hδ : ∀ i j : Fin r, ((if i = j then 1 else 0 : Fv F v ⊗[F] E)) ∈ intLoc F E v := fun i j => by
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hx : ∀ i, colV v X i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxx]; exact zero_mem _
    · rw [hyx]; exact hδ _ _
    · simp [hxx, hyx]
  have hy : ∀ i, colV v Y i ∈ Λ := fun i => by
    refine (hA _).2 ⟨fun j => ?_, fun j => ?_, ?_⟩
    · rw [hxy]; exact hδ _ _
    · rw [hyy]; exact zero_mem _
    · simp [hxy, hyy]
  have hP : ∀ z ∈ Λ, projP v σ J X Y *ᵥ z ∈ Λ := fun z hz => by
    rw [projP_mulVec]
    exact ((hA z).1 hz).2.2
  have hsm : ∀ a ∈ intLoc F E v, ∀ z ∈ Λ, a • z ∈ Λ := fun a ha z hz => Λ.smul_mem ⟨a, ha⟩ hz
  have hpz : ∀ z ∈ Λ, (matHom _ σ J p).1 *ᵥ z ∈ Λ := fun z hz => (hp z).1 hz
  have hsub : ∀ z ∈ Λ, (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z hz => by
    rw [hm, leviMat_mulVec]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) (sum_mem fun i _ => ?_)) (hP _ (hpz _ (hP z hz)))
    · exact hsm _ (mul_mem (hint _ (hy i) _ (hpz _ (hx i))) (hint _ (hy i) _ hz)) _ (hx i)
    · exact hsm _ (mul_mem (hint _ (hx i) _ (hpz _ (hy i))) (hint _ (hx i) _ hz)) _ (hy i)
  let L' : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E) :=
    { carrier := {z | (matHom _ σ J m).1 *ᵥ z ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, mulVec_add] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a z hz => by
        have e : (matHom _ σ J m).1 *ᵥ (a • z) = a • ((matHom _ σ J m).1 *ᵥ z) := by
          change (matHom _ σ J m).1 *ᵥ ((a : Fv F v ⊗[F] E) • z) = (a : Fv F v ⊗[F] E) • ((matHom _ σ J m).1 *ᵥ z)
          rw [mulVec_smul]
        change (matHom _ σ J m).1 *ᵥ (a • z) ∈ Λ
        rw [e]
        exact Λ.smul_mem a hz }
  have hL' : ∀ z, z ∈ L' ↔ (matHom _ σ J m).1 *ᵥ z ∈ Λ := fun z => Iff.rfl
  have hev : IsEvenInt (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) L' := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · rw [← hR_isom m a b]
      exact hint _ ha _ hb
    · rw [← hR_isom m a a]
      exact heven _ ha
  have hle : L' ≤ Λ := hmax L' hev hsub
  exact fun y => ⟨hsub y, fun h => hle h⟩

end GlobalTheory.CompanionTheory.KFin.GoodLocal

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasisStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.max_even_lattice_adapted_basis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ → ∀ (p m : GLoc σ J v), p ∈ stabLat σ J Λ → ∀ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → (matHom _ σ J m).1 = leviMat σ J (Fv F v) X Y (matHom _ σ J p).1 → m ∈ stabLat σ J Λ := by
  first | exact @GlobalTheory.CompanionTheory.KFin.GoodLocal.levi_mem_stabLat | exact GlobalTheory.CompanionTheory.KFin.GoodLocal.levi_mem_stabLat | (intros; apply GlobalTheory.CompanionTheory.KFin.GoodLocal.levi_mem_stabLat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionBallIndicatorSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionBallIndicatorSpan
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl
open scoped Topology

namespace GlobalTheory.CompanionTheory.ThetaInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ball (n : ℕ) (s : kˣ) :
    IsOpen {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} :=
  (isOpen_polyBall n s).preimage continuous_ofAdd

theorem isCompact_ball (n : ℕ) (s : kˣ) :
    IsCompact {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} := by
  have e : {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} =
      Multiplicative.toAdd '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))) := by
    ext a
    constructor
    · intro h
      exact ⟨Multiplicative.ofAdd a, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [e]
  exact (isCompact_polyBall n s).image continuous_toAdd

theorem isLocallyConstant_of_periodic {n : ℕ} {Y : Type} (g : (Fin n → k) → Y) (s : kˣ)
    (h : ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → g (v + a) = g v) :
    IsLocallyConstant g := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have h0 : (fun z : Fin n → k => -x + z) ⁻¹'
      {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} ∈ 𝓝 x :=
    ((isOpen_ball n s).preimage (by fun_prop)).mem_nhds (by
      show Multiplicative.ofAdd (-x + x) ∈ polyBall (k := k) n s
      rw [neg_add_cancel]
      exact one_mem _)
  filter_upwards [h0] with z hz
  have e : z = x + (-x + z) := by abel
  rw [e]
  exact h x _ hz

theorem hasCompactSupport_of_ball {n : ℕ} {E : Type} [AddCommGroup E] (g : (Fin n → k) → E) (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) : HasCompactSupport g := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine HasCompactSupport.intro (isCompact_ball n S) fun x hx => ?_
  by_contra h1
  exact hx (h x h1)

def tw (ψ : AddChar k Circle) {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]
    (g : (Fin (N + 1) → k) → E) : (Fin (N + 1) → k) → E :=
  fun v => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) • g v

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem isLocallyConstant_tw (ψ : AddChar k Circle) (hψ : Continuous ψ)
    {g : (Fin (N + 1) → k) → E} (hg : IsLocallyConstant g) : IsLocallyConstant (tw ψ g) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have h1 : IsLocallyConstant fun v : Fin (N + 1) → k => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) := by
    refine isLocallyConstant_of_periodic _ s fun v a ha => ?_
    have h2 : ψ (a (Fin.last N)) = 1 := hs _ (ha (Fin.last N))
    rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv (a := a (Fin.last N)), h2,
      inv_one, mul_one]
  exact h1.comp₂ hg fun c x => c • x

theorem hasCompactSupport_tw (ψ : AddChar k Circle) {g : (Fin (N + 1) → k) → E} (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) :
    HasCompactSupport (tw ψ g) := by
  refine hasCompactSupport_of_ball _ S fun v hv => h v fun h0 => hv ?_
  simp [tw, h0]

section Int

variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem smInt_comp_inv_mulVec (g : GL (Fin (N + 1)) k) {φ : (Fin (N + 1) → k) → E}
    (l : IsLocallyConstant φ) :
    smInt (Measure.pi fun _ : Fin (N + 1) => ν) (φ ∘ ((g⁻¹ : GL (Fin (N + 1)) k) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) •
        smInt (Measure.pi fun _ : Fin (N + 1) => ν) φ := by
  have hm : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) k, Measurable B.mulVec := fun B =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have key : ∀ B : Set (Fin (N + 1) → k), MeasurableSet B →
      (Measure.pi fun _ : Fin (N + 1) => ν)
          (((g⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec ⁻¹' B) =
        (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ENNReal) *
          (Measure.pi fun _ : Fin (N + 1) => ν) B := by
    intro B hB
    have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl
    conv_lhs => rw [← h1]
    rw [Measure.smul_apply, Measure.map_apply (hm _) ((hm _) hB), smul_eq_mul]
    congr 2
    ext x
    simp only [Set.mem_preimage, mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  rw [Set.preimage_comp, key (φ ⁻¹' {v}) (l.isOpen_fiber v).measurableSet, ENNReal.toReal_mul, smul_smul]
  congr 1
  simp [nabs]

end Int

theorem exists_twisted_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  intro k _ _ _ _ ψ hψ N X E _ _ _ _ r hper hsup tr htr lev A hlev
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ : ∃ ν : Measure k, ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let μ : Measure (Fin (N + 1) → k) := Measure.pi fun _ => ν
  haveI hμ : μ.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hl : ∀ f, IsLocallyConstant (tw ψ (r f)) := fun f => by
    obtain ⟨s, hs⟩ := hper f
    exact isLocallyConstant_tw ψ hψ (isLocallyConstant_of_periodic _ s fun v a ha => hs v a ha)
  have hc : ∀ f, HasCompactSupport (tw ψ (r f)) := fun f => by
    obtain ⟨S, hS⟩ := hsup f
    exact hasCompactSupport_tw ψ S hS
  let T : X →ₗ[ℂ] E :=
    { toFun := fun f => smInt μ (tw ψ (r f))
      map_add' := fun f g => by
        have e : tw ψ (r (f + g)) = tw ψ (r f) + tw ψ (r g) := by
          funext v
          simp [tw, map_add (f := _), smul_add]
        show smInt μ (tw ψ (r (f + g))) = smInt μ (tw ψ (r f)) + smInt μ (tw ψ (r g))
        rw [e, smInt_add μ (hl f) (hc f) (hl g) (hc g)]
      map_smul' := fun c f => by
        have e : tw ψ (r (c • f)) = (c • LinearMap.id : E →ₗ[ℂ] E) ∘ tw ψ (r f) := by
          funext v
          simp only [tw, Function.comp, map_smul, Pi.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
        show smInt μ (tw ψ (r (c • f))) = c • smInt μ (tw ψ (r f))
        rw [e, smInt_linear μ _ (hl f) (hc f)]
        rfl }
  have hT : ∀ f, T f = smInt μ (tw ψ (r f)) := fun _ => rfl
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a f
    let L : E →ₗ[ℂ] E := ((ψ (a (Fin.last N)) : Circle) : ℂ) • LinearMap.id
    have e : tw ψ (r (tr a f)) = (L ∘ tw ψ (r f)) ∘ fun v => v + a := by
      funext v
      simp only [tw, Function.comp, htr, L, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [Pi.add_apply]
      abel
    rw [hT, hT, e, smInt_comp_measurePreserving μ (measurePreserving_add_right μ a) ((hl f).comp _),
      smInt_linear μ L (hl f) (hc f)]
    rfl
  · intro m hm f
    have e : tw ψ (r (lev m f)) = (A m ∘ tw ψ (r f)) ∘
        ((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec := by
      funext v
      simp only [tw, Function.comp, hlev, map_smul]
      rw [mulVec_last_of_mem k _ (inv_mem hm) v]
    rw [hT, hT, e]
    refine (smInt_comp_inv_mulVec ν m ((hl f).comp _)).trans ?_
    congr 1
    exact smInt_linear μ (A m) (hl f) (hc f)
  · intro s hs
    have hLo := isOpen_ball (k := k) (N + 1) s
    have hLc := isCompact_ball (k := k) (N + 1) s
    refine ⟨(((μ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s}).toReal : ℝ) : ℂ), ?_, fun b e hb => ?_⟩
    · have h0 := (hLo.measure_pos μ ⟨0, one_mem (polyBall (k := k) (N + 1) s)⟩).ne'
      exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, hLc.measure_lt_top.ne⟩)
    · have e' : tw ψ (r b) = Set.indicator {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} fun _ => e := by
        funext v
        by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s
        · have h1 : ψ (v (Fin.last N)) = 1 := hs v hv
          simp only [tw]
          rw [hb v, if_pos hv, Set.indicator_of_mem (show v ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            AddChar.map_neg_eq_inv, h1]
          simp
        · simp only [tw]
          rw [hb v, if_neg hv, Set.indicator_of_notMem (show v ∉ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            smul_zero]
      rw [hT, e', smInt_indicator]

end GlobalTheory.CompanionTheory.ThetaInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionBallIndicatorSpanStatement
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_ball_indicator_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral | exact GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral | (intros; apply GlobalTheory.CompanionTheory.ThetaInt.exists_twisted_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdFamL
open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult

variable {n : ℕ}

def AdFamL (lev : Fin n → ℕ) {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n))
    (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (X1 X2 : Fin n → Fin n → Module.End ℂ W), LRel lev X1 X2 →
    ∀ c d, lev c = lev d → ∀ i, (X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d) =
      ∑ j, M c d j i • evB lev X1 X2 (w j)

theorem ad_letter {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] {X1 X2 : Fin n → Fin n → Module.End ℂ W}
    (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (s : Bool) (a b : Fin n) :
    (X1 c d + X2 c d) * evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) -
        evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, b)) * (X1 c d + X2 c d) =
      (if d = a then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, c, b)) else 0) -
        (if b = c then evB lev X1 X2 (FreeAlgebra.ι ℂ (s, a, d)) else 0) := by
  obtain ⟨h1, h2, h3⟩ := hX
  simp only [evB, FreeAlgebra.lift_ι_apply]
  by_cases hab : lev a = lev b
  · have e1 : d = a → lev c = lev b := fun h => by rw [hcd, h, hab]
    have e2 : b = c → lev a = lev d := fun h => by rw [hab, h, hcd]
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) =
        if d = a then (if s = true then X1 c b else X2 c b) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e1 h) h'
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) =
        if b = c then (if s = true then X1 a d else X2 a d) else 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd (e2 h) h'
    rw [k1, k2, if_pos hab]
    cases s
    · have e := h2 c d a b hcd hab
      have k := (h3 c d a b hcd hab).eq
      simp only [Bool.false_eq_true, if_false, add_mul, mul_add]
      rw [k, ← e]
      abel
    · have e := h1 c d a b hcd hab
      have k := (h3 a b c d hab hcd).eq
      simp only [if_true, add_mul, mul_add]
      rw [k, ← e]
      abel
  · have e1 : d = a → ¬ lev c = lev b := fun h => by rw [hcd, h]; exact hab
    have e2 : b = c → ¬ lev a = lev d := fun h => by rw [← hcd, ← h]; exact hab
    have k1 : (if d = a then (if lev c = lev b then (if s = true then X1 c b else X2 c b) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e1 h)
    have k2 : (if b = c then (if lev a = lev d then (if s = true then X1 a d else X2 a d) else 0) else 0) = 0 := by
      split_ifs with h h' <;> first | rfl | exact absurd h' (e2 h)
    rw [k1, k2, if_neg hab]
    simp

theorem exists_adFamL (lev : Fin n → ℕ) (a : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFamL lev w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro W _ _ X1 X2 _ c d _ i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Bool × Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.2.1 ∧ j = (i.1, c, i.2.2) then 1 else 0) -
        (if i.2.2 = c ∧ j = (i.1, i.2.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨s, i1, i2⟩ ⟨t, j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3.symm, h2.symm, h1.symm, h4.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h4, h2.symm, h3.symm, h1⟩
    · rintro W _ _ X1 X2 hX c d hcd ⟨s, a, b⟩
      have h := ad_letter hX hcd s a b
      simp only [Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a <;> simp [h1]
      · by_cases h1 : b = c <;> simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro W _ _ X1 X2 hX c d hcd ⟨i, i'⟩
      have e1 := h2 W X1 X2 hX c d hcd i
      have e2 := h2' W X1 X2 hX c d hcd i'
      have : (X1 c d + X2 c d) * evB lev X1 X2 (w i * w' i') - evB lev X1 X2 (w i * w' i') * (X1 c d + X2 c d) =
          ((X1 c d + X2 c d) * evB lev X1 X2 (w i) - evB lev X1 X2 (w i) * (X1 c d + X2 c d)) * evB lev X1 X2 (w' i') +
            evB lev X1 X2 (w i) *
              ((X1 c d + X2 c d) * evB lev X1 X2 (w' i') - evB lev X1 X2 (w' i') * (X1 c d + X2 c d)) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro W _ _ X1 X2 hX c d hcd (i | i)
      · simp [Fintype.sum_sum_type, h2 W X1 X2 hX c d hcd]
      · simp [Fintype.sum_sum_type, h2' W X1 X2 hX c d hcd]
    · simp [Fintype.sum_sum_type]

theorem AdFamL.comm {lev : Fin n → ℕ} {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Bool × Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFamL lev w M) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hX : LRel lev X1 X2) {c d : Fin n} (hcd : lev c = lev d) (t : ι → ℂ) :
    (X1 c d + X2 c d) * evB lev X1 X2 (∑ i, t i • w i) - evB lev X1 X2 (∑ i, t i • w i) * (X1 c d + X2 c d) =
      evB lev X1 X2 (∑ j, (M c d *ᵥ t) j • w j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, h.2 W X1 X2 hX c d hcd, Finset.smul_sum, Matrix.mulVec, dotProduct,
    Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem invL : InvL := by
  classical
  intro n lev V _ _ X1 X2 L a hX hL ha
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFamL lev a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, evB lev X1 X2 (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, lev c = lev d → ∀ x ∈ N, D c d x ∈ N := by
    intro c d hcd x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]
  have ht : ∀ c d, lev c = lev d → D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d hcd
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hX hcd]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, lev c = lev d → D c d t' = 0 := by
    intro c d hcd
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d hcd) (hDN c d hcd k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ Y1 Y2 hY c d hcd
    have := hM.comm hY hcd t'.ofLp
    rw [← hD, h0 c d hcd] at this
    have h2 : evB lev Y1 Y2 (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, this, zero_add]

end GlobalTheory.CompanionTheory.PairMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowQMulOfMemQ
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

namespace GlobalTheory.CompanionTheory.BZPhiPhi

theorem rowQ_mul_of_mem_Q (k : Type) [Field k] (n : ℕ) (q g : Mir k (n + 1)) (hq : q ∈ Q k n) :
    rowQ k n (q * g) = rowQ k n g := by
  have hb : (blockMat k (n + 1) ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)) (Fin.last n) =
      eLast k n := by
    have h := (mem_Mir_iff k (mirabolicProjection k (n + 1) q)).1 hq
    exact h
  have hg : ∀ j : Fin (n + 1), ((g : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.last (n + 1)) (Fin.castSucc j) = 0 := by
    intro j
    have := congrFun ((mem_Mir_iff k (g : GL (Fin (n + 2)) k)).1 g.2) (Fin.castSucc j)
    simpa [eLast, Fin.castSucc_ne_last] using this
  funext j
  have hb' : ∀ l : Fin (n + 1), ((q : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k)
      (Fin.castSucc (Fin.last n)) (Fin.castSucc l) = eLast k n l := fun l => congrFun hb l
  simp only [rowQ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_castSucc (n := n + 1), hg, hb', mul_zero, add_zero]
  simp [eLast, Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactor
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Emb

open GlobalTheory.CompanionTheory.BZPhiPhi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirProj_iotaM (n : ℕ) (y : Mir k n) :
    mirabolicProjection k (n + 1) (embedding₂ k n y) = (y : GL (Fin (n + 1)) k) := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k (n + 1) (GlobalTheory.BZMir.glEmbMat k (n + 1) ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) i j = _
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem iotaM_mem_Q (n : ℕ) (y : Mir k n) : embedding₂ k n y ∈ Q k n := by
  show mirabolicProjection k (n + 1) (embedding₂ k n y) ∈ Mir k n
  rw [mirProj_iotaM]
  exact y.2

theorem mem_mirabolicParabolic_of_iotaM_mem (m j : ℕ) (p : Mir k (m + j))
    (h : embedding₂ k (m + j) p ∈ MirabolicParabolic k m (j + 1)) : p ∈ MirabolicParabolic k m j := by
  have h1 := (GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic k m (j + 1) (embedding₂ k (m + j) p)).1 h
  have e : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) p) = (p : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) p
  rw [e] at h1
  exact h1

theorem mem_mirabolicParabolic_of_mirabolicProj_eq_one (m j : ℕ) (w : Mir k (m + j)) (h : mirabolicProjection k (m + j) w = 1) :
    w ∈ MirabolicParabolic k m j := by
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic, h]
  exact one_mem _

theorem rowQ_eq_zero_of_mem_HGP (m j : ℕ) (h : Mir k (m + (j + 1))) (hh : h ∈ MirabolicParabolic k m (j + 1))
    (i : Fin (m + j + 1)) (hi : (i : ℕ) < m) : rowQ k (m + j) h i = 0 := by
  have h1 := (mem_mirabolicParabolic_iff k m (j + 1) h).1 hh ⟨j, by omega⟩ ⟨i, hi⟩
  have e1 : eGP m (j + 1) ⟨true, ⟨j, by omega⟩⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  have e2 : eGP m (j + 1) ⟨false, ⟨i, hi⟩⟩ = Fin.castSucc i :=
    Fin.ext (by rw [blockIndex_false_val]; simp)
  rw [e1, e2] at h1
  exact h1

theorem rowEl_mem_HGP (m j : ℕ) (r : Fin (m + j + 1) → k) (hr : (rowMat (m + j) r).det ≠ 0)
    (h0 : ∀ i : Fin (m + j + 1), (i : ℕ) < m → r i = 0) :
    (rowEl (m + j) r hr : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  have hb := blockIndex_true_val m (j + 1) b
  have ha := blockIndex_false_val m (j + 1) a
  have hval : (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) = rowMat (m + j) r := rfl
  generalize eGP m (j + 1) ⟨true, b⟩ = p at hb ⊢
  generalize eGP m (j + 1) ⟨false, a⟩ = q at ha ⊢
  show (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) p q = 0
  rw [hval, rowMat]
  by_cases hp : p = Fin.castSucc (Fin.last (m + j))
  · subst hp
    rw [updateRow_self]
    have ham := a.2
    have hq : q = Fin.castSucc (⟨a, by omega⟩ : Fin (m + j + 1)) := Fin.ext (by simpa using ha)
    rw [hq, Fin.lastCases_castSucc]
    exact h0 _ a.2
  · rw [updateRow_ne hp, one_apply_ne]
    intro c
    have := congrArg Fin.val c
    have ham := a.2
    omega

theorem mul_inv_qProj_mem (m j : ℕ) (x : Mir k (m + j)) (h d κ : Mir k (m + (j + 1)))
    (hh : h ∈ MirabolicParabolic k m (j + 1)) (hd : d ∈ MirabolicParabolic k m (j + 1)) (hq : d * κ ∈ Q k (m + j))
    (e : embedding₂ k (m + j) x = h * κ) :
    x * (qProj k (m + j) ⟨d * κ, hq⟩)⁻¹ ∈ MirabolicParabolic k m j := by
  apply mem_mirabolicParabolic_of_iotaM_mem
  set y := qProj k (m + j) ⟨d * κ, hq⟩ with hy
  have e1 : embedding₂ k (m + j) (x * y⁻¹) = (h * d⁻¹) * ((d * κ) * (embedding₂ k (m + j) y)⁻¹) := by
    rw [map_mul, map_inv, e]
    group
  rw [e1]
  refine mul_mem (mul_mem hh (inv_mem hd)) (mem_mirabolicParabolic_of_mirabolicProj_eq_one m (j + 1) _ ?_)
  have e2 : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) y) = (y : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) y
  have e3 : (y : GL (Fin (m + j + 1)) k) = mirabolicProjection k (m + (j + 1)) (d * κ) := rfl
  rw [map_mul, map_inv, e2, e3, mul_inv_cancel]

theorem iotaM_descent (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) :
    ∀ K' ∈ 𝓝 (1 : Mir k (m + j)), ∃ K ∈ 𝓝 (1 : Mir k (m + (j + 1))),
      ∀ x : Mir k (m + j), ∀ h ∈ MirabolicParabolic k m (j + 1), ∀ κ ∈ K, embedding₂ k (m + j) x = h * κ →
        ∃ h' ∈ MirabolicParabolic k m j, ∃ κ' ∈ K', x = h' * κ' := by
  have : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  intro K' hK'
  let r : Mir k (m + j + 1) → Fin (m + j + 1) → k := fun κ => rowQ k (m + j) κ⁻¹
  have hcr : Continuous r := (continuous_rowQ (m + j)).comp continuous_inv
  let O : Set (Mir k (m + j + 1)) := {κ | (rowMat (m + j) (r κ)).det ≠ 0}
  have hO : IsOpen O :=
    isOpen_compl_singleton.preimage ((continuous_rowMat (m + j)).comp hcr).matrix_det
  have hr1 : r 1 = Pi.single (Fin.last (m + j)) 1 := by
    show rowQ k (m + j) 1⁻¹ = _
    rw [inv_one, rowQ_one]
  have hm1 : rowMat (m + j) (r 1) = 1 := by rw [hr1, rowMat_single]
  have h1O : (1 : Mir k (m + j + 1)) ∈ O := by
    show (rowMat (m + j) (r 1)).det ≠ 0
    rw [hm1, det_one]
    exact one_ne_zero
  let d : O → Mir k (m + j + 1) := fun κ => rowEl (m + j) (r κ.1) κ.2
  have hdc : Continuous d :=
    (continuous_rowEl (k := k) (m + j)).comp
      (Continuous.subtype_mk (hcr.comp continuous_subtype_val) fun κ => κ.2)
  have hQ : ∀ κ : O, d κ * κ.1 ∈ Q k (m + j) := fun κ => by
    have := mul_inv_mem_Q_of_rowQ_eq (m + j) (d κ) (κ.1)⁻¹ (rowQ_rowEl (m + j) (r κ.1) κ.2)
    rwa [inv_inv] at this
  let φ : O → Q k (m + j) := fun κ => ⟨d κ * κ.1, hQ κ⟩
  have hφc : Continuous φ := Continuous.subtype_mk (hdc.mul continuous_subtype_val) _
  let ψ : O → Mir k (m + j) := fun κ => qProj k (m + j) (φ κ)
  have hψc : Continuous ψ := (GlobalTheory.CompanionTheory.BZMirOnto.continuous_qProj k (m + j)).comp hφc
  have hd1 : d ⟨1, h1O⟩ = 1 := Subtype.ext (Units.ext hm1)
  have hψ1 : ψ ⟨1, h1O⟩ = 1 := by
    have : φ ⟨1, h1O⟩ = 1 := Subtype.ext (by
      show d ⟨1, h1O⟩ * 1 = 1
      rw [hd1, one_mul])
    show qProj k (m + j) (φ ⟨1, h1O⟩) = 1
    rw [this, map_one]
  have hpre : ψ ⁻¹' K' ∈ 𝓝 (⟨1, h1O⟩ : O) :=
    hψc.continuousAt.preimage_mem_nhds (by rw [hψ1]; exact hK')
  refine ⟨Subtype.val '' (ψ ⁻¹' K'), hO.isOpenMap_subtype_val.image_mem_nhds hpre, ?_⟩
  rintro x h hh _ ⟨κ, hκ, rfl⟩ e
  have hκinv : (κ.1)⁻¹ = embedding₂ k (m + j) x⁻¹ * h := by
    rw [map_inv, e]
    group
  have hrow : r κ.1 = rowQ k (m + j) h := by
    show rowQ k (m + j) (κ.1)⁻¹ = _
    rw [hκinv]
    exact rowQ_mul_of_mem_Q k (m + j) _ h (iotaM_mem_Q (m + j) x⁻¹)
  have hdH : d κ ∈ MirabolicParabolic k m (j + 1) :=
    rowEl_mem_HGP m j (r κ.1) κ.2 fun i hi => by
      rw [hrow]
      exact rowQ_eq_zero_of_mem_HGP m j h hh i hi
  exact ⟨x * (ψ κ)⁻¹, mul_inv_qProj_mem m j x h (d κ) κ.1 hh hdH (hQ κ) e, ψ κ, hκ, by group⟩

end GlobalTheory.CompanionTheory.LeibPhi.Emb

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddedSmallNeighbourhoodFactorStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedded_small_neighbourhood_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), ∀ K' ∈ 𝓝 (1 : Mir k (m + j)), ∃ K ∈ 𝓝 (1 : Mir k (m + (j + 1))),
    ∀ x : Mir k (m + j), ∀ h ∈ MirabolicParabolic k m (j + 1), ∀ κ ∈ K, embedding₂ k (m + j) x = h * κ →
      ∃ h' ∈ MirabolicParabolic k m j, ∃ κ' ∈ K', x = h' * κ' := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent | exact GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Emb.iotaM_descent <;> assumption)
end
end
