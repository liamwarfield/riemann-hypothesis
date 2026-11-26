module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieProj

theorem lie_finite_projective_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), Module.Finite R L ∧ Module.Projective R L ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L'] [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →ₗ[R] L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → IsBaseChange R' β :=
  @PositivityTheory.HtPt.Htat.lie_proj

end GlobalTheory.CompanionTheory.Ar.LieProj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_finite_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), Module.Finite R L ∧ Module.Projective R L ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L'] [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →ₗ[R] L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → IsBaseChange R' β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange | exact GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

section Block

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def blkV (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) : (Σ k, J₀ k) → Σ k, J k :=
  fun p => ⟨bk p.1, bx p.1 p.2⟩

theorem isBlockMap_blkV {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) (h : Function.Injective bk) :
    IsBlockMap bk (blkV bk bx) := by
  refine ⟨h, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, a⟩ ⟨k', a'⟩ e
    have e1 : bk k = bk k' := congrArg Sigma.fst e
    obtain rfl := h e1
    have e2 : bx k a = bx k a' := by simpa [blkV] using e
    rw [(bx k).injective e2]
  · rintro ⟨_, a⟩ ⟨k, rfl⟩
    exact ⟨⟨k, (bx k).symm a⟩, by simp [blkV]⟩

variable {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}

def restr (v : (Σ k, J₀ k) → Σ k, J k) : ((Σ k, J k) → ℂ) →L[ℝ] ((Σ k, J₀ k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Σ k, J k => ℂ) (v p)

theorem restr_ne (hv : IsBlockMap κ v) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K₀) :
    ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem isSmoothHerm_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsSmoothHerm A) :
    IsSmoothHerm (pullHerm hv A) := by
  have h := ContDiffOn.comp (s := {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA
    (restr v).contDiff.contDiffOn (fun z hz => restr_ne hv hz)
  exact h

theorem isConj_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsConjInvariantH A) :
    IsConjInvariantH (pullHerm hv A) := fun z => hA fun p => z (v p)

theorem isConj_tensor {A B : HermLine J} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B) :
    IsConjInvariantH (A.tensor B) := fun z => by
  show A.h _ * B.h _ = A.h _ * B.h _
  rw [hA, hB]

theorem mCoordIdeal_le_imageZ {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) {y₀ : (Σ k, J₀ k) → Ω₀}
    {y : (Σ k, J k) → Ω} {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k))
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) :
    mCoordIdeal y₀ ≤ imageZ (blkV bk bx) (mCoordIdeal y) := by
  intro f hf
  let Φ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp i) fun k => MvPolynomial.X (bk k)
  have key : ∀ f : MRing J₀, mConeMap y (rename (blkV bk bx) f) = Φ (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap, Φ]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      obtain ⟨k, a⟩ := n
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, Φ, blkV, hy]
  have hf' : mConeMap y₀ f = 0 := hf
  show mConeMap y (rename (blkV bk bx) f) = 0
  rw [key, hf', map_zero]

theorem mem_mcPts_restr (hv : IsBlockMap κ v) {P₀ : Ideal (MRing J₀)} {P : Ideal (MRing J)}
    (hP : P₀ ≤ imageZ v P) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) : (fun p => z (v p)) ∈ mcPts P₀ := by
  refine ⟨restr_ne hv hz.1, fun f hf => ?_⟩
  have := hz.2 _ (hP hf)
  have e : (rename v : MRing J₀ →ₐ[ℤ] MRing J).toRingHom f = rename v f := rfl
  rw [e, map_rename, eval_rename] at this
  exact this

end Block

section Lines

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have h1 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)) (A.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (h1 k)), add_comm]
  simp only [Real.log_zpow]

theorem prod_zpow_sum {R : Type} [Field R] {X : Type} (s : Finset X) {r : R} (hr : r ≠ 0) (a : X → ℤ) :
    ∏ x ∈ s, r ^ a x = r ^ ∑ x ∈ s, a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, zpow_add₀ hr, ih]

def stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) : HermLine J where
  a := fun k => -∑ x ∈ Finset.Iic i, (T x).a k
  h z := ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹
  pos z hz := Finset.prod_pos fun x _ => inv_pos.2 ((T x).pos z hz)
  smul c z hc := by
    have h1 : ∀ k, (‖c k‖ : ℝ) ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    simp only [(T _).smul c z hc, mul_inv, Finset.prod_mul_distrib]
    congr 1
    simp only [← Finset.prod_inv_distrib]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg, ← prod_zpow_sum _ (h1 k), Finset.prod_inv_distrib]

theorem log_stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) :
    Real.log ((stepLine T i).h z) = -∑ x ∈ Finset.Iic i, Real.log ((T x).h z) := by
  show Real.log (∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) = _
  rw [Real.log_prod fun x _ => inv_ne_zero ((T x).pos z hz).ne']
  simp only [Real.log_inv, Finset.sum_neg_distrib]

theorem isSmoothHerm_stepLine {N : ℕ} {T : Fin N → HermLine J} (hT : ∀ x, IsSmoothHerm (T x)) (i : Fin N) :
    IsSmoothHerm (stepLine T i) := by
  show ContDiffOn ℝ _ (fun z => ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) _
  exact contDiffOn_prod fun x _ => (hT x).inv fun z hz => ((T x).pos z hz).ne'

def corr {Ψ : Type} {N : ℕ} (T : Ψ × Fin N → HermLine J) : Option (Ψ × Fin N) → HermLine J
  | none => Top.trivLine J
  | some r => stepLine (fun k => T (r.1, k)) r.2

theorem isSmoothHerm_trivLine : IsSmoothHerm (Top.trivLine J) := contDiffOn_const

theorem isSmoothHerm_corr {Ψ : Type} {N : ℕ} {T : Ψ × Fin N → HermLine J} (hT : ∀ r, IsSmoothHerm (T r))
    (a : Option (Ψ × Fin N)) : IsSmoothHerm (corr T a) := by
  cases a with
  | none => exact isSmoothHerm_trivLine
  | some r => exact isSmoothHerm_stepLine (fun k => hT (r.1, k)) r.2

def IsFlatOn {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (T : HermLine J) : Prop :=
  PB.SamePot R.A Set.univ (potOf R T) (ReciprocityTheory.AnForm.M.LocPot.ofFun 0)

def withTop {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (hP : ¬ (⊤ : Ideal (MRing J)) ≤ P)
    (hE : Cmp.IsEmbedded R.A P R.U R.lift) : AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hP
  X := R.X
  A := R.A
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  lift := R.lift
  holo := R.holo
  mem := R.mem
  compat := R.compat
  surj z hz _ := hE.surj z hz
  inj x x' _ h := hE.inj x x' h
  immersion x _ p hp j hj := hE.immersion x p hp j hj
  snc f a hf hh hz := R.snc f a hf hh fun z hz' h0 => by
    have h1 := (hz z hz' h0).2 1 trivial
    simp at h1
  null j := by
    have : {x | R.lift x x ∈ mcPts (⊤ : Ideal (MRing J))} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have h1 := h.2 1 trivial
      simp at h1
    rw [this]
    simp

end Lines

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

def pushCpt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀} {i : Ω₀ →+* Ω}
    (hd : Dominates ξ ξ₀ h i) (p : Cpt ξ) : Cpt ξ₀ := ⟨h p.1, hd.specializes p⟩

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def IsRatio (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (bk : K₀ → K)
    (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀)
    (φ : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w →
    ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) →
      ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u ∧
        φ w * ∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k

end Points

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

def IsCovOf (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i ∧ 𝔐.f = h ≫ 𝔐₀.f ∧ 𝔐.cst = i.comp 𝔐₀.cst

def FlagsOver {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) : Prop :=
  ∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ

def GenPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) {h : 𝔐.X ⟶ 𝔐₀.X}
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) : Prop :=
  ∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s (a : Fin (labelRk D s)) (t₀ : Ω₀),
    ((𝔐₀.V s).gr (Fl₀.b s) a).IsGenAt (pushCpt hd q) t₀ → ((𝔐.V s).gr (Fl.b s) a).IsGenAt q (i t₀)

def NormPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω)
    (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) s (a : Fin (labelRk D s)) (t₀ : Ω₀) (ν : ℝ),
    𝔐₀.M.IsGrNorm 𝔐₀.t.PP.L (𝔐₀.V s) (Fl₀.b s) a (z ≫ h) t₀ ν →
      𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) a z (i t₀) ν

end Cover

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsAction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Bridge

theorem comb_eig_frame : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ :=
  @PositivityTheory.Xgf.lie_model_eigenvectors_action

end GlobalTheory.CompanionTheory.Ar.Fl.Bridge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_eigenvectors_action : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame | exact GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_spec {a : Ω} {r : R} (h : ValAt ξ z a r) : ∃ hz : genPt ξ ⤳ centre z, a ∈ regAt ξ ⟨centre z, hz⟩ := by
  obtain ⟨hz, s, hs, -⟩ := h
  exact ⟨hz, s, hs⟩

theorem val_exists {a : Ω} {hz : genPt ξ ⤳ centre z} (h : a ∈ regAt ξ ⟨centre z, hz⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, hz, s, hs, rfl⟩

theorem val_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, hs, rfl⟩ := h
  obtain ⟨hz', s', hs', rfl⟩ := h'
  have : s = s' := hξ.inj ⟨centre z, hz⟩ (hs.trans hs'.symm)
  rw [this]

theorem val_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t * t', by rw [map_mul, ht]; rw [← ht'], map_mul _ _ _⟩

theorem val_add {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t + t', by rw [map_add (f := _), ht]; rw [← ht'], map_add _ _ _⟩

theorem val_nat (hz : genPt ξ ⤳ centre z) (n : ℕ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩

theorem val_one (hz : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 1

theorem val_zero (hz : genPt ξ ⤳ centre z) : ValAt ξ z (0 : Ω) (0 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 0

theorem val_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : ValAt ξ z a⁻¹ (↑r⁻¹ : R) := by
  obtain ⟨hz, s, hs, hr⟩ := h
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (hr ▸ r.isUnit)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · rw [← hs, map_units_inv]
  · have : (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom u) = r := Units.ext hr
    rw [← this]
    exact congrArg Units.val (map_inv (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom) u)

theorem val_ne_zero (hξ : IsCptGen ξ) [Nontrivial R] {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 := by
  rintro rfl
  obtain ⟨hz, -⟩ := val_spec h
  have := val_unique hξ h (val_zero hz)
  exact r.ne_zero this

theorem val_inv₀ {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) :
    ValAt ξ z a⁻¹ r⁻¹ := by
  have := val_inv (r := Units.mk0 r hr) h
  simpa using this

theorem val_zpow {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, -⟩ := val_spec h
  have hp : ∀ k : ℕ, ∀ {b : Ω} {s : F}, ValAt ξ z b s → ValAt ξ z (b ^ k) (s ^ k) := by
    intro k b s hb
    induction k with
    | zero => simpa using val_one hz
    | succ k ih => rw [pow_succ, pow_succ]; exact val_mul ih hb
  rcases n with k | k
  · simpa using hp k h
  · simpa [zpow_negSucc] using val_inv₀ (pow_ne_zero _ hr) (hp (k + 1) h)

theorem in_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
  have h1 := fun k => hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (h1 k).1, fun c' => ?_⟩
  simp only
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (h1 k).2 (c' k)
  obtain ⟨hz', s, hs, -⟩ := hr
  exact ⟨s, hs⟩

theorem coordsAt_smul {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (hw : CoordsAt ξ y z w) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k c' hu => ?_⟩
  · obtain ⟨c', h'⟩ := hw.1 k
    exact ⟨c', (isUnit_iff_ne_zero.2 (hc k)).mul h'⟩
  · have hu' : IsUnit (w ⟨k, c'⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hu.ne_zero)
    obtain ⟨h1, h2⟩ := hw.2 k c' hu'
    refine ⟨h1, fun i => ?_⟩
    obtain ⟨r, hr, hr'⟩ := h2 i
    refine ⟨r, hr, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, c'⟩)
    rw [hr']; ring

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCount

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem emb_ext {τ τ' : E →+* ℂ} (h : ∀ a : 𝓞 E, τ (a : E) = τ' (a : E)) : τ = τ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
  exact rt0_ne_zero H ((mul_eq_zero.mp h2).resolve_left two_ne_zero)

theorem labelEmb_injective (c : Coeff l) : Function.Injective (labelEmb (H := H) c) := by
  have val : ∀ {s t : CMType H ⊕ CMType H}, labelEmb c s = labelEmb c t → ∀ a : 𝓞 E,
      ((labelEmb c s a : c.F) : ℂ) = ((labelEmb c t a : c.F) : ℂ) := fun h a => by rw [h]
  rintro (τ | τ) (τ' | τ') h
  · refine congrArg Sum.inl (Subtype.ext (emb_ext fun a => val h a))
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ).symm.trans
      ((val h H.rt).trans (HodgeCptTest.labelEmb_inr_rt c τ'))) (rt0_ne_neg H)
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ').symm.trans
      ((val h H.rt).symm.trans (HodgeCptTest.labelEmb_inr_rt c τ))) (rt0_ne_neg H)
  · refine congrArg Sum.inr (Subtype.ext (emb_ext fun a => ?_))
    have := val h (H.bar.symm a)
    simpa [labelEmb] using this

def labelCx (H : Host E) : CMType H ⊕ CMType H → (E →+* ℂ) :=
  Sum.elim (fun τ => τ.1) (fun τ => (starRingEnd ℂ).comp τ.1)

theorem labelCx_bijective (H : Host E) : Function.Bijective (labelCx H) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1 (rt0_ne_neg H)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1.symm (rt0_ne_neg H)
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      exact (starRingEnd ℂ).injective (RingHom.congr_fun h x)
  · intro σ
    have hsq : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have hrt : σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hsq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hrt with hp | hm
    · exact ⟨.inl ⟨σ, hp⟩, rfl⟩
    · have ht : ((starRingEnd ℂ).comp σ) (H.rt : E) = H.rt0 := by
        simp [hm, HodgeCptTest.imaginary_root_conj]
      refine ⟨.inr ⟨(starRingEnd ℂ).comp σ, ht⟩, RingHom.ext fun x => ?_⟩
      simp [labelCx]

theorem labels_injective_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) [Fintype (CMType H)] (Ω : Type) [Field Ω] (cst : c.F →+* Ω),
    Function.Injective (fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)) ∧
      Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c _ Ω _ cst
  refine ⟨fun s t h => labelEmb_injective c (RingHom.ext fun a => cst.injective (RingHom.congr_fun h a)), ?_⟩
  rw [Fintype.card_of_bijective (labelCx_bijective H), NumberField.Embeddings.card]

end GlobalTheory.CompanionTheory.Ar.LabelCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicative
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicative
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusPoints

theorem charVal_eq_diag {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A] {a : Sp A ⟶ S}
    (t : Over.mk a ⟶ splitTorus S X) (χ : X) : charVal t χ = GlobalTheory.Diag.charVal t χ := by
  rw [GlobalTheory.Diag.charVal_eq_torusFst]
  rfl

theorem main : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] (a : Sp A ⟶ S), (∀ t t' : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = charVal t' χ) → t = t') ∧ (∀ (t t' : Over.mk a ⟶ splitTorus S X) (χ : X), charVal (t * t') χ = charVal t χ * charVal t' χ) ∧ (∀ χ : X, charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1) ∧ (∀ (t : Over.mk a ⟶ splitTorus S X), charVal t 0 = 1 ∧ ∀ χ χ', charVal t (χ + χ') = charVal t χ * charVal t χ') ∧ (∀ w : Multiplicative X →* A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = w (Multiplicative.ofAdd χ)) ∧ ∀ (A' : Type) [CommRing A'] (g : A →+* A') (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk (spMap g ≫ a) ⟶ splitTorus S X), t'.left = spMap g ≫ t.left → ∀ χ, charVal t' χ = g (charVal t χ) := by
  intro S X _ A _ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' h
    refine GlobalTheory.Diag.charVal_ext fun χ => ?_
    rw [← charVal_eq_diag, ← charVal_eq_diag]
    exact h χ
  · intro t t' χ
    rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_mul]
  · intro χ
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_one]
  · intro t
    refine ⟨?_, fun χ χ' => ?_⟩
    · rw [charVal_eq_diag, GlobalTheory.Diag.charVal_zero]
    · rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_add]
  · intro w
    refine ⟨GlobalTheory.Diag.ofVal a w, fun χ => ?_⟩
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_ofVal]
  · intro A' _ g t t' ht χ
    rw [charVal_eq_diag, charVal_eq_diag]
    exact (GlobalTheory.Diag.left_eq_iff g rfl t' t).1 ht χ

end GlobalTheory.CompanionTheory.Ar.TorusPoints
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharValMultiplicativeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charVal_multiplicative : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] (a : Sp A ⟶ S), (∀ t t' : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = charVal t' χ) → t = t') ∧ (∀ (t t' : Over.mk a ⟶ splitTorus S X) (χ : X), charVal (t * t') χ = charVal t χ * charVal t' χ) ∧ (∀ χ : X, charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1) ∧ (∀ (t : Over.mk a ⟶ splitTorus S X), charVal t 0 = 1 ∧ ∀ χ χ', charVal t (χ + χ') = charVal t χ * charVal t χ') ∧ (∀ w : Multiplicative X →* A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = w (Multiplicative.ofAdd χ)) ∧ ∀ (A' : Type) [CommRing A'] (g : A →+* A') (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk (spMap g ≫ a) ⟶ splitTorus S X), t'.left = spMap g ≫ t.left → ∀ χ, charVal t' χ = g (charVal t χ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusPoints.main | exact GlobalTheory.CompanionTheory.Ar.TorusPoints.main | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusPoints.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabLie

theorem lieModel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (V : Type) [AddCommGroup V] [Module R V] (M : LieModel t'.G x V), ∃ Mf : LieModel t.G (x ≫ f) V, ∀ e, (Mf.pt e).left = (M.pt e).left ≫ m.φ := by
  intro E _ _ _ H S S' t' t f m R _ x V _ _ M
  obtain ⟨Mf, h⟩ := (LiePull.lieModel_pullback S S' t.G t'.G f m.φ m.cart R x V).2 M
  exact ⟨Mf, fun e => (h e).symm⟩

end GlobalTheory.CompanionTheory.Ar.SabLie
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_push_along_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (V : Type) [AddCommGroup V] [Module R V] (M : LieModel t'.G x V), ∃ Mf : LieModel t.G (x ≫ f) V, ∀ e, (Mf.pt e).left = (M.pt e).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap | exact GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap | (intros; apply GlobalTheory.CompanionTheory.Ar.SabLie.lieModel_of_sabMap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L L' : Type} [Field L] [Field L']

theorem centre_field (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) = centre z := by
  show z (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint L')) = z (IsLocalRing.closedPoint L)
  exact congrArg z (Subsingleton.elim _ _)

theorem centre_specializes (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) ⤳ centre z :=
  specializes_of_eq (centre_field ψ z)


set_option backward.isDefEq.respectTransparency false in
theorem stalk_comp (ψ : L →+* L') (z : Sp L ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫ Scheme.stalkClosedPointTo (spMap ψ ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (spMap ψ ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_field {ξ : Sp Ω ⟶ X} (ψ : L →+* L') {z : Sp L ⟶ X} {a : Ω} {r : L}
    (h : ValAt ξ z a r) : ValAt ξ (spMap ψ ≫ z) a (ψ r) := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  have h' : genPt ξ ⤳ centre (spMap ψ ≫ z) := by rw [centre_field]; exact h1
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalk_comp ψ z)

theorem coordsAt_field {ξ : Sp Ω ⟶ X} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (ψ : L →+* L')
    {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (h : CoordsAt ξ y z w) :
    CoordsAt ξ y (spMap ψ ≫ z) fun p => ψ (w p) := by
  refine ⟨fun k => (h.1 k).imp fun c hc => hc.map ψ, fun k c hc => ?_⟩
  have hc' : IsUnit (w ⟨k, c⟩) := by
    rw [isUnit_iff_ne_zero] at hc ⊢
    exact fun h0 => hc (by simp [h0])
  refine ⟨(h.2 k c hc').1, fun i => ?_⟩
  obtain ⟨r, hr, e⟩ := (h.2 k c hc').2 i
  exact ⟨ψ r, valAt_field ψ hr, by simp only [e, map_mul]⟩

theorem coordsAt_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ),
    CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w →
    CoordsAt ξ y (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (fun p => σ (w p)) := by
  intro X Ω _ ξ K J y L _ _ w z σ h
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [e]
  exact coordsAt_field σ h

end GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtComplexEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_at_complex_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ),
    CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w →
    CoordsAt ξ y (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (fun p => σ (w p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding | exact GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords.coordsAt_embedding <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

theorem cls_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p →
    ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (κ : Ω), (∀ n : ℕ, flagStep Ω b n = flagStep Ω b₀ n) ∧
      V.IsFrameAt b p ∧ (∀ j, (m : Ω) • b j ∈ M.lat p) ∧ (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      (∀ j, ∀ e ∈ M.lat p, (m : Ω) * π j e ∈ regAt ξ p) ∧ κ ≠ 0 ∧ κ ∈ regAt ξ p ∧ κ⁻¹ ∈ regAt ξ p ∧
      ∀ (e : Li) (t : Ω), e ∈ flagStep Ω b₀ (i + 1) → IsCls b₀ i e t → t / gen y a e₀ c = π i e * κ := by
  intro X Ω _ ξ K _ J y G _ Li _ _ M V r b₀ m i a e₀ _hb₀ hS hD p c hc
  obtain ⟨b, π, hf, hfr, hm, hπ, hr⟩ := hS p

  have hker : flagStep Ω b₀ i ≤ LinearMap.ker (π i) := by
    rw [← hf]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := by
      rintro rfl
      simp at hk
    simp [hπ, hne]
  have hkill : ∀ (e : Li) (t : Ω), e - t • b₀ i ∈ flagStep Ω b₀ i → π i e = t * π i (b₀ i) := by
    intro e t h
    have h1 : π i (e - t • b₀ i) = 0 := hker h
    simpa [sub_eq_zero] using h1

  have hbi : b i ∈ flagStep Ω b₀ (i + 1) := by
    rw [← hf]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [Flag.step_succ] at hbi
  obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hbi
  obtain ⟨u', rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hone : u' * π i (b₀ i) = 1 := by
    have h1 : π i (b i) = 1 := by simp [hπ]
    have h2 : π i z = 0 := hker hz
    rw [← hzw] at h1
    simpa [h2] using h1
  have hu' : u' ≠ 0 := left_ne_zero_of_mul_eq_one hone
  have hw0 : π i (b₀ i) ≠ 0 := right_ne_zero_of_mul_eq_one hone
  have hcls : b i - u' • b₀ i ∈ flagStep Ω b₀ i := by
    have : b i - u' • b₀ i = z := by rw [← hzw]; abel
    rw [this]; exact hz

  have hreg : ∀ e ∈ V p, π i e ∈ regAt ξ p := by
    intro e he
    rw [hfr.2] at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hπ]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul s x _ hx =>
      have : π i (s • x) = (s : Ω) * π i x := (π i).map_smul (s : Ω) x
      rw [this]
      exact mul_mem s.2 hx

  have hgen : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {u'} := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro s ⟨e, he, hs⟩
      have h1 := hkill e s hs
      refine Submodule.mem_span_singleton.2 ⟨⟨π i e, hreg e he⟩, ?_⟩
      show π i e * u' = s
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    · rintro _ rfl
      exact ⟨b i, by rw [hfr.2]; exact Submodule.subset_span ⟨i, rfl⟩, hcls⟩
  have hdeg : (V.gr b₀ i) p = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    have := hD.2 p (Set.mem_univ p) c hc
    rw [this]
    rfl
  have hspan : Submodule.span (regAt ξ p) {u'} = Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hgen, hdeg]
  have a1 : u' ∈ Submodule.span (regAt ξ p) {gen y a e₀ c} := by
    rw [← hspan]; exact Submodule.mem_span_singleton_self _
  have a2 : gen y a e₀ c ∈ Submodule.span (regAt ξ p) {u'} := by
    rw [hspan]; exact Submodule.mem_span_singleton_self _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 a2
  have hα' : (α : Ω) * gen y a e₀ c = u' := hα
  have hβ' : (β : Ω) * u' = gen y a e₀ c := hβ
  have hg0 : gen y a e₀ c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hα'
    exact hu' hα'.symm
  have hκ : u' / gen y a e₀ c = α := by
    rw [← hα']; field_simp
  have hκi : (u' / gen y a e₀ c)⁻¹ = β := by
    rw [inv_div, ← hβ']; field_simp
  refine ⟨b, π, u' / gen y a e₀ c, hf, hfr, hm, hπ, hr, div_ne_zero hu' hg0, ?_, ?_, ?_⟩
  · rw [hκ]; exact α.2
  · rw [hκi]; exact β.2
  · intro e t _ hcl
    have h1 := hkill e t hcl
    have h2 : t = π i e * u' := by
      rw [h1, _root_.mul_assoc, mul_comm (π i (b₀ i)), hone, _root_.mul_one]
    rw [h2, mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_graded_sandwich_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p →
    ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (κ : Ω), (∀ n : ℕ, flagStep Ω b n = flagStep Ω b₀ n) ∧
      V.IsFrameAt b p ∧ (∀ j, (m : Ω) • b j ∈ M.lat p) ∧ (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      (∀ j, ∀ e ∈ M.lat p, (m : Ω) * π j e ∈ regAt ξ p) ∧ κ ≠ 0 ∧ κ ∈ regAt ξ p ∧ κ⁻¹ ∈ regAt ξ p ∧
      ∀ (e : Li) (t : Ω), e ∈ flagStep Ω b₀ (i + 1) → IsCls b₀ i e t → t / gen y a e₀ c = π i e * κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame | exact GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt


open scoped ComplexOrder in
theorem gramDet_ne_zero_of_linearIndependent :
    ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (f : Fin n → B.carrier), LinearIndependent (𝓞 L) f → B.gramDet σ f ≠ 0 := by
  intro L _ _ B σ n f hf
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec B.metric σ (f i)) =
      Matrix.of fun i j ↦ (B.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f j) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hf)).det_pos
  rw [hG] at hp
  exact hp.ne'

end GlobalTheory.CompanionTheory.Ar.RootHt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramDetNeZeroOfIndepStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_ne_zero_of_indep : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (f : Fin n → B.carrier), LinearIndependent (𝓞 L) f → B.gramDet σ f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.gramDet_ne_zero_of_linearIndependent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Flat.KonstReg

theorem exists_const_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ g₀ : c.F →+* 𝔐.X.presheaf.stalk p.1, (genMap 𝔐.ξ p).comp g₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 p hunit
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hs : 𝔐.ξ ≫ (𝔐.f ≫ Y.s) = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) Ω)) := 𝔐.cst_over
  let h : 𝓞 c.F →+* 𝔐.X.presheaf.stalk p.1 :=
    (𝔐.X.presheaf.germ ⊤ p.1 trivial).hom.comp
      ((𝔐.f ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom)
  have hgen : ∀ o : 𝓞 c.F, genMap 𝔐.ξ p (h o) = 𝔐.cst (algebraMap (𝓞 c.F) c.F o) :=
    fun o => Flat.ConstReg.genMap_germ_const 𝔐.ξ (𝔐.f ≫ Y.s) hs p o
  have hu : ∀ o : 𝓞 c.F, o ≠ 0 → IsUnit (h o) := by
    intro o ho
    have hI : (Ideal.span {o}).comap (algebraMap ℤ (𝓞 c.F)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ho (Ideal.mem_span_singleton_self o) (Algebra.IsIntegral.isIntegral o)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
    have hnat : IsUnit ((n.natAbs : ℕ) : 𝔐.X.presheaf.stalk p.1) := hunit _ (Int.natAbs_ne_zero.mpr hn0)
    have hint : IsUnit (h (algebraMap ℤ (𝓞 c.F) n)) := by
      rw [eq_intCast (algebraMap ℤ (𝓞 c.F)), map_intCast]
      rcases Int.natAbs_eq n with hn' | hn'
      · rw [hn']
        simpa using hnat
      · rw [hn']
        simpa using hnat
    exact isUnit_of_dvd_unit (map_dvd h hn) hint
  refine ⟨IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F)
    (fun z => hu z.1 (nonZeroDivisors.ne_zero z.2)), ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F))
  ext o
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  exact hgen o

end GlobalTheory.CompanionTheory.Ar.Flat.KonstReg
end
