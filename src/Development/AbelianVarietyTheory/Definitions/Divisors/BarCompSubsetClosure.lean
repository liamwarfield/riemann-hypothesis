module

public import Development.AbelianVarietyTheory.Definitions.Foundations.TableDegreeElevenProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsDominantWeightFiniteDimensional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsResolProjSpace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.ChowHt
open GlobalTheory.Adelic GlobalTheory.HilbertSamuel
open scoped Matrix ComplexOrder

variable {F : Type} [Field F] [NumberField F]

section Frame

variable {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]

structure LatFrame (Nm : (F →+* ℂ) → V → ℝ) (M : Submodule (𝓞 F) V) where

  N : ℕ

  n : ℕ

  b : Module.Basis (Fin N) F V

  w : Matrix (Fin N) (Fin n) F

  A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ

  isFrame : CompHt.IsFrame Nm M b w A

namespace LatFrame

variable {Nm : (F →+* ℂ) → V → ℝ} {M : Submodule (𝓞 F) V} (f : LatFrame Nm M)

def gram (σ : F →+* ℂ) : Matrix (Fin f.N) (Fin f.N) ℂ := (f.A σ)⁻¹ᴴ * (f.A σ)⁻¹

theorem posDef_gram (σ : F →+* ℂ) : (f.gram σ).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2
    (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 (f.isFrame.herm σ).isUnit)))

theorem form_gram (σ : F →+* ℂ) (x : Fin f.N → ℂ) :
    star x ⬝ᵥ f.gram σ *ᵥ x = ((frameNorm (f.A σ) x ^ 2 : ℝ) : ℂ) := by
  rw [frameNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), gram, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp [dotProduct, Complex.conj_mul']

def fam : HermFam F V := ofGram f.b f.gram f.posDef_gram

theorem nrm_fam (σ : F →+* ℂ) (x : V) : f.fam.nrm σ x = Nm σ x := by
  rw [← f.isFrame.norm σ x]
  exact (congrArg (fun z : ℂ => Real.sqrt z.re) (f.form_gram σ _)).trans
    (by rw [Complex.ofReal_re]; exact Real.sqrt_sq (Real.sqrt_nonneg _))

theorem isConjInv_fam : f.fam.IsConjInv := isConjInv_ofGram _ _ fun σ i j => by
  let P := f.gram (ComplexEmbedding.conjugate σ) - (f.gram σ).map (starRingEnd ℂ)
  have h₀ : ∀ y, star y ⬝ᵥ P *ᵥ y = 0 := fun y => by
    have e : star y ⬝ᵥ (f.gram σ).map (starRingEnd ℂ) *ᵥ y =
        starRingEnd ℂ (star (star y) ⬝ᵥ f.gram σ *ᵥ star y) := by
      simp [dotProduct, Matrix.mulVec]
    have c := f.isFrame.conj σ (star y)
    simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj] at c
    rw [Matrix.sub_mulVec, dotProduct_sub, e, f.form_gram, f.form_gram, Complex.conj_ofReal, ← c]
    exact sub_self _
  have h₁ : P.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((f.posDef_gram _).1.sub ((f.posDef_gram σ).1.map _ fun _ => rfl)) fun y => (h₀ y).ge
  have := congrFun (h₁.dotProduct_mulVec_zero_iff.1 (h₀ (Pi.single j 1))) i
  simpa [P, sub_eq_zero] using this


include f in
theorem isFull [IsScalarTower (𝓞 F) F V] : IsFull M := by
  refine ⟨f.isFrame.span ▸ Submodule.fg_span (Set.finite_range _), top_le_iff.1 fun x _ => ?_⟩
  have h : f.b.equivFun x ∈ Submodule.span F (Set.range f.w.col) := f.isFrame.full ▸ trivial
  rw [← f.b.equivFun.symm_apply_apply x]
  refine Submodule.span_le.2 ?_ (Submodule.apply_mem_span_image_of_mem_span f.b.equivFun.symm.toLinearMap h)
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact Submodule.subset_span (f.isFrame.span.le (Submodule.subset_span ⟨k, (f.b.equivFun_symm_apply _).symm⟩))

end LatFrame

end Frame

section Moving

variable {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ} {B : LB Y}


omit [NumberField F] in
theorem restr_pull (hB : B.IsLB) {T : Scheme.{0}} (r : T ⟶ Y) {O O' : T.Opens} (h : O ≤ r ⁻¹ᵁ U) (h' : O' ≤ O)
    (f : H0 p B U) : restr h' (H0.pull r h f) = H0.pull r (h'.trans h) f :=
  ext_germ fun z hz => (exists_chart (LB.isLB_pull hB r) z).imp fun i hi => ⟨hi,
    by
    rw [germ_restr, germ_pull, germ_pull]⟩

def NoBase (hB : B.IsLB) (W : Submodule F (H0 p B ⊤)) (U : Y.Opens) : Prop := ∀ y ∈ U, y ∉ (baseIdeal hB W).support

namespace Modif

variable (M : Modif p U D)

def bd : Closeds M.X := M.opn.compl

def off : M.X.Opens := M.bd.compl

theorem off_eq : M.off = M.σ ⁻¹ᵁ U := Opens.compl_compl _

def pullOff : H0 p B U →ₗ[F] H0 M.str (B.pull M.σ) M.off := H0.pull M.σ M.off_eq.le

theorem bijective_pullOff (hB : B.IsLB) : Function.Bijective (M.pullOff (B := B)) :=
  have := M.iso
  (isoOver_of_isIso M.σ).bijective_pull hB _ M.off_eq.ge

def K : CanonLB M.str D := CanonLB.all _ _

variable {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (Δ : Cartier ((baseIdeal hB W).comap M.σ))

theorem notMem_support (h : NoBase hB W U) : ∀ z ∈ M.off, z ∉ ((baseIdeal hB W).comap M.σ).support := fun z hz => by
  rw [Scheme.IdealSheafData.support_comap]
  exact h _ (M.off_eq.le hz)

theorem lift_injective [IsReduced Y] (hU : Dense (U : Set Y)) : Function.Injective Δ.lift := fun w w' e => by
  refine Subtype.ext (restr_injective_of_dense le_top hU ((M.bijective_pull hB).1 ?_))
  have := congrArg (fun s => restr (le_top : M.opn ≤ ⊤) (Δ.incl ⊤ s)) e
  simp only [Δ.incl_lift] at this
  exact (pull_restr _ _ _ _).trans ((restr_pull hB _ _ _ _).symm.trans
    (this.trans ((restr_pull hB _ _ _ _).trans (pull_restr _ _ _ _).symm)))

variable {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V}
  (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt)

def basisSec (j : Fin f.N) : Δ.moving.Sec := toSec (Δ.lift (φ (f.b j)))

abbrev sys (abelian₂ : ℝ) : HermSys F where
  Y := M.X
  str := M.str
  D := D
  L := Δ.moving
  isLB := Δ.isLB_moving
  N := f.N
  b := M.basisSec Δ φ f
  n := f.n
  w := f.w
  A := f.A
  abelian₂ := abelian₂

theorem ofSec_comb (abelian₂ : ℝ) (u : Fin f.N → F) :
    H0.ofSec M.str ⊤ ((M.sys Δ φ f abelian₂).comb u) = Δ.lift (φ (f.b.equivFun.symm u)) := by
  refine (LinSys.ofSec_comb (M.sys Δ φ f abelian₂).toLinSys ⊤ u).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.b.equivFun_symm_apply, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul]; exact congrArg _ (ofSec_toSec _)

theorem isAlgebraicData [IsReduced Y] (hU : Dense (U : Set Y)) (hc : GeometricallyConnected M.str) (hD : 1 ≤ D)
    (abelian₂ : ℝ) : (M.sys Δ φ f abelian₂).IsAlgebraicData := by
  refine ⟨⟨M.smooth, M.proj, hc, hD⟩, fun u hu => ?_, f.isFrame.full, Δ.iSup_nonzeroLocus ?_⟩
  · have := M.ofSec_comb Δ φ f abelian₂ u
    rw [hu, map_zero] at this
    exact f.b.equivFun.symm.map_eq_zero_iff.1 (φ.map_eq_zero_iff.1
      (M.lift_injective Δ hU (this.symm.trans (map_zero _).symm)))
  · exact (f.b.map φ).span_eq

theorem bd_ne_top (hc : GeometricallyConnected M.str) : M.bd ≠ ⊤ := fun e => by
  have : ConnectedSpace M.X := GeometricallyConnected.connectedSpace_of_subsingleton M.str
  obtain ⟨z, hz⟩ := M.dense.nonempty
  exact (e.ge (Set.mem_univ z)) hz

end Modif

end Moving

section Resol

variable {Y : Scheme.{0}} {p : Y ⟶ Sp F} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y}

structure Resol (C : Common B) (U : Y.Opens) (D : ℕ) {a₁ a₂ : Λ} (W₁ : Submodule F (H0 p (B a₁) ⊤))
    (W₂ : Submodule F (H0 p (B a₂) ⊤)) extends Modif p U D where

  Δ₁ : Cartier ((baseIdeal (C.isLB a₁) W₁).comap σ)

  Δ₂ : Cartier ((baseIdeal (C.isLB a₂) W₂).comap σ)

namespace Resol

variable {C : Common B} {U : Y.Opens} {D : ℕ} {a₁ a₂ : Λ} {W₁ : Submodule F (H0 p (B a₁) ⊤)}
  {W₂ : Submodule F (H0 p (B a₂) ⊤)} (R : Resol C U D W₁ W₂)

abbrev pb (a : Λ) : LB R.X := (B a).pull R.σ

abbrev com : Common R.pb := C.pull R.σ

abbrev L : LB R.X := R.Δ₁.moving

abbrev L₂ : LB R.X := R.Δ₂.moving

abbrev A : LB R.X := R.pb (a₂ + D • a₁)

def e : (LB.div R.A (tw R.L₂ R.L D)).Sec :=
  toSec ((R.com.effChart R.Δ₁.isLB R.Δ₂.isLB rfl).mul (H0.ofSec R.str ⊤ R.Δ₂.t) (H0.ofSec R.str ⊤ (R.Δ₁.pow D)))

theorem ger_e (t : R.Δ₂.P.ι × C.J × R.Δ₁.P.ι) (z : R.X) (h₂ : z ∈ R.Δ₂.P.U t.1) (h₁ : z ∈ R.Δ₁.P.U t.2.2) (h) :
    ger z h (R.e.f ((R.com.effChart R.Δ₁.isLB R.Δ₂.isLB rfl).c t)) =
      ger z h₂ (R.Δ₂.t.f t.1) * ger z h₁ (R.Δ₁.t.f t.2.2) ^ D :=
  (ger_toSec _ _ _ _).trans <| ((R.com.effChart R.Δ₁.isLB R.Δ₂.isLB rfl).germ_mul _ _ t z _ h₂ (mem_zpow_U.2 h₁) h).trans
    (congrArg₂ (· * ·) (germ_ofSec _ _ _ _ _) (R.Δ₁.germ_pow _ D _ z _ h₁ _))

theorem off_le_nonzeroLocus_e (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) :
    R.off ≤ nonzeroLocus R.e := fun z hz => by
  obtain ⟨t, ha, hb, hc⟩ := (R.com.effChart (n := D) R.Δ₁.isLB R.Δ₂.isLB (rfl : a₂ + D • a₁ = _)).cover z
  refine (isUnit_ger_iff _ hc).1 ?_
  rw [R.ger_e t z ha (mem_zpow_U.1 hb)]
  exact ((isUnit_ger_iff _ _).2 ((R.Δ₂.mem_nonzeroLocus z).2 (R.notMem_support h₂ z hz))).mul
    (((isUnit_ger_iff _ _).2 ((R.Δ₁.mem_nonzeroLocus z).2 (R.notMem_support h₁ z hz))).pow D)

abbrev adj (j : ℕ) : LB R.X := tw (tens R.K.bundle R.A) R.L j

def mulPole (j : ℕ) (O : R.X.Opens) :
    H0 R.str (R.adj j) O →ₗ[F] H0 R.str (tens R.K.bundle (R.pb (a₂ + D • a₁ + j • a₁))) O :=
  (R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mul (H0.ofSec R.str O (R.Δ₁.pow j))

variable {κ : Λ} (ω : H0 R.str (LB.div R.K.bundle (R.pb κ)) R.off)

def mulCan {b s : Λ} (h : κ + b = s) : H0 R.str (R.pb s) R.off →ₗ[F] H0 R.str (tens R.K.bundle (R.pb b)) R.off :=
  (R.com.canChart R.K.isLB h).mul ω

def adjEquiv (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s : Λ} (h : κ + (a₂ + D • a₁ + j • a₁) = s) :
    H0 R.str (R.pb s) R.off ≃ₗ[F] H0 R.str (R.adj j) R.off :=
  ((R.com.canChart R.K.isLB h).mulEquiv hω).trans ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv
    (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).symm

theorem mulPole_adjEquiv (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s : Λ}
    (h : κ + (a₂ + D • a₁ + j • a₁) = s) (m : H0 R.str (R.pb s) R.off) :
    R.mulPole j R.off (R.adjEquiv ω hω h₁ j h m) = R.mulCan ω h m :=
  ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv
    (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).apply_symm_apply _

abbrev adjIdx (j : ℕ) (t : R.K.bundle.ι × C.J × R.Δ₁.P.ι) : (R.adj j).ι :=
  twIdx (M := tens R.K.bundle R.A) (L := R.L) j (t.1, R.com.idx _ t.2.1) (R.com.idx a₁ t.2.1, t.2.2)

theorem germ_adjEquiv (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s : Λ}
    (h : κ + (a₂ + D • a₁ + j • a₁) = s) (m : H0 R.str (R.pb s) R.off) (t : R.K.bundle.ι × C.J × R.Δ₁.P.ι) (z : R.X)
    (hz : z ∈ R.off) (hP : z ∈ R.Δ₁.P.U t.2.2) (ha : z ∈ (R.adj j).U (R.adjIdx j t))
    (hω' : z ∈ (LB.div R.K.bundle (R.pb κ)).U (t.1, R.com.idx κ t.2.1)) (hs : z ∈ (R.pb s).U (R.com.idx s t.2.1)) :
    ger z hP (R.Δ₁.t.f t.2.2) ^ j * germ (R.adjIdx j t) z hz ha (R.adjEquiv ω hω h₁ j h m) =
      germ (B := LB.div R.K.bundle (R.pb κ)) (t.1, R.com.idx κ t.2.1) z hz hω' ω * germ (R.com.idx s t.2.1) z hz hs m := by
  have hc : z ∈ (tens R.K.bundle (R.pb (a₂ + D • a₁ + j • a₁))).U (t.1, R.com.idx _ t.2.1) :=
    ⟨hω'.1, (R.com.mem _ _ _).2 ((R.com.mem _ _ _).1 hs)⟩
  rw [← R.Δ₁.germ_pow R.str j _ z hz hP (mem_zpow_U.2 hP)]
  exact ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).germ_mul _ _ t z hz _ ha hc).symm.trans
    ((congrArg _ (R.mulPole_adjEquiv ω hω h₁ j h m)).trans
      ((R.com.canChart R.K.isLB h).germ_mul _ _ (t.1, t.2.1) z hz hω' hs hc))

theorem adjEquiv_mul (hω : NowhereZero ω) (h₁ : NoBase (C.isLB a₁) W₁ U) (j : ℕ) {s s' : Λ}
    (h : κ + (a₂ + D • a₁ + j • a₁) = s) (h' : κ + (a₂ + D • a₁ + (j + 1) • a₁) = s') (hs : a₁ + s = s') (w : W₁)
    (m : H0 R.str (R.pb s) R.off) :
    R.adjEquiv ω hω h₁ (j + 1) h' ((R.com.addChart hs).mul (restr le_top (H0.pull R.σ le_top w.1)) m) =
      (oneChart (isLB_tens R.K.isLB (R.com.isLB _)) R.Δ₁.isLB_moving (Nat.cast_succ j).symm).mul
        (restr le_top (R.Δ₁.lift w)) (R.adjEquiv ω hω h₁ j h m) := ext_germ fun z hz => by
  obtain ⟨i, hi⟩ := exists_chart R.K.isLB z
  obtain ⟨k, hk⟩ := R.com.cover z
  obtain ⟨n, hn⟩ := exists_chart R.Δ₁.isLB z
  have hk' (a : Λ) : z ∈ (R.pb a).U (R.com.idx a k) := (R.com.mem a k z).2 hk
  have ha (j : ℕ) : z ∈ (R.adj j).U (R.adjIdx j (i, k, n)) := mem_tw_U.2 ⟨⟨hi, hk' _⟩, hk' _, hn⟩
  refine ⟨R.adjIdx (j + 1) (i, k, n), ha _,
    (mul_cancel_left_mem_nonZeroDivisors (pow_mem (R.Δ₁.reg n z hn) (j + 1))).1 ?_⟩
  have e₁ := R.germ_adjEquiv ω hω h₁ (j + 1) h' ((R.com.addChart hs).mul (restr le_top (H0.pull R.σ le_top w.1)) m)
    (i, k, n) z hz hn (ha _) ⟨hi, hk' _⟩ (hk' _)
  have e₂ := R.germ_adjEquiv ω hω h₁ j h m (i, k, n) z hz hn (ha _) ⟨hi, hk' _⟩ (hk' _)
  have e₃ := (R.com.addChart hs).germ_mul (restr le_top (H0.pull R.σ le_top w.1)) m k z hz (hk' _) (hk' _) (hk' _)
  have e₄ := (oneChart (isLB_tens R.K.isLB (R.com.isLB (a₂ + D • a₁))) R.Δ₁.isLB_moving (Nat.cast_succ j).symm).germ_mul
    (restr le_top (R.Δ₁.lift w)) (R.adjEquiv ω hω h₁ j h m) ((i, R.com.idx _ k), (R.com.idx a₁ k, n)) z hz
    ⟨hk' _, hn⟩ (ha j) (ha (j + 1))
  have e₅ := R.Δ₁.germ_lift w (R.com.idx a₁ k, n) z ⟨hk' _, hn⟩
  replace e₃ := e₃.trans (congrArg (· * _) (germ_restr _ _ _ _ _ _))
  replace e₄ := e₄.trans (congrArg (· * _) (germ_restr _ _ _ _ _ _))
  refine e₁.trans (Eq.trans ?_ (congrArg (_ * ·) e₄).symm)
  refine (congrArg (_ * ·) (e₃.trans (congrArg (· * _) e₅.symm))).trans ?_
  refine (mul_left_comm _ _ _).trans ((congrArg (_ * ·) e₂.symm).trans ?_)
  rw [pow_succ']
  exact mul_mul_mul_comm _ _ _ _

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module F V₁] [Module (𝓞 F) V₁] [AddCommGroup V₂] [Module F V₂]
  [Module (𝓞 F) V₂] {N₁ : (F →+* ℂ) → V₁ → ℝ} {M₁ : Submodule (𝓞 F) V₁} {N₂ : (F →+* ℂ) → V₂ → ℝ}
  {M₂ : Submodule (𝓞 F) V₂}

def geo [IsReduced Y] (hU : Dense (U : Set Y)) (hc : GeometricallyConnected R.str) (hD : 1 ≤ D)
    (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) (φ₁ : V₁ ≃ₗ[F] W₁) (φ₂ : V₂ ≃ₗ[F] W₂)
    (f₁ : LatFrame N₁ M₁) (f₂ : LatFrame N₂ M₂) (th : R.L.Sec) (abelian₂ : ℝ) : Geo F where
  toHermSys := R.sys R.Δ₁ φ₁ f₁ abelian₂
  bd := R.bd
  j₀ := 1
  th := secToPow th 1
  geom := ⟨R.isAlgebraicData _ _ _ hU hc hD _, R.bd_ne_top hc⟩
  herm := f₁.isFrame.herm
  conj := f₁.isFrame.conj
  K := R.K
  L₂ := R.L₂
  isLB₂ := R.Δ₂.isLB_moving
  N₂ := f₂.N
  b₂ := R.basisSec R.Δ₂ φ₂ f₂
  n₂ := f₂.n
  w₂ := f₂.w
  A₂ := f₂.A
  alg₂ := R.isAlgebraicData _ _ _ hU hc hD abelian₂
  herm₂ := f₂.isFrame.herm
  conj₂ := f₂.isFrame.conj
  LA := R.A
  isLBA := R.com.isLB _
  e := R.e
  U_le := R.off_le_nonzeroLocus_e h₁ h₂

end Resol

end Resol

section Lattices

structure Consts where

  abelian₂ : ℝ

  beta : ℝ

  LamD : ℝ

  LamT : ℝ

  J : ℝ

  one_le_beta : 1 ≤ beta

  one_le_LamD : 1 ≤ LamD

  one_le_LamT : 1 ≤ LamT

variable {S X : Type} [AddCommGroup S] [Module F S] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [AddCommGroup X]
  [Module F X] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] (ψ : S →ₗ[F] X) (hψ : Function.Injective ψ) (q : Prop)


open Classical in
def rangeIf : Submodule F X := if q then LinearMap.range ψ else ⊥


omit [NumberField F] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] in
theorem rangeIf_le : rangeIf ψ q ≤ LinearMap.range ψ := by
  unfold rangeIf
  split_ifs
  exacts [le_rfl, bot_le]

def invIf : rangeIf ψ q →ₗ[F] S :=
  (LinearEquiv.ofInjective ψ hψ).symm.toLinearMap ∘ₗ Submodule.inclusion (rangeIf_le ψ q)


omit [NumberField F] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] in
theorem apply_invIf (x : rangeIf ψ q) : ψ (invIf ψ hψ q x) = x :=
  congrArg Subtype.val ((LinearEquiv.ofInjective ψ hψ).apply_symm_apply ⟨x, rangeIf_le ψ q x.2⟩)


omit [NumberField F] [Module (𝓞 F) S] [IsScalarTower (𝓞 F) F S] [Module (𝓞 F) X] [IsScalarTower (𝓞 F) F X] in
theorem invIf_injective : Function.Injective (invIf ψ hψ q) := fun x y e =>
  Subtype.ext (by rw [← apply_invIf ψ hψ, e, apply_invIf])

def equivIf (hq : q) : rangeIf ψ q ≃ₗ[F] S :=
  LinearEquiv.ofBijective (invIf ψ hψ q) ⟨invIf_injective ψ hψ q, fun s =>
    ⟨⟨ψ s, by rw [rangeIf, if_pos hq]; exact ⟨s, rfl⟩⟩, hψ (apply_invIf _ _ _ _)⟩⟩

variable {Nm : (F →+* ℂ) → S → ℝ} (M : Submodule (𝓞 F) S)

def latIf : Submodule (𝓞 F) (rangeIf ψ q) := M.comap ((invIf ψ hψ q).restrictScalars (𝓞 F))

variable {q M} (h : q → Nonempty (LatFrame Nm M))
include h

theorem isFull_latIf : IsFull (latIf ψ hψ q M) := by
  by_cases hq : q
  · obtain ⟨f⟩ := h hq
    let e := equivIf ψ hψ q hq
    have : latIf ψ hψ q M = M.map (e.symm.toLinearMap.restrictScalars (𝓞 F)) := Submodule.ext fun x =>
      ⟨fun hx => ⟨e x, hx, e.symm_apply_apply x⟩, fun ⟨s, hs, ex⟩ => ex ▸ ((e.apply_symm_apply s).symm ▸ hs : e (e.symm s) ∈ M)⟩
    rw [this]
    refine ⟨f.isFull.fg.map _, ?_⟩
    refine (Submodule.span_image e.symm.toLinearMap).trans ?_
    rw [f.isFull.span, Submodule.map_top, LinearEquiv.range]
  · have : Subsingleton (rangeIf ψ q) := by rw [rangeIf, if_neg hq]; infer_instance
    exact ⟨by rw [Subsingleton.elim (latIf ψ hψ q M) ⊥]; exact Submodule.fg_bot, Subsingleton.elim _ _⟩

theorem exists_famIf : ∃ g : HermFam F (rangeIf ψ q), g.IsConjInv ∧ (q → ∀ σ x, g.nrm σ x = Nm σ (invIf ψ hψ q x)) := by
  by_cases hq : q
  · obtain ⟨f⟩ := h hq
    exact ⟨HermTools.comap f.fam _ (invIf_injective ψ hψ q), isConjInv_comap f.isConjInv_fam _ _,
      fun _ σ x => f.nrm_fam σ _⟩
  · have := (isFull_latIf ψ hψ h).finiteDimensional
    exact ⟨ofBasis (Module.finBasis F _), isConjInv_ofBasis _, fun h => absurd h hq⟩

end Lattices

section Data

variable (G : Geo F) (T : ℕ) (hT : G.D + 1 ≤ T) {S : ℕ → Type} [∀ j, AddCommGroup (S j)] [∀ j, Module F (S j)]
  [∀ j, Module (𝓞 F) (S j)] [∀ j, IsScalarTower (𝓞 F) F (S j)] (ψ : ∀ j, S j →ₗ[F] G.Sec j)
  (hψ : ∀ j, Function.Injective (ψ j)) {Nm : ∀ j, (F →+* ℂ) → S j → ℝ} {M : ∀ j, Submodule (𝓞 F) (S j)}
  (hM : ∀ j, j ≤ T → Nonempty (LatFrame (Nm j) (M j))) (hle : ∀ j ≤ T, G.global j ≤ LinearMap.range (ψ j))
  (h0 : LinearMap.range (ψ 0) ≤ G.global 0) (k : Consts)

def dataOf : Data F where
  toGeo := G
  T := T
  le_T := hT
  V j := rangeIf (ψ j) (j ≤ T)
  global_le j hj := by rw [rangeIf, if_pos hj]; exact hle j hj
  V_zero := by rw [rangeIf, if_pos T.zero_le]; exact le_antisymm h0 (hle 0 T.zero_le)
  M j := latIf (ψ j) (hψ j) _ (M j)
  full j := isFull_latIf _ _ (hM j)
  nm j := (exists_famIf _ (hψ j) (hM j)).choose
  conjInv j := (exists_famIf _ (hψ j) (hM j)).choose_spec.1
  beta := k.beta
  LamD := k.LamD
  LamT := k.LamT
  J := k.J
  one_le_beta := k.one_le_beta
  one_le_LamD := k.one_le_LamD
  one_le_LamT := k.one_le_LamT

def dataEquiv {j : ℕ} (hj : j ≤ T) : S j ≃ₗ[F] (dataOf G T hT ψ hψ hM hle h0 k).V j := (equivIf (ψ j) (hψ j) _ hj).symm

theorem coe_dataEquiv {j : ℕ} (hj : j ≤ T) (s : S j) : (dataEquiv G T hT ψ hψ hM hle h0 k hj s).1 = ψ j s :=
  (apply_invIf _ (hψ j) _ _).symm.trans (congrArg _ ((equivIf (ψ j) (hψ j) _ hj).apply_symm_apply s))

theorem dataEquiv_mem {j : ℕ} (hj : j ≤ T) (s : S j) :
    dataEquiv G T hT ψ hψ hM hle h0 k hj s ∈ (dataOf G T hT ψ hψ hM hle h0 k).M j ↔ s ∈ M j :=
  Iff.of_eq (congrArg (· ∈ M j) ((equivIf (ψ j) (hψ j) _ hj).apply_symm_apply s))

theorem nrm_dataEquiv {j : ℕ} (hj : j ≤ T) (σ : F →+* ℂ) (s : S j) :
    ((dataOf G T hT ψ hψ hM hle h0 k).nm j).nrm σ (dataEquiv G T hT ψ hψ hM hle h0 k hj s) = Nm j σ s :=
  ((exists_famIf _ (hψ j) (hM j)).choose_spec.2 hj σ _).trans
    (congrArg _ ((equivIf (ψ j) (hψ j) _ hj).apply_symm_apply s))

end Data

end GlobalTheory.CompHS
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime)

theorem LatFrame.mem_span_iff {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] {Nm : (F →+* ℂ) → V → ℝ} {M : Submodule (𝓞 F) V} (f : LatFrame Nm M) (x : V) :
    f.b.equivFun x ∈ Submodule.span (𝓞 F) (Set.range f.w.col) ↔ x ∈ M := by
  have e : (fun k => ∑ j, f.w j k • f.b j) = (f.b.equivFun.symm.restrictScalars (𝓞 F)) ∘ f.w.col :=
    funext fun k => (f.b.equivFun_symm_apply _).symm
  conv_rhs => rw [← f.isFrame.span, e, Set.range_comp]
  rw [Submodule.span_image_linearEquiv, Submodule.mem_map_equiv]
  rfl

section Gaps

variable {N : ℕ}

def gap (v : Fin N → ℤ) (k : ℕ) : ℤ := if h : k + 1 < N then v ⟨k, by omega⟩ - v ⟨k + 1, h⟩ else 0

def ofGaps (a : ℕ) (g : ℕ → ℤ) : Fin N → ℤ := fun i => ∑ k ∈ Finset.range a, g k - ∑ k ∈ Finset.range i, g k

def floorGaps (a : ℕ) (n : ℤ) (v : Fin N → ℤ) : Fin N → ℤ := ofGaps a fun k => gap v k / n

def remGaps (a : ℕ) (n : ℤ) (v : Fin N → ℤ) : Fin N → ℤ := ofGaps a fun k => gap v k - n * (gap v k / n)

theorem gap_eq (v : Fin N → ℤ) {i j : Fin N} (h : (j : ℕ) = i + 1) : gap v i = v i - v j := by
  have := j.2
  rw [gap, dif_pos (by omega)]
  exact congrArg (fun x => v i - v x) (Fin.ext h.symm)

theorem ofGaps_anchor (g : ℕ → ℤ) (i : Fin N) : ofGaps i g i = 0 := sub_self _

theorem gap_ofGaps (a : ℕ) (g : ℕ → ℤ) {k : ℕ} (h : k + 1 < N) : gap (ofGaps a g : Fin N → ℤ) k = g k := by
  simp [gap, h, ofGaps, Finset.sum_range_succ]

theorem ofGaps_gap (v : Fin N → ℤ) (a i : Fin N) : ofGaps a (gap v) i = v i - v a := by
  have key : ∀ (n : ℕ) (h : n < N), ∑ k ∈ Finset.range n, gap v k = v ⟨0, by omega⟩ - v ⟨n, h⟩ := fun n => by
    induction n with
    | zero => simp
    | succ n ih => intro h; rw [Finset.sum_range_succ, ih (by omega), gap, dif_pos h]; ring
  rw [ofGaps, key a a.2, key i i.2]
  ring

theorem floorGaps_add_remGaps (n : ℤ) (v : Fin N → ℤ) (a i : Fin N) :
    n * floorGaps a n v i + remGaps a n v i = v i - v a := by
  rw [← ofGaps_gap]
  simp only [floorGaps, remGaps, ofGaps, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem gap_remGaps (a : ℕ) {n : ℤ} (hn : 0 < n) (v : Fin N → ℤ) (k : ℕ) :
    0 ≤ gap (remGaps a n v) k ∧ gap (remGaps a n v) k < n := by
  by_cases h : k + 1 < N
  · rw [remGaps, gap_ofGaps _ _ h, ← Int.emod_def]
    exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩
  · rw [gap, dite_eq_right h]; exact ⟨le_rfl, hn⟩

end Gaps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure WtPar (Dw : Datum H) where

  u : AllWt.Weight Dw

  c₀ : ℤ

  a : ℕ

  T : ℕ

namespace WtPar

variable (P : WtPar Dw)

def T₁ : ℤ := P.T + dimFlag Dw + 1

def uMinus : AllWt.Weight Dw := P.u - P.c₀ • hodgeWt Dw

def u₁ : AllWt.Weight Dw := fun τ => floorGaps P.a P.T₁ ((P.uMinus - FlagTan.kap Dw) τ)

def rem : AllWt.Weight Dw := fun τ => remGaps P.a P.T₁ ((P.uMinus - FlagTan.kap Dw) τ)

def u₂ : AllWt.Weight Dw := P.u₁ + P.rem

def uc : AllWt.Weight Dw := FlagTan.kap Dw + P.u₂ + dimFlag Dw • P.u₁

def ub : AllWt.Weight Dw := fun τ => floorGaps P.a (dimFlag Dw + 3) (P.u₁ τ)

def wt (j : ℕ) : AllWt.Weight Dw := P.uc + j • P.u₁

theorem kap_add (j : ℕ) : FlagTan.kap Dw + (P.u₂ + dimFlag Dw • P.u₁ + j • P.u₁) = P.wt j := by
  rw [wt, uc]; abel

theorem u₁_add_wt (j : ℕ) : P.u₁ + P.wt j = P.wt (j + 1) := by
  rw [wt, wt, succ_nsmul]; abel

theorem gap_u₁ (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (P.u₁ τ) k = gap ((P.uMinus - FlagTan.kap Dw) τ) k / P.T₁ := gap_ofGaps _ _ h

theorem gap_rem (τ : Psi H) (k : ℕ) : 0 ≤ gap (P.rem τ) k ∧ gap (P.rem τ) k ≤ P.T + dimFlag Dw :=
  (gap_remGaps P.a (n := P.T₁) (by unfold T₁; positivity) _ k).imp_right Int.lt_add_one_iff.1

theorem gap_ub (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (P.ub τ) k = gap (P.u₁ τ) k / (dimFlag Dw + 3) := gap_ofGaps _ _ h

theorem anchored (τ : Psi H) {i : Fin (Dw.p + Dw.q)} (h : (i : ℕ) = P.a) :
    P.u₁ τ i = 0 ∧ P.rem τ i = 0 ∧ P.u₂ τ i = 0 ∧ P.ub τ i = 0 := by
  simp [u₂, u₁, rem, ub, floorGaps, remGaps, ← h, ofGaps_anchor]

theorem uMinus_eq (τ : Psi H) {a : Fin (Dw.p + Dw.q)} (h : (a : ℕ) = P.a) (i : Fin (Dw.p + Dw.q)) :
    P.uMinus τ i = P.wt P.T τ i + (P.uMinus τ a - FlagTan.kap Dw τ a) := by
  have := floorGaps_add_remGaps P.T₁ ((P.uMinus - FlagTan.kap Dw) τ) a i
  rw [h] at this
  simp only [wt, uc, u₂, u₁, rem, T₁, Pi.add_apply, Pi.smul_apply, Pi.sub_apply] at this ⊢
  simp only [nsmul_eq_mul]
  linear_combination -this

theorem gap_uMinus_sub_kap (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) : gap ((P.uMinus - FlagTan.kap Dw) τ) k =
    gap (P.u τ) k + if k + 1 = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2 := by
  simp only [gap, dif_pos h, uMinus, hodgeWt, CompHt.barWt, FlagTan.kap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> omega

end WtPar

theorem dimFlag_eq (Dw : Datum H) : CompHt.dimFlag Dw = dimFlag Dw := by
  classical
  rw [CompHt.dimFlag, Formalism.DegreeFormula.dimFl, dimFlag, Nat.choose_two_right, ← (FlagTan.isHalf_psiSet H).card]
  congr 1
  exact Fintype.card_of_subtype _ fun τ => by simp [psiSet]

structure TorFlag (Xo : Moduli Dw l) (c : Coeff l) where

  Y : Model Xo c (RingHom.id c.F)

  smooth : SmoothOfRelativeDimension Dw.dim Y.s

  snc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (LogKS.boundary Y)

  logKS : LogKS.HasLogKS Y.t Y.s (LogKS.interior Y)

  flag : FlagModel Y

abbrev TorFlag.X (T : TorFlag Xo c) : FlagCover T.Y := T.flag.toFlagCover

set_option synthInstance.maxHeartbeats 200000
section Flag

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

abbrev flagStr : X.YY ⟶ Sp c.F := X.π ≫ Y.s

def flagOpen : X.YY.Opens := X.π ⁻¹ᵁ LogKS.interior Y

instance isOpenImmersion_inc : IsOpenImmersion X.inc := inferInstanceAs (IsOpenImmersion (pullback.fst X.π Y.j))

theorem opensRange_inc : X.inc.opensRange = flagOpen X := Scheme.Hom.opensRange_pullbackFst _ _

theorem top_le_inc : ⊤ ≤ X.inc ⁻¹ᵁ flagOpen X := fun z _ => (opensRange_inc X).le ⟨z, rfl⟩

instance isReduced_flag : IsReduced X.YY :=
  have : ∀ x : X.YY, _root_.IsReduced (X.YY.presheaf.stalk x) := fun x => have := (X.normal x).1; inferInstance
  isReduced_of_isReduced_stalk _

theorem dense_flagOpen : Dense (flagOpen X : Set X.YY) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  let r := pullback.fst (X.π ≫ Y.s) (spMap (RingHom.id c.F))
  refine (r.surjective.denseRange.dense_image r.continuous X.dense).mono ?_
  rintro _ ⟨z, ⟨x, hx⟩, rfl⟩
  refine ⟨x, ?_⟩
  rw [Model.j, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, FlagMod.genMap,
    pullback.lift_fst]

theorem ptY_str {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) :
    X.ptY P ≫ flagStr X = spMap (algebraMap c.F S) := by
  rw [← Category.assoc, (X.lies_ptY P).1, Category.assoc, Model.j, Category.assoc, pullback.condition,
    ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, FlagMod.frX_snd]
  exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)

def commonLL : Common X.F.LL where
  isLB := X.F.isLB_LL
  J := X.F.J
  U := X.F.U
  cover y := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ y))
  idx _ k := k
  mem _ _ _ := Iff.rfl
  add a b y k k' h h' := Units.ext <| by
    rw [Units.val_mul]
    refine (val_tr _ y (memInf h h')).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (val_tr _ y (memInf h h')) (val_tr _ y (memInf h h'))).symm)
    exact (congrArg (fun u => ger y (memInf h h') u.val) (X.F.LL_add_g a b k k')).trans (map_mul _ _ _)

variable {X} {e : Ix Dw → ℤ}

def toSecO (m : H0 (flagStr X) (X.LL e) (flagOpen X)) : X.SecO e := toSec (H0.pull X.inc (top_le_inc X) m)

theorem coef_toSecO {S : Type} [CommRing S] (m : H0 (flagStr X) (X.LL e) (flagOpen X)) (k : X.F.J) (w : Sp S ⟶ X.Yo)
    (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k) (hO : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ flagOpen X) :
    FlagCover.coef (toSecO m) k w hz = H0.val (B := X.LL e) (w ≫ X.inc) k hO hz m :=
  (val_ofSec (p := X.inc ≫ flagStr X) (O := ⊤) w (pIdx (X.LL e) X.inc k) le_top (FlagCover.le_pull hz) _).symm.trans
    ((congrArg _ (ofSec_toSec _)).trans (val_pull _ _ _ _ _ _ hO hz m))

theorem bijective_toSecO : Function.Bijective (toSecO : H0 (flagStr X) (X.LL e) (flagOpen X) → X.SecO e) :=
  (Equiv.ofBijective _ bijective_ofSec_top).symm.bijective.comp
    ((isoOver_of_isOpenImmersion X.inc (opensRange_inc X).ge).bijective_pull (X.F.isLB_LL e) _ le_top)


variable (X e) in
def ruleOf : H0 (flagStr X) (X.LL e) (flagOpen X) →ₗ[c.F] secZ Xo c e where
  toFun m := ⟨FlagCover.toRule (toSecO m), FlagCover.toRule_mem_secZ _⟩
  map_add' m m' := Subtype.ext <| funext₂ fun p P => by
    refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
    have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
    change ψ (FlagCover.val _ P + FlagCover.val _ P) = _
    rw [map_add (f := _), FlagCover.isVal_val _ P S' ψ P' hP k hz Q t hQ ht, FlagCover.isVal_val _ P S' ψ P' hP k hz Q t hQ ht,
      coef_toSecO _ _ _ _ hO, coef_toSecO _ _ _ _ hO, coef_toSecO _ _ _ _ hO, map_add, mul_add]
  map_smul' a m := Subtype.ext <| funext₂ fun p P => by
    refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
    have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
    change ψ (a • FlagCover.val _ P) = _
    rw [map_smul, FlagCover.isVal_val _ P S' ψ P' hP k hz Q t hQ ht, coef_toSecO _ _ _ _ hO, coef_toSecO _ _ _ _ hO,
      Algebra.smul_def, mul_left_comm]
    refine congrArg (_ * ·) (Eq.symm ((val_fun_smul (B := X.LL e) _ k hO hz _ m).trans (congrArg (· * _) ?_)))
    exact evalPt_algX_of_eq _ _ (by rw [X.pt_inc]; exact ptY_str X P') _ _ a

theorem bijective_ruleOf : Function.Bijective (ruleOf X e) := by
  have : IsReduced X.Yo := isReduced_of_isOpenImmersion X.inc
  refine ⟨fun m m' h => bijective_toSecO.1 (FlagCover.toRule_injective (congrArg Subtype.val h)), fun f => ?_⟩
  obtain ⟨s, hs⟩ := FlagCover.exists_toRule_eq (X := X) f.2
  obtain ⟨m, rfl⟩ := bijective_toSecO.2 s
  exact ⟨m, Subtype.ext hs⟩


variable (X e) in
def secOf : secZ Xo c e ≃ₗ[c.F] H0 (flagStr X) (X.LL e) (flagOpen X) :=
  (LinearEquiv.ofBijective _ bijective_ruleOf).symm


open Classical in
theorem evR_eq_val_secOf {S : Type} [CommRing S] [Algebra c.F S] [_root_.IsReduced S] (f : secZ Xo c e)
    {P Q : FrPt Xo c S} {k : X.F.J} {z : Sp S ⟶ X.YY} {hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k} (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen X)
    {t : Ix Dw → Sˣ} (hQ : X.F.ChartFr k z hz Q) (ht : FrBor t Q P) :
    evR Xo c f.1 P = (∏ ix, t ix ^ e ix).val * H0.val (B := X.LL e) z k hO hz (secOf X e f) := by
  obtain rfl : z = X.pt P ≫ X.inc := (FlagCover.eq_ptY (hQ.lies.frBor ht)).trans (X.pt_inc P).symm
  obtain ⟨m, rfl⟩ := (secOf X e).symm.surjective f
  rw [LinearEquiv.apply_symm_apply, ← coef_toSecO, ← FlagCover.val_eq _ hQ ht]
  exact FlagCover.evR_toRule_of_isReduced _ P

theorem exists_chartFr {S : Type} [CommRing S] (z : Sp S ⟶ X.YY) (hO : ⊤ ≤ z ⁻¹ᵁ flagOpen X) :
    ∃ _ : Algebra c.F S, ∀ (k : X.F.J) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k), ∃ Q : FrPt Xo c S, X.F.ChartFr k z hz Q := by
  have hr : Set.range z ⊆ Set.range X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc X).ge (hO (Set.mem_univ s))
  obtain ⟨w, rfl⟩ : ∃ w, w ≫ X.inc = z := ⟨_, IsOpenImmersion.lift_fac X.inc z hr⟩
  obtain ⟨a, h⟩ := FlagCover.exists_alg_chartFr w
  exact ⟨a, fun k hz => (h k hz).imp fun _ => And.left⟩

theorem secOf_mul {e₁ e₂ : Ix Dw → ℤ} (h : e₁ + e₂ = e) (f₁ : secZ Xo c e₁) (f₂ : secZ Xo c e₂) (f : secZ Xo c e)
    (hf : f.1 = f₁.1 * f₂.1) : secOf X e f = ((commonLL X).addChart h).mul (secOf X e₁ f₁) (secOf X e₂ f₂) := by
  refine LB.sec_ext fun k => FlagMod.ext_ev_field fun L _ z hz => ?_
  have hO := FlagMod.le_preimage_mono inf_le_left hz
  have hk := FlagMod.le_preimage_mono inf_le_right hz
  obtain ⟨_, hQ⟩ := exists_chartFr z hO
  obtain ⟨Q, hQ⟩ := hQ k hk
  have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q
  have a := evR_eq_val_secOf f hO hQ hb
  have a₁ := evR_eq_val_secOf f₁ hO hQ hb
  have a₂ := evR_eq_val_secOf f₂ hO hQ hb
  simp only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] at a a₁ a₂
  refine a.symm.trans (Eq.trans ?_ (((commonLL X).addChart h).val_mul _ _ k z hO hk hk hk).symm)
  rw [hf]
  exact (evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) _ _ Q).trans
    (congrArg₂ (· * ·) a₁ a₂)

end Flag

section Component

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)


variable (Y) in
def barComp : Y.X.Opens := ⟨(closure (Y.j '' (Z : Set (Xo.XF c))ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩

theorem j_mem_barComp (x : Xo.XF c) : Y.j x ∈ barComp Y Z ↔ x ∈ (Z : Set (Xo.XF c)) := by
  have h := Y.j.isOpenEmbedding.isOpenMap.preimage_closure_image Y.j.isOpenEmbedding.injective Y.j.continuous _
    (TrivOrderTieCompare.isClopen_comp Z).compl.isClosed
  exact (not_congr (Set.ext_iff.1 h x)).trans not_not

theorem barComp_subset_closure : (barComp Y Z : Set Y.X) ⊆ closure (Y.j '' (Z : Set (Xo.XF c))) := fun y hy => by
  have h : y ∈ closure (Set.range Y.j) := LogKS.dense_interior Y y
  rw [← Set.image_univ, ← Set.union_compl_self (Z : Set (Xo.XF c)), Set.image_union, closure_union] at h
  exact h.resolve_right hy

abbrev Y₀ : Scheme.{0} := (X.π ⁻¹ᵁ barComp Y Z).toScheme

abbrev inc₀ : Y₀ X Z ⟶ X.YY := (X.π ⁻¹ᵁ barComp Y Z).ι

abbrev str₀ : Y₀ X Z ⟶ Sp c.F := inc₀ X Z ≫ flagStr X

def U₀ : (Y₀ X Z).Opens := inc₀ X Z ⁻¹ᵁ flagOpen X

def bd₀ : Closeds (Y₀ X Z) := (U₀ X Z).compl

instance isReduced_Y₀ : IsReduced (Y₀ X Z) := isReduced_of_isOpenImmersion (inc₀ X Z)

theorem dense_U₀ : Dense (U₀ X Z : Set (Y₀ X Z)) :=
  (dense_flagOpen X).preimage (inc₀ X Z).isOpenEmbedding.isOpenMap

theorem ptY_le_iff {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) :
    ⊤ ≤ X.ptY P ⁻¹ᵁ (X.π ⁻¹ᵁ barComp Y Z) ↔ LiesOn Z P := by
  rw [← Scheme.Hom.comp_preimage, (X.lies_ptY P).1]
  exact ⟨fun h s => (j_mem_barComp Z _).1 (h (Set.mem_univ s)), fun h s _ => (j_mem_barComp Z _).2 (h s)⟩

def IsVariety₀ : Prop :=
  SmoothOfRelativeDimension (dimFlag Dw) (str₀ X Z) ∧ IsProjOver (str₀ X Z) ∧ GeometricallyConnected (str₀ X Z)

abbrev LL₀ (e : Ix Dw → ℤ) : LB (Y₀ X Z) := (X.LL e).pull (inc₀ X Z)

abbrev L₀ (la : AllWt.Weight Dw) : LB (Y₀ X Z) := LL₀ X Z (exOf Dw la 0)

theorem exOf_add_zero (a b : AllWt.Weight Dw) : exOf Dw (a + b) 0 = exOf Dw a 0 + exOf Dw b 0 :=
  AllWt.exOf_add a b 0 0

def common₀ : Common (L₀ X Z) := ((commonLL X).pull (inc₀ X Z)).comap (fun la => exOf Dw la 0) exOf_add_zero

theorem isLB_L₀ (la : AllWt.Weight Dw) : (L₀ X Z la).IsLB := (common₀ X Z).isLB la

def sec₀ (e : Ix Dw → ℤ) : secZ Xo c e →ₗ[c.F] H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z) :=
  H0.pull (inc₀ X Z) le_rfl ∘ₗ (secOf X e).toLinearMap

theorem eq_zero_of_sec₀ {e : Ix Dw → ℤ} {f : secZ Xo c e} (hf : f.1 ∈ suppOn Z) (h : sec₀ X Z e f = 0) : f = 0 := by
  refine (secOf X e).map_eq_zero_iff.1 (LB.sec_ext fun k => FlagMod.ext_ev_field fun L _ z hz => ?_)
  have hO := FlagMod.le_preimage_mono inf_le_left hz
  have hk := FlagMod.le_preimage_mono inf_le_right hz
  refine Eq.trans (b := 0) ?_ (map_zero _).symm
  obtain ⟨_, hQ⟩ := exists_chartFr z hO
  obtain ⟨Q, hQ⟩ := hQ k hk
  by_cases hZ : LiesOn Z Q
  · have hY := (ptY_le_iff X Z Q).2 hZ
    rw [← FlagCover.eq_ptY hQ.lies] at hY
    have hr : Set.range z ⊆ Set.range (inc₀ X Z) := by
      rintro _ ⟨s, rfl⟩; exact ⟨⟨_, hY (Set.mem_univ s)⟩, rfl⟩
    obtain ⟨w, rfl⟩ : ∃ w, w ≫ inc₀ X Z = z := ⟨_, IsOpenImmersion.lift_fac _ z hr⟩
    exact (H0.val_pull (O := flagOpen X) (W := U₀ X Z) (inc₀ X Z) le_rfl w (pIdx (X.LL e) _ k) hO (fun s hs => mem_pIdx.2 (hk hs)) hO hk _).symm.trans
      ((congrArg _ h).trans (map_zero _))
  · have a := evR_eq_val_secOf f hO hQ ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q)
    simp only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] at a
    exact a.symm.trans (hf L Q ((AllWt.liesOff_iff Z Q).2 hZ))

theorem sec₀_mul {e₁ e₂ e : Ix Dw → ℤ} (h : e₁ + e₂ = e) (f₁ : secZ Xo c e₁) (f₂ : secZ Xo c e₂) (f : secZ Xo c e)
    (hf : f.1 = f₁.1 * f₂.1) : sec₀ X Z e f =
      (((commonLL X).addChart h).pull (inc₀ X Z)).mul (sec₀ X Z e₁ f₁) (sec₀ X Z e₂ f₂) :=
  (congrArg (H0.pull (inc₀ X Z) (le_refl (U₀ X Z))) (secOf_mul h f₁ f₂ f hf)).trans
    (((commonLL X).addChart h).pull_mul (inc₀ X Z) (le_refl (U₀ X Z)) (secOf X e₁ f₁) (secOf X e₂ f₂))

def vanBd (la : AllWt.Weight Dw) : Submodule c.F (H0 (str₀ X Z) (L₀ X Z la) ⊤) where
  carrier := {s | ∀ y ∈ bd₀ X Z, ∀ i hi, germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal _}
  zero_mem' y _ i hi := by rw [map_zero]; exact zero_mem _
  add_mem' hs ht y hy i hi := by
    rw [map_add (germ i y (memTop y) hi)]
    exact add_mem (hs y hy i hi) (ht y hy i hi)
  smul_mem' a s hs y hy i hi := by rw [germ_smul]; exact Ideal.mul_mem_left _ _ (hs y hy i hi)

theorem mem_vanBd {la : AllWt.Weight Dw} {s : H0 (str₀ X Z) (L₀ X Z la) ⊤} :
    s ∈ vanBd X Z la ↔ ∀ y ∈ bd₀ X Z, y ∉ nonzeroLocus (toSec s) := by
  refine forall₂_congr fun y _ => ⟨fun h hy => ?_, fun h i hi hu => h ((isUnit_ger_iff _ hi).1 (by rwa [ger_toSec]))⟩
  obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ X Z la) y
  exact h i hi (by rw [← ger_toSec]; exact (isUnit_ger_iff _ hi).2 hy)

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

abbrev Cusp (la : AllWt.Weight Dw) : Submodule c.F (Rul Xo c) := cuspOn U Z (wtOf Dw la 0)

theorem cusp_le_secZ (la : AllWt.Weight Dw) : Cusp Z U la ≤ secZ Xo c (exOf Dw la 0) :=
  (AllWt.cuspOn_le U Z _).trans (AllWt.cuspW_le_secZ _)

def cuspSec (la : AllWt.Weight Dw) : Cusp Z U la →ₗ[c.F] H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z) :=
  sec₀ X Z _ ∘ₗ Submodule.inclusion (cusp_le_secZ Z U la)

theorem cuspSec_injective (la : AllWt.Weight Dw) : Function.Injective (cuspSec X Z U la) :=
  (injective_iff_map_eq_zero _).2 fun f h =>
    Submodule.inclusion_injective (cusp_le_secZ Z U la) ((eq_zero_of_sec₀ X Z f.2.2 h).trans (map_zero _).symm)

def space (la : AllWt.Weight Dw) : Submodule c.F (H0 (str₀ X Z) (L₀ X Z la) ⊤) :=
  (LinearMap.range (cuspSec X Z U la)).comap (restr le_top)

def Extends (la : AllWt.Weight Dw) : Prop :=
  ∀ f : Cusp Z U la, ∃ s ∈ vanBd X Z la, restr le_top s = cuspSec X Z U la f

abbrev baseId (la : AllWt.Weight Dw) : (Y₀ X Z).IdealSheafData := baseIdeal (isLB_L₀ X Z la) (space X Z U la)

abbrev FreeOnOpen (la : AllWt.Weight Dw) : Prop := NoBase (isLB_L₀ X Z la) (space X Z U la) (U₀ X Z)

def ofSpace (la : AllWt.Weight Dw) : space X Z U la →ₗ[c.F] Cusp Z U la :=
  (LinearEquiv.ofInjective _ (cuspSec_injective X Z U la)).symm.toLinearMap ∘ₗ
    (restr le_top ∘ₗ (space X Z U la).subtype).codRestrict _ fun s => s.2

theorem cuspSec_ofSpace (la : AllWt.Weight Dw) (s : space X Z U la) :
    cuspSec X Z U la (ofSpace X Z U la s) = restr le_top s.1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective _ (cuspSec_injective X Z U la)).apply_symm_apply ⟨_, s.2⟩)

theorem ofSpace_injective (la : AllWt.Weight Dw) : Function.Injective (ofSpace X Z U la) := fun s s' h =>
  Subtype.ext (restr_injective_of_dense le_top (dense_U₀ X Z) (by rw [← cuspSec_ofSpace, h, cuspSec_ofSpace]))

variable {X Z U} {la : AllWt.Weight Dw}

def Extends.equiv (h : Extends X Z U la) : Cusp Z U la ≃ₗ[c.F] space X Z U la :=
  (LinearEquiv.ofBijective _ ⟨ofSpace_injective X Z U la, fun f => (h f).elim fun s hs =>
    ⟨⟨s, f, hs.2.symm⟩, cuspSec_injective X Z U la ((cuspSec_ofSpace X Z U la _).trans hs.2)⟩⟩).symm

theorem Extends.restr_equiv (h : Extends X Z U la) (f : Cusp Z U la) :
    restr le_top (h.equiv f).1 = cuspSec X Z U la f :=
  (cuspSec_ofSpace X Z U la _).symm.trans (congrArg _ (h.equiv.symm_apply_apply f))

theorem Extends.space_le (h : Extends X Z U la) : space X Z U la ≤ vanBd X Z la := by
  rintro s ⟨f, hf⟩
  obtain ⟨s', hs', e⟩ := h f
  exact restr_injective_of_dense le_top (dense_U₀ X Z) (e.trans hf) ▸ hs'

end Component

end GlobalTheory.CompHS
