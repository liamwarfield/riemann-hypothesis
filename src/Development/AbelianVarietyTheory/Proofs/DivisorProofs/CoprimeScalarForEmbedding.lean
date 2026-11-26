module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem pairL_levRep_zsmul {n : ℕ} (x : Fin n → Dw.La) (m : ℤ) (q : Fin n → LevQ Dw l) :
    (l.M : ℤ) ∣ pairL (l := l) x (fun b => levRep ((m • q) b)) - m * pairL (l := l) x (fun b => levRep (q b)) := by
  have hrep : ∀ q : LevQ Dw l, (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  have e : m * pairL (l := l) x (fun b => levRep (q b)) = pairL (l := l) x (fun b => m • levRep (q b)) := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm, map_zsmul, smul_eq_mul]
  rw [e]
  refine GlobalTheory.LevelPairing.pairL_congr _ _ _ _ (fun b => by simp) fun b => ?_
  rw [← Submodule.Quotient.eq, hrep]
  refine Eq.trans ?_ (map_zsmul (Submodule.mkQ _) m (levRep (q b))).symm
  rw [Submodule.mkQ_apply, hrep, Pi.smul_apply]

theorem map_phiHat (c : Coeff l) (τ : c.F →+* ℂ) : ∃ m : ℤ, IsCoprime m (l.M : ℤ) ∧
    ∀ (n : ℕ) (φ : (Fin n → LevQc Dw l) → c.F), (∀ x, φ x = 0 ∨ φ x = 1) → ∀ q,
      τ (phiHat c φ q) = c.F.val.toRingHom (phiHat c φ (m • q)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  haveI : NeZero l.M := ⟨hM⟩
  have h0 := GlobalTheory.LevelPairing.zetaM_prim c
  have h1 : IsPrimitiveRoot (c.F.val.toRingHom (zetaM c)) l.M := h0.map_of_injective c.F.val.toRingHom.injective
  have h2 : IsPrimitiveRoot (τ (zetaM c)) l.M := h0.map_of_injective τ.injective
  obtain ⟨m, -, hm⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hc : m.Coprime l.M := (h1.pow_iff_coprime (Nat.pos_of_ne_zero hM) m).1 (hm ▸ h2)
  refine ⟨m, Nat.isCoprime_iff_coprime.2 hc, fun n φ hφ q => ?_⟩
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [phiHat, phiHat, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.LevelPairing.zpow_congr c (pairL_levRep_zsmul _ (m : ℤ) q), map_mul, map_mul, map_zpow₀, map_zpow₀, ← hm,
    _root_.zpow_mul, zpow_natCast]
  congr 1
  rcases hφ x with h | h <;> simp [h]

end Gen

end GlobalTheory.GalOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullPow

variable {X Y Z : Scheme.{0}}

theorem pull_pw_g (H : LB X) (g : Z ⟶ X) (n : ℤ) (i j : ((GlobalTheory.AbLaw.pw H n).pull g).ι) :
    ((GlobalTheory.AbLaw.pw H n).pull g).g i j = ((H.pull g).g i j) ^ n := by
  show (∏ k : PUnit, _) = (∏ k : PUnit, _) ^ n
  erw [Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

theorem div_pull_pw_g (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (n : ℤ)
    (p q : (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).ι) :
    (LB.div ((GlobalTheory.AbLaw.pw H n).pull g) ((GlobalTheory.AbLaw.pw M n).pull f)).g p q =
      ((LB.div (H.pull g) (M.pull f)).g p q) ^ n := by
  simp only [LB.div, pull_pw_g]
  erw [map_zpow, map_zpow, ← inv_zpow, ← mul_zpow]
  rfl

def isoPow {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g)) (n : ℤ) :
    LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g) where
  s := fun p => (w.s p) ^ n

theorem isoPow_isGen {M : LB X} {H : LB Y} {f : Z ⟶ X} {g : Z ⟶ Y} (w : LB.Iso (M.pull f) (H.pull g))
    (hw : w.IsGen) (n : ℤ) : (isoPow w n).IsGen := by
  intro p q
  rw [div_pull_pw_g]
  erw [map_zpow, map_zpow]
  erw [hw p q, mul_zpow]
  rfl

theorem exists_isGen_iso_pw : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y)
    (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ,
    ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen :=
  fun _ _ _ _ w _ _ hw n => ⟨isoPow w n, isoPow_isGen w hw n⟩

end GlobalTheory.PullPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpowStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isGen_iso_pullback_lineBundle_zpow : ∀ {X Y Z : Scheme.{0}} (M : LB X) (H : LB Y) (f : Z ⟶ X) (g : Z ⟶ Y) (w : LB.Iso (M.pull f) (H.pull g)), M.IsLB → H.IsLB → w.IsGen → ∀ n : ℤ, ∃ w' : LB.Iso ((GlobalTheory.AbLaw.pw M n).pull f) ((GlobalTheory.AbLaw.pw H n).pull g), w'.IsGen := by
  first | exact @GlobalTheory.PullPow.exists_isGen_iso_pw | exact GlobalTheory.PullPow.exists_isGen_iso_pw | (intros; apply GlobalTheory.PullPow.exists_isGen_iso_pw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPoint
noncomputable section

namespace GlobalTheory.LevModel

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem exists_frBor_of_frOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S]
    [Algebra d.c₂.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {p p' : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d p y) (h' : FrOver d p' y') (hb : FrBor t p p') : ∃ t' : Ix Dw → Sˣ, FrBor t' y y' := by
  obtain ⟨e, hu, -⟩ := h
  obtain ⟨e', hu', -⟩ := h'
  obtain ⟨ex, au, -⟩ := hb
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').2.1 (by rw [← e, ← e', ex]) fun τ i => ?_
  obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
  refine ⟨cf, by rw [c₁]; exact (t _).isUnit, c₂, ?_⟩
  have k := (GlobalTheory.FrameLift.comb_iff d.m e (fun j => (p.tan τ j).1) cf (ex ▸ (p'.tan τ i).1)).1 hcf
  rw [funext (hu τ), hu'] at k
  exact k

theorem lact_conj_eq_rmul : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hLev σ₂ hσ₂ k₂ k δ hG hδ hOv γ₂ hγ₂ x hx x' hM
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
    unfold GoodEmb at hσ₂ ⊢
    rw [← hσ₂]
    rfl
  have hU := hL.unf _ hσ
  have hU₂ := hL₂.unf _ hσ₂
  have hγx : lact γ₂ x ∈ ((U₂ σ₂).X k₂).dom := (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ hγ₂ x).2 hx
  obtain ⟨t₀, ht₀⟩ := (hU₂.2.2.2.1 k₂ k₂ ⟨x, hx⟩ ⟨lact γ₂ x, hγx⟩).2
    ⟨γ₂, hγ₂, ExtFPf.oneF _, ExtFPf.oneF_mem _, by rw [ExtFPf.rmul_oneF]⟩
  have hM' : Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ (lact γ₂ x) (lact (MulAut.conj δ γ₂) x') := by
    intro τ h₂ h₁
    have e := hM τ h₂ h₁
    show ((MulAut.conj δ γ₂ : GL _ _) : Matrix _ _ _).map τ * mat x' ⟨τ, h₁⟩ =
      (δ : Matrix _ _ _).map τ * ((γ₂ : Matrix _ _ _).map τ * mat x ⟨τ, h₂⟩)
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul (f := τ), ← Matrix.map_mul (f := τ),
      ← Units.val_mul, ← Units.val_mul, MulAut.conj_apply, inv_mul_cancel_right]
  obtain ⟨hx', t₁, -, y, hy₁, hy₂⟩ := hOv x hx x' hM
  obtain ⟨hx'', t₂, -, y', hy₁', hy₂'⟩ := hOv (lact γ₂ x) hγx _ hM'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨t', ht'⟩ := exists_frBor_of_frOver d hy₂ hy₂' ht₀
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have hb := G.2.1 _ _ _ _ _ (G.2.1 _ _ _ _ _ hy₁ ht') (G.2.2.1 _ _ _ hy₁')
  obtain ⟨γ, hγ, b, hb', e⟩ := (hU.2.2.2.1 k k ⟨x', hx'⟩ ⟨_, hx''⟩).1 ⟨_, hb⟩
  exact ⟨γ, hγ, b, hb', eq_of_heq (Sigma.mk.inj e).2⟩

end GlobalTheory.LevModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticGroupConjIsometryMovesCoverPointStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticGroup_conj_isometry_moves_cover_point : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  first | exact @GlobalTheory.LevModel.lact_conj_eq_rmul | exact GlobalTheory.LevModel.lact_conj_eq_rmul | (intros; apply GlobalTheory.LevModel.lact_conj_eq_rmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLe
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem closure_point_topologicalKrullDim : ∀ (X : Scheme.{0}) (n : ℕ) (z : X), topologicalKrullDim X = n → ∃ e : ℕ, e ≤ n ∧ topologicalKrullDim (closure ({z} : Set X)) = e ∧ ∀ x, z ⤳ x → x ≠ z → 1 ≤ e := by
  intro X n z hX
  set S : Set X := closure ({z} : Set X) with hS
  have hle : topologicalKrullDim S ≤ n := hX ▸ topologicalKrullDim_subspace_le X S
  have hzS : z ∈ S := subset_closure rfl
  haveI : Nonempty S := ⟨⟨z, hzS⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim S := Order.krullDim_nonneg_iff.mpr
    ⟨⟨closure {(⟨z, hzS⟩ : S)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim S = e := by
    generalize topologicalKrullDim S = d at hle h0 ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := hle
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m => exact ⟨m, rfl⟩
  refine ⟨e, ?_, he, ?_⟩
  · rw [he] at hle; exact_mod_cast hle
  · intro x hzx hxz
    have hxS : x ∈ S := specializes_iff_mem_closure.mp hzx
    let x' : S := ⟨x, hxS⟩
    let z' : S := ⟨z, hzS⟩
    have hsp : z' ⤳ x' := (Topology.IsInducing.subtypeVal.specializes_iff).mp hzx
    have hns : ¬ x' ⤳ z' := fun h => hxz (congrArg Subtype.val (h.antisymm hsp).eq)
    let A : IrreducibleCloseds S := ⟨closure {x'}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds S := ⟨closure {z'}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hAB : A < B := by
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x'} ⊆ closure {z'}
        exact specializes_iff_closure_subset.mp hsp
      · intro h
        apply hns
        have : closure ({x'} : Set S) = closure {z'} :=
          congrArg (fun C : IrreducibleCloseds S => (C : Set S)) h
        exact specializes_iff_closure_subset.mpr this.symm.subset
    have h1 : (1 : WithBot ℕ∞) ≤ topologicalKrullDim S := Order.one_le_krullDim_iff.mpr ⟨A, B, hAB⟩
    rw [he] at h1
    exact_mod_cast h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopologicalKrullDimClosurePointLeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topologicalKrullDim_closure_point_le : ∀ (X : Scheme.{0}) (n : ℕ) (z : X), topologicalKrullDim X = n → ∃ e : ℕ, e ≤ n ∧ topologicalKrullDim (closure ({z} : Set X)) = e ∧ ∀ x, z ⤳ x → x ≠ z → 1 ≤ e := by
  first | exact @GlobalTheory.closure_point_topologicalKrullDim | exact GlobalTheory.closure_point_topologicalKrullDim | (intros; apply GlobalTheory.closure_point_topologicalKrullDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultNsmulOfQadd
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    rw [zero_nsmul, (CartierDiv.isEqn_zero z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero]
    simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul_of_qadd {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ),
    IsProjOver p → ∀ (N : LB X) (a b : ℚ) (D B : X → ℚ), QNum p N a D → QNum p N b B →
      QNum p N (a + b) (D + B) := by
  intro X _ _ p hp N a b D B hD hB
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨m, D₀, hm, hD₀, rfl, hDn⟩ := hD
  obtain ⟨m', B₀, hm', hB₀, rfl, hBn⟩ := hB
  refine ⟨m * m', m' • D₀ + m • B₀, Nat.mul_pos hm hm', (eff_nsmul_of_qadd hD₀ m').add
    (eff_nsmul_of_qadd hB₀ m), ?_, ?_⟩
  · funext z
    simp only [Pi.add_apply, qWeil, CartierDiv.mult_add, mult_nsmul_of_qadd]
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    push_cast
    field_simp
  · intro C hC
    let hLB (D : CartierDiv X) : (toLB D).IsLB := (presents_toLB D).isLB
    let f : CartierDiv X →+ Pic X := AddMonoidHom.mk' (fun D => cls _ (hLB D)) fun D E =>
      (cls_eq_iff _ (isLB_tens (hLB D) (hLB E))).2
        ((presents_toLB _).lbIso ((presents_toLB D).tens (presents_toLB E)))
    have e := hC.interNumRed_of_cls_eq_add (N := toLB (m' • D₀ + m • B₀))
      (A := lbPow (toLB D₀) m') (B := lbPow (toLB B₀) m) hH (hLB (m' • D₀ + m • B₀))
      (isLB_lbPow (hLB D₀) m') (isLB_lbPow (hLB B₀) m)
      (by
        rw [cls_lbPow (hLB D₀), cls_lbPow (hLB B₀)]
        change f (m' • D₀ + m • B₀) = m' • f D₀ + m • f B₀
        rw [map_add, map_nsmul, map_nsmul])
    rw [hC.interNumRed_lbPow hH (hLB D₀), hC.interNumRed_lbPow hH (hLB B₀)] at e
    have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    have h2 : (m' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm'.ne'
    have hD' := hDn C hC
    have hB' := hBn C hC
    rw [e]
    push_cast
    rw [div_eq_iff h1] at hD'
    rw [div_eq_iff h2] at hB'
    rw [div_eq_iff (mul_ne_zero h1 h2), hD', hB']
    ring

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstant
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteGroupSchemeLength

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  have h1 : Module.length R S = Module.length S S :=
    Module.length_eq_of_surjective (R := S) (M := S) (S := R) e.surjective
  let l : R ≃ₗ[R] S :=
    { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
      map_add' := e.map_add,
      map_smul' := fun r x => by
        simp only [smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  rw [l.length_eq, h1]

theorem isClosed_singleton_of_isFinite {k : Type} [Field k] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of k)) [IsFinite f] (z : H) : IsClosed ({z} : Set H) := by
  have hz : f z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have hc : IsClosed (f ⁻¹' {IsLocalRing.closedPoint k}) :=
    (IsLocalRing.isClosed_singleton_closedPoint k).preimage f.continuous
  have hd := (f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)).to_subtype
  have := hc.isClosedEmbedding_subtypeVal.isClosedMap {⟨z, hz⟩} (isClosed_discrete _)
  rwa [Set.image_singleton] at this

theorem length_stalk_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  intro k _ _ G _ hf x x'
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have hsurj : ∀ y : G.left, ∃ a : 𝟙_ (Over (Sp k)) ⟶ G, a.left pt = y := by
    intro y
    have hy := isClosed_singleton_of_isFinite G.hom y
    exact ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
      pointOfClosedPoint_apply G.hom y hy _⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨a', rfl⟩ := hsurj x'
  let φ := GrpObj.mulRight (a⁻¹ * a')
  have h : a ≫ φ.hom = a' := by
    have : a ≫ φ.hom = a * (a⁻¹ * a') := by
      simp [φ, comp_lift_assoc, Hom.mul_def]
    rw [this, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  have hx : φ.hom.left (a.left pt) = a'.left pt := by
    rw [← h]; rfl
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso φ).hom)
  have hi : IsIso (φ.hom.left.stalkMap (a.left pt)) :=
    ((isIso_iff_isIso_stalkMap φ.hom.left).1 inferInstance).2 _
  let e := (asIso (φ.hom.left.stalkMap (a.left pt))).commRingCatIsoToRingEquiv
  rw [← length_self_eq_of_ringEquiv e]
  congr 1 <;> rw [hx]

end GlobalTheory.FiniteGroupSchemeLength
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupSchemeStalkLengthConstantStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_group_scheme_stalk_length_constant : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsFinite G.hom → ∀ x x' : G.left, Module.length (G.left.presheaf.stalk x) (G.left.presheaf.stalk x) = Module.length (G.left.presheaf.stalk x') (G.left.presheaf.stalk x') := by
  first | (exact @GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (exact GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq) | (intros; apply GlobalTheory.FiniteGroupSchemeLength.length_stalk_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRank

theorem etale_pullback_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (K : Over S) (i : K ⟶ A) (c : ℕ) [Mono i] [IsFinite K.hom]
    [Flat K.hom] (hi : i ^ c = 1) (k : Type) [Field k] (hc : (c : k) ≠ 0) (y : Sp k ⟶ S) :
    Etale (pullback.snd K.hom y) := by
  let A' := (Over.pullback y).obj A
  let K' := (Over.pullback y).obj K
  let i' : K' ⟶ A' := (Over.pullback y).map i
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback y A hA
  have := hA'.comm
  have := hA'.smooth
  have hc' : IsUnit (c : Γ(Sp k, ⊤)) := by
    have := (Ne.isUnit hc).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this
  have hTe : Etale (torsion A' c).hom := GrpTangent.etale_torsion A' hc'
  have hi' : i' ^ c = 1 := by
    have h := map_pow (Over.pullback y).homMonoidHom i c
    rw [hi, map_one] at h
    exact h.symm
  obtain ⟨j, hj, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A' c i' hi'
  have : Mono i' := inferInstance
  have hjm : Mono j := mono_of_mono_fac hj
  have hjml : Mono j.left := inferInstanceAs (Mono ((Over.forget _).map j))
  have hju : FormallyUnramified j.left := inferInstance
  have hKu : FormallyUnramified K'.hom := by
    rw [← Over.w j]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ hju inferInstance
  have : Flat K'.hom := by change Flat (pullback.snd K.hom y); infer_instance
  have : IsFinite K'.hom := by change IsFinite (pullback.snd K.hom y); infer_instance
  have : LocallyOfFinitePresentation K'.hom := inferInstance
  exact Etale.of_formallyUnramified_of_flat K'.hom

theorem finrank_eq_card : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (K : Over S) (i : K ⟶ A) (c : ℕ), Mono i → IsFinite K.hom → Flat K.hom → i ^ c = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (y : Sp k ⟶ S) (z : Sp k), K.hom.finrank (y z) = Nat.card (Over.mk y ⟶ K) := by
  intro S A _ _ hA K i c hi hfin hfl hic k _ _ hc y z
  have het := etale_pullback_snd A hA K i c hic k hc y
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank (pullback.snd K.hom y) (𝟙 (Sp k)) z
  have hz : (𝟙 (Sp k) : Sp k ⟶ Sp k) z = z := rfl
  rw [hz, Scheme.Hom.finrank_pullback_snd] at hcard
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun x => Over.homMk (x.1 ≫ pullback.fst K.hom y) (by
        change (x.1 ≫ pullback.fst K.hom y) ≫ K.hom = y
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp])
      invFun := fun g => ⟨pullback.lift g.left (𝟙 _) (by
        rw [Category.id_comp]; exact Over.w g), pullback.lift_snd _ _ _⟩
      left_inv := fun x => Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans x.2.symm))
      right_inv := fun g => Over.OverMorphism.ext (pullback.lift_fst _ _ _) }

end GlobalTheory.TorsionRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPointsStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_finiteFlat_torsion_subscheme_eq_card_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (K : Over S) (i : K ⟶ A) (c : ℕ), Mono i → IsFinite K.hom → Flat K.hom → i ^ c = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (y : Sp k ⟶ S) (z : Sp k), K.hom.finrank (y z) = Nat.card (Over.mk y ⟶ K) := by
  first | (exact @GlobalTheory.TorsionRank.finrank_eq_card) | (exact GlobalTheory.TorsionRank.finrank_eq_card) | (intros; apply GlobalTheory.TorsionRank.finrank_eq_card  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialMod
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open OverMove in
theorem levMove_comm_levelMap_of_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (g gA : Dw.La →ₗ[𝓞 E] Dw.La), IsIso ρ₂ → IsLevMove ρ₂ ν₂ g gA → (∀ a, g a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ρ₂ ≫ d.r = d.r ∧ ν₂.φ ≫ d.m.φ = d.m.φ := by
  intro E _ _ _ H Dw l Xo c n d _ hLev hA2 hover ρ₂ ν₂ g gA _ hmv hg
  have hL : Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  obtain ⟨hd, hM, -, -, -, hE, -⟩ := hLev
  have hA : l.A = 1 := Nat.eq_one_of_dvd_one (hA2 ▸ hd.2.2)
  have hK : KA l ≤ KA d.l₂ := by
    show IntermediateField.adjoin ℚ {H.rt0, zeta l.A} ≤ IntermediateField.adjoin ℚ {H.rt0, zeta d.l₂.A}
    rw [hA, hA2]
  have hb := hover hK
  have hred : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  have hpd : d.pd = d.l₂.M / l.M := by
    rw [hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]
  have L₁ : Lev d.m := ⟨hpd ▸ hE.1, hE.2⟩
  obtain ⟨o, ⟨p⟩⟩ := obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (d.r ≫ Xo.s) d.r rfl rfl
    (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨u, hu, F₁⟩ := exists_fib p L₁ (x := 𝟙 _) (Category.id_comp _)
  obtain ⟨u₂, hu₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₂ u
  have hA1 : ∀ a, d.Xo₂.univ.etaA a = 1 := fun a => by
    have := d.Xo₂.univ.etaA_ker a
    rwa [hA2, one_smul] at this
  have hfix : ∀ a, (d.Xo₂.univ.eta (g a) ^ (d.l₂.M / l.M)).left = (d.Xo₂.univ.eta a ^ (d.l₂.M / l.M)).left :=
    fun a => by
      apply d.m.cart.1.hom_ext
      · rw [L₁.1, L₁.1, LevelActionLaws.eta_congr Xo (hg a)]
      · rw [LevelFibre.sec_w, LevelFibre.sec_w]
  have hone : (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left ≫ ν₂.φ = ρ₂ ≫ (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left := by
    have := hmv.2.2 0
    rwa [hA1, hA1] at this
  have F₂ : Fib o u₂ := by
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hu₂, ← Category.assoc, F₁.1, Category.id_comp, ← hfix, pow_left_comp ν₂ (hmv.2.1 a), Category.id_comp, hfix]
    · rw [hu₂, ← Category.assoc, F₁.2, Category.id_comp, Category.id_comp, hA1, one_pow]
      exact hone
  obtain ⟨q, hq⟩ := exists_objMap F₂ L₁
  have hr : (𝟙 _ ≫ ρ₂) ≫ d.r = d.r := by
    refine (Xo.rep d.Xo₂.X (d.r ≫ Xo.s) hred o).unique ⟨?_, ⟨q⟩⟩ ⟨rfl, ⟨p⟩⟩
    rw [Category.id_comp, Category.assoc, hb, ← Category.assoc, hmv.1]
  obtain ⟨q', hq'⟩ := LevelFibre.sab_cast hr q.toSABMap
  have e : p.toSABMap.φ = q'.φ := sabMap_eq_of_level_eq hL obj_isAbelianScheme_dim_rigidified_sym E H Dw l _ _ _ _ _ _
    _ _ Xo.univ o _ (Or.inl hred) p.toSABMap q' fun a => ⟨_, p.eta a, by rw [hq']; exact (q.eta a).trans (by rw [hr])⟩
  rw [hq', hq, ← hu, hu₂, Category.assoc] at e
  have : IsIso u.φ := u.cart.1.isIso_fst_of_isIso
  refine ⟨by simpa using hr, ((cancel_epi u.φ).1 e).symm⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialModStatement
open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levMove_comp_r_eq_of_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (g gA : Dw.La →ₗ[𝓞 E] Dw.La), IsIso ρ₂ → IsLevMove ρ₂ ν₂ g gA → (∀ a, g a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ρ₂ ≫ d.r = d.r ∧ ν₂.φ ≫ d.m.φ = d.m.φ := by
  first | exact @GlobalTheory.levMove_comm_levelMap_of_trivial_mod | exact GlobalTheory.levMove_comm_levelMap_of_trivial_mod | (intros; apply GlobalTheory.levMove_comm_levelMap_of_trivial_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem not_mem_div_uniformizer_pow : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → ∀ x : Ω, x ≠ 0 → ∃ n : ℕ, x / algebraMap K Ω (algebraMap R K π) ^ n ∉ V := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ x hx
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable

  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨r, rfl⟩
    exact this

  have hKV : ∀ c : K, algebraMap K Ω c ∈ V → ∃ r : R, algebraMap R K r = c := by
    intro c hc
    have : c ∈ V.toSubring.comap (algebraMap K Ω) := hc
    rw [hV] at this
    exact this
  have halgK : IsAlgebraic K x⁻¹ := Algebra.IsAlgebraic.isAlgebraic _
  have halgR : IsAlgebraic R x⁻¹ := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨d, hd0, hint⟩ := halgR.exists_integral_multiple
  let f : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV
  letI : Algebra R V := f.toAlgebra
  haveI : IsScalarTower R V Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hintV : IsIntegral V (d • x⁻¹) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintV
  have hyV : d • x⁻¹ ∈ V := by rw [← hy]; exact y.2

  have hfin : FiniteMultiplicity π d := FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hd0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ π ^ n ∣ d := by
    obtain ⟨m, hm⟩ := hfin
    exact ⟨m + 1, hm⟩
  refine ⟨n, fun hmem => hn ?_⟩
  have hprod : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) ∈ V := V.mul_mem _ _ hyV hmem
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have heq : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) =
      algebraMap K Ω (algebraMap R K d / algebraMap R K π ^ n) := by
    rw [Algebra.smul_def, map_div₀, map_pow]
    change (algebraMap K Ω) (algebraMap R K d) * x⁻¹ * _ = _
    field_simp
  rw [heq] at hprod
  obtain ⟨r, hr⟩ := hKV _ hprod
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_pow, hr]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPowStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_mem_div_uniformizer_pow_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → ∀ x : Ω, x ≠ 0 → ∃ n : ℕ, x / algebraMap K Ω (algebraMap R K π) ^ n ∉ V := by
  first | exact @GlobalTheory.not_mem_div_uniformizer_pow | exact GlobalTheory.not_mem_div_uniformizer_pow | (intros; apply GlobalTheory.not_mem_div_uniformizer_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ChernDegreeBaseChange

theorem exists_baseChange {F E : Type} [Field F] [Field E] (ρ : F →+* E) (Y : Var F) :
    ∃ (Y' : Var E) (r : Y'.X ⟶ Y.X), Y'.dim = Y.dim ∧ IsPullback r Y'.str Y.str (spMap ρ) := by
  have H := IsPullback.of_hasPullback Y.str (spMap ρ)
  generalize Limits.pullback.fst Y.str (spMap ρ) = r at H
  generalize Limits.pullback.snd Y.str (spMap ρ) = q at H
  have hs : SmoothOfRelativeDimension Y.dim q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange Y.dim
    MorphismProperty.of_isPullback H Y.smooth_str
  have hg : GeometricallyIntegral q :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H Y.geometricallyIntegral_str
  have hc : GeometricallyConnected q :=
    ⟨fun _ _ y _ fst snd h =>
      have := GeometricallyIntegral.geometrically_isIntegral (f := q) y fst snd h
      inferInstance⟩
  obtain ⟨Y', e, hd, he⟩ := Var.exists_iso q Y.dim (ProjSpace.isProjOver_of_isPullback_spMap ρ H Y.isProjOver)
  refine ⟨Y', e.inv ≫ r, hd, ?_⟩
  refine H.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simpa using he.symm
  · simp
  · simp

theorem chernDegree_of_complex (h : GlobalTheory.Published.ChernDegreeComplex) : GlobalTheory.Published.ChernDegree := by
  intro F _ Y σ Δ L r hr φ hφ
  obtain ⟨Y', π, hd, H⟩ := exists_baseChange σ Y
  have := CxPts.compactSpace (RingHom.id ℂ) Y'.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (RingHom.id ℂ) Y'.isProjOver
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts Y'.str (RingHom.id ℂ) → CxPts Y.str σ, (∀ z, (m z).1 = z.1 ≫ π) ∧
      Function.Bijective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, bijective_bcMap H _⟩
  let Φ : CxPts Y'.str (RingHom.id ℂ) ≃ₜ CxPts Y.str σ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hb) (continuous_of_comp hm)
  have hΦ : ∀ z, (Φ z).1 = z.1 ≫ π := hm
  have hL' := LB.isLB_pull hr.isLB π
  obtain ⟨s, hs⟩ := exists_isRatSec hL'
  have hp := presents_divOfRatSec hL' hs
  obtain ⟨h₁, h₂⟩ := h Y' _ _ s hp (ChernTransfer.pullW hΦ φ) (ChernTransfer.isCInf_pullW hΦ hφ)
  have hi : Y'.inter (fun _ => divOfRatSec hL' hs) = Y.inter fun _ => Δ := by
    letI := σ.toAlgebra
    rw [Var.inter_eq_of_toPic_eq (fun _ => hL') (fun _ => hp.toPic_eq),
      Var.inter_eq_of_toPic_eq (fun _ => hr.isLB) (fun _ => hr.toPic_eq), hd]
    exact FieldChangeInter.interNum_pull (f := Y.str) (f' := Y'.str) H (L := fun _ => L) fun _ => hr.isLB
  have hsm : SmoothOfRelativeDimension Y.dim Y'.str := hd ▸ Y'.smooth_str
  have e (ε) := ChernTransfer.chernPart_pullW hΦ (AnRead.all _ _ Y.dim) (AnRead.all _ _ Y.dim) hφ ε
  rw [hi] at h₂
  rw [hd] at h₁ h₂
  simp only [Weight.ChernIntegrableOn, Weight.chernInt, integrableOn_univ, Measure.restrict_univ, e,
    integral_map_equiv, integrable_map_equiv] at h₁ h₂ ⊢
  exact ⟨h₁, h₂⟩

end GlobalTheory.ChernDegreeBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCaseStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernDegree := by
  first | exact @GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | exact GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex | (intros; apply GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

theorem under_under_of_compat {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have : algebraMap (𝓞 K) (𝓞 L) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 L) x := by
    apply RingOfIntegers.ext
    exact hc (x : F)
  rw [this]

theorem finEval_ideleMap_localIdele {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.under (𝓞 F) ≠ w.under (𝓞 F)) (a : (v.adicCompletion K)ˣ) :
    Units.map (GlobalTheory.IdeleNormChar.finEval w) (ideleMap K L (Neutral.B1.localIdele K v a)) = 1 := by
  have hne : w.under (𝓞 K) ≠ v := fun h => hv (h ▸ under_under_of_compat hc w)
  apply Units.ext
  show finiteCompletionMap K L w ((Neutral.B1.localIdele K v a : AdeleRing (𝓞 K) K).2 (w.under (𝓞 K))) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt K v a).2 _ hne, map_one]

theorem isSplitAt_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {v w : HeightOneSpectrum (𝓞 E)}
    (hw : GlobalTheory.UnitaryBC.IsSplitAt w)
    (h : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    GlobalTheory.UnitaryBC.IsSplitAt v := by
  obtain ⟨u, hu, hu'⟩ := hw
  by_cases hvw : v = w
  · subst hvw; exact ⟨u, hu, hu'⟩
  · exact ⟨w, Ne.symm hvw, h.symm⟩

theorem conjQuot_nsUnits_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.UnitaryBC.IsSplitAt w → ∀ u ∈ GlobalTheory.MuExist.nsUnits E, GlobalTheory.ConsEta.conjQuot E w u = 1 := by
  intro E _ _ _ w hw u hu
  have key : GlobalTheory.MuExist.nsUnits E ≤ (conjQuot E w).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w', a, hw', -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hne : w' ≠ w := fun h => hw' (h ▸ hw)
    have hunder : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
      fun h => hw' (isSplitAt_of_under_eq hw h)
    have h1 : Units.map (GlobalTheory.IdeleNormChar.finEval w) (Neutral.B1.localIdele E w' a) = 1 :=
      Units.ext ((Neutral.B1.localIdele_isSupportedAt E w' a).2 w hne.symm)
    have h2 : Units.map (GlobalTheory.IdeleNormChar.finEval w)
        (ideleConj (maximalRealSubfield E) E (Neutral.B1.localIdele E w' a)) = 1 :=
      finEval_ideleMap_localIdele (F := maximalRealSubfield E)
        (alg := (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra)
        (fun x => (conj (maximalRealSubfield E) E).commutes x) w w' hunder a
    simp only [conjQuot, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, _root_.map_div, h1, h2, div_one]
  exact key hu

end GlobalTheory.ConsEta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjQuot_eq_one_of_mem_nsUnits_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), GlobalTheory.UnitaryBC.IsSplitAt w →
    ∀ u ∈ GlobalTheory.MuExist.nsUnits E, GlobalTheory.ConsEta.conjQuot E w u = 1 := by
  first | exact @GlobalTheory.ConsEta.conjQuot_nsUnits_eq_one | exact GlobalTheory.ConsEta.conjQuot_nsUnits_eq_one | (intros; apply GlobalTheory.ConsEta.conjQuot_nsUnits_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelsOfChain
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

namespace KerGrp

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

def sub (T : Over S) : Subgroup (T ⟶ A) := (IsMonHom.monoidHom f T).ker

theorem mem_sub {T : Over S} (x : T ⟶ A) : x ∈ sub f T ↔ x ≫ f = 1 := by
  simp [sub, MonoidHom.mem_ker]

def pts : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (sub f T.unop)
  map {T T'} g := GrpCat.ofHom
    { toFun := fun x => ⟨g.unop ≫ x.1, (mem_sub f _).2 (by
        rw [Category.assoc, (mem_sub f _).1 x.2, MonObj.comp_one])⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp g h := by ext x; exact Category.assoc _ _ _

theorem fst_comp : pullback.fst f η[B] ≫ f = 1 := by
  rw [pullback.condition, Hom.one_def, toUnit_unique (pullback.snd f η[B]) (toUnit _)]

def lift {T : Over S} (x : T ⟶ A) (hx : x ≫ f = 1) : T ⟶ ker f :=
  pullback.lift x (toUnit T) (by rw [hx, Hom.one_def])

@[simp] theorem lift_fst {T : Over S} (x : T ⟶ A) (hx : x ≫ f = 1) : lift f x hx ≫ pullback.fst f η[B] = x :=
  pullback.lift_fst _ _ _

theorem hom_ext {T : Over S} {y z : T ⟶ ker f} (h : y ≫ pullback.fst f η[B] = z ≫ pullback.fst f η[B]) :
    y = z :=
  pullback.hom_ext h (toUnit_unique _ _)

def rep : (pts f ⋙ forget _).RepresentableBy (ker f) where
  homEquiv {T} :=
    { toFun := fun y => (⟨y ≫ pullback.fst f η[B], (mem_sub f _).2 (by rw [Category.assoc, fst_comp,
        MonObj.comp_one])⟩ : sub f T)
      invFun := fun x => lift f (x : sub f T).1 ((mem_sub f _).1 (x : sub f T).2)
      left_inv := fun y => hom_ext f (lift_fst _ _ _)
      right_inv := fun x => Subtype.ext (lift_fst _ _ _) }
  homEquiv_comp g y := Subtype.ext (Category.assoc _ _ _)

@[instance_reducible]
def grp : GrpObj (ker f) := GrpObj.ofRepresentableBy _ (pts f) (rep f)

theorem mul_fst {T : Over S} (y z : T ⟶ ker f) :
    letI := grp f
    (y * z) ≫ pullback.fst f η[B] = (y ≫ pullback.fst f η[B]) * (z ≫ pullback.fst f η[B]) := by
  letI := grp f
  have := ((yonedaGrpObjIsoOfRepresentableBy (ker f) _ (rep f)).hom.app (.op T)).hom.map_mul y z
  exact congrArg Subtype.val this

theorem isMonHom_fst : letI := grp f; IsMonHom (pullback.fst f η[B]) := by
  letI := grp f
  exact isMonHom_of_mul _ fun T y z => mul_fst f y z

instance mono_fst : Mono (pullback.fst f η[B]) := ⟨fun _ _ h => hom_ext f h⟩

end KerGrp

end GlobalTheory.IwLevel
end
end
