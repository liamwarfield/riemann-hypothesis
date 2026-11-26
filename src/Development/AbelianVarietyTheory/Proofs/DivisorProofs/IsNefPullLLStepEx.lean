module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIntegralFlagModelOfSmoothCoefficientFielStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushInvertibleOfHasTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv sabT sabM)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.FlagMod GlobalTheory.LocM GlobalTheory.NefCurveTest
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.NefStep

section Span

variable {X : Scheme.{0}} {F : X.Modules} {J : Type} {T : J → X.Opens} {r : ℕ}
  (w : ∀ j, Fin r → Γ(F, T j)) (l : ∀ j, Fin r → Γ(VB.dual F, T j))

def spanSub : Sub F where
  sec V :=
    { carrier := {s | ∀ j (W : X.Opens) (h₁ : W ≤ V) (h₂ : W ≤ T j),
        resM F h₁ s = ∑ a, dualApp (l j a) h₂ (resM F h₁ s) • resM F h₂ (w j a)}
      add_mem' := fun hs ht j W h₁ h₂ => by
        simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
        rw [← hs j W h₁ h₂, ← ht j W h₁ h₂]
      zero_mem' := fun j W h₁ h₂ => by simp
      smul_mem' := fun a s hs j W h₁ h₂ => by
        simp only [resM_smul, map_smul, smul_assoc, ← Finset.smul_sum]
        rw [← hs j W h₁ h₂] }
  res_mem h s hs j W h₁ h₂ := by rw [resM_resM]; exact hs j W _ h₂
  mem_of_local {V s} H j W h₁ h₂ := by
    choose U hU hx hs using fun x : W => H x (h₁ x.2)
    refine Twist.sec_ext_of_cover (fun x => W ⊓ U x) (fun _ => inf_le_left)
      (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx', hx _⟩) fun x => ?_
    have := hs x j (W ⊓ U x) inf_le_right (inf_le_left.trans h₂)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, resM_smul, ← dualApp_resM, resM_resM] at this ⊢
    exact this

theorem exists_sub_det {L : LB X} (hL : L.IsLB) (w : ∀ j, Fin r → Γ(F, L.U j)) (l : ∀ j, Fin r → Γ(VB.dual F, L.U j))
    (hl : ∀ j a b, dualApp (l j a) le_rfl (w j b) = if a = b then 1 else 0)
    (B : ∀ j j', Matrix (Fin r) (Fin r) Γ(X, L.U j ⊓ L.U j'))
    (hB : ∀ j j' b, resM F inf_le_right (w j' b) = ∑ a, B j j' a b • resM F inf_le_left (w j a))
    (hg : ∀ j j', (L.g j j').val = (B j j').det) :
    ∃ (W : X.Modules) (i : W ⟶ F), Mono i ∧ IsVB W r ∧ LBIso L (det W r) := by
  have hl' (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) (a) :
      dualApp (l j a) h (∑ b, c b • resM F h (w j b)) = c a := by
    have e (b) : dualApp (l j a) h (resM F h (w j b)) = if a = b then 1 else 0 := by
      rw [dualApp_resM (l j a) le_rfl h, hl]; split_ifs <;> simp
    simp [e]
  let N := spanSub w l
  have hm (j) (b) : w j b ∈ N.sec (L.U j) := fun j' V h₁ h₂ => by
    have e := congrArg (resM F (le_inf h₂ h₁)) (hB j' j b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, resM_smul, resM_resM] at e
    rw [e]
    simp only [hl']
  have hi (j) {V : X.Opens} (h : V ≤ L.U j) (c : Fin r → Γ(X, V)) :
      N.incl.app V (∑ b, c b • resM _ h (N.mkSec _ (hm j b))) = ∑ b, c b • resM F h (w j b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Scheme.Modules.Hom.app_smul, app_resM, Sub.incl_app_mkSec]
  have he (j) : IsFrame fun b => N.mkSec _ (hm j b) := isFrame_iff.2 fun V h => by
    refine ⟨Fintype.linearIndependent_iff.2 fun c hc a => ?_, fun s _ =>
      (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun a => dualApp (l j a) h (resM F le_rfl (N.incl.app V s)),
        N.incl_app_injective V ((hi j h _).trans ?_)⟩⟩
    · rw [← hl' j h c a, ← hi, hc, map_zero, map_zero]
    · exact (N.incl_app_mem s j V le_rfl h).symm.trans (resM_self _ _)
  refine ⟨N.toMod, N.incl, inferInstance, lbIso_det_of_frames hL _ he fun j j' => Units.ext ?_⟩
  rw [hg, IsFrame.val_detUnit, Module.Basis.det_apply]
  congr 1
  ext a b
  have e : resM _ inf_le_right (N.mkSec _ (hm j' b)) =
      ∑ a, B j j' a b • (he j).basis (inf_le_left : L.U j ⊓ L.U j' ≤ _) a := by
    simp only [IsFrame.basis_apply]
    refine N.incl_app_injective _ (Eq.trans ?_ (hi j _ _).symm)
    rw [app_resM, Sub.incl_app_mkSec, hB]
  rw [Module.Basis.toMatrix_apply, e, Module.Basis.repr_sum_self]

end Span

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)


open Classical in
theorem LL_stepEx_g_inv (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) (k k' : F.J) :
    ((show Γ(Z, F.U k ⊓ F.U k')ˣ from (F.LL (stepEx σ n)).g k k')⁻¹).val =
      ∏ a : Fin n, F.B k k' σ (a.castLE hn) (a.castLE hn) := by
  have e : (∏ ix, F.T k k' ix ^ (-stepEx σ n ix))⁻¹ = ∏ a : Fin n, F.T k k' (some ⟨σ, a.castLE hn⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun a : Fin n => (some ⟨σ, a.castLE hn⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun a _ => ?_).symm
    · simpa using h
    · rcases ix with _ | ⟨σ', i⟩
      · simp [stepEx]
      · have : ¬ (σ' = σ ∧ (i : ℕ) < n) := by
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, by simp, rfl⟩
        simp [stepEx, this]
    · simp [stepEx]
  refine (congrArg Units.val e).trans ?_
  rw [Units.coe_prod]
  rfl

theorem left_vecAt {S S' : Type} [CommRing S] [CommRing S'] (k : F.J) (φ : S →+* S') {z : Sp S ⟶ Z} {z' : Sp S' ⟶ Z}
    (e : spMap φ ≫ z = z') (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k) (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z' hz' rfl σ a)).left = spMap (Formalism.L2.Pj.dualMap φ) ≫ (tv (F.vecAt k z hz rfl σ a)).left := by
  subst e
  rw [← F.tanPull_vecAt k φ z hz hz' rfl rfl (Category.assoc _ _ _).symm, tanPull_left]

theorem exists_step_sub {C : Scheme.{0}} [C.IsSeparated] [PreconnectedSpace C] (g : C ⟶ Z) {t : SAB H C}
    (m : SABMap t Y.t (g ≫ π)) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (i : W ⟶ Lie t.G), Mono i ∧ IsVB W n ∧
      LBIso (CechPic.dual ((F.LL (stepEx σ n)).pull g)) (det W n) := by
  have := t.semi
  obtain ⟨Ψ, hΨ⟩ := exists_tangent_equiv m
  obtain ⟨d, -, hd⟩ := exists_isVB_of_isSemiAbelian t.G
  have := hd.isQuasicoherent
  let J := {q : C.Opens × F.J // CoordOpen t q.1 ∧ q.1 ≤ g ⁻¹ᵁ F.U q.2}
  have hin {T : C.Opens} (hT : IsAffineOpen T) {U : Z.Opens} (h : T ≤ g ⁻¹ᵁ U) : ⊤ ≤ (affPt hT ≫ g) ⁻¹ᵁ U :=
    fun z hz => h (le_preimage_affPt hT hz)
  have hc : ⨆ j : J, j.1.1 = ⊤ := top_unique fun x _ => by
    obtain ⟨q, hq⟩ := Opens.mem_iSup.1 (F.cover.ge (Set.mem_univ (g x)))
    obtain ⟨T, hT, hx, hle⟩ := exists_coordOpen t (V := g ⁻¹ᵁ F.U q) hq
    exact Opens.mem_iSup.2 ⟨⟨(T, q), hT, hle⟩, hx⟩
  let M := CechPic.dual ((F.LL (stepEx σ n)).pull g)
  have hM : M.IsLB := isLB_dual (LB.isLB_pull (F.isLB_LL _) g)
  have hle (j : J) : j.1.1 ≤ M.U fun _ => j.1.2 := j.2.2.trans (GlobalTheory.LB.pull_U (L := F.LL _) g fun _ => j.1.2).ge
  have hL := TriangularFrames.isLB_refine hc hM (fun j : J => fun _ => j.1.2) hle
  let ψ (j : J) := Ψ _ j.2.1 ((affPt j.2.1.1 ≫ g) ≫ π) (Category.assoc _ _ _).symm
  let b (j : J) := (lieBasis (F.M j.1.2).toMChart _ (F.inM (hin j.2.1.1 j.2.2) rfl)).map (ψ j)
  have hb (j : J) : IsFrame (b j) := Summand.isFrame_of_affine_basis j.2.1.1 _
  choose p hp using fun j : J => F.uAt_split j.1.2 _ (hin j.2.1.1 j.2.2) σ
  have hT (j j' : J) : CoordOpen t (j.1.1 ⊓ j'.1.1) := j.2.1.mono (j.2.1.1.inf j'.2.1.1) inf_le_left
  have hh (j j' : J) := hin (hT j j').1 ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
  have hres (j : J) {T : C.Opens} (hT : CoordOpen t T) (h : T ≤ j.1.1) (a : Fin (Dw.mult σ)) :
      resM (Lie t.G) h (ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ a)) =
        Ψ T hT _ (Category.assoc _ _ _).symm (F.vecAt j.1.2 _ (hin hT.1 (h.trans j.2.2)) rfl σ a) := by
    exact (hΨ _ _ _ _ _ _ _ _ h _ _ (left_vecAt F _ _ (by rw [← Category.assoc, spMap_affPt]) _ _ _ _)).symm
  let w (j : J) (a : Fin n) : Γ(Lie t.G, j.1.1) := ψ j (F.vecAt j.1.2 _ (hin j.2.1.1 j.2.2) rfl σ (a.castLE hn))
  let f (j : J) (a : Fin n) : Γ(VB.dual (Lie t.G), j.1.1) := ∑ s, p j (a.castLE hn) s • (hb j).coord s
  let B (j j' : J) : Matrix (Fin n) (Fin n) Γ(C, j.1.1 ⊓ j'.1.1) :=
    ((F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j'))).submatrix (Fin.castLE hn) (Fin.castLE hn)
  have h₁ (j : J) (a a' : Fin n) : dualApp (f j a) le_rfl (w j a') = if a = a' then 1 else 0 := by
    have e := congrFun (congrFun (hp j) (a.castLE hn)) (a'.castLE hn)
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Fin.castLE_inj] at e
    rw [← e, dualApp_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e' : w j a' = ∑ s, F.uAt j.1.2 _ (hin j.2.1.1 j.2.2) σ s (a'.castLE hn) • (hb j).basis le_rfl s := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [w, Frames.vecAt, vec_apply, map_sum, map_smul, IsFrame.basis_apply, resM_self, b,
        Module.Basis.map_apply]
    rw [dualApp_smul, LinearMap.smul_apply, IsFrame.dualApp_coord, e', Module.Basis.repr_sum_self, GlobalTheory.LB.resG_self,
      smul_eq_mul]
  have h₂ (j j' : J) (a : Fin n) : resM (Lie t.G) (inf_le_right : j.1.1 ⊓ j'.1.1 ≤ _) (w j' a) =
      ∑ s, B j j' s a • resM (Lie t.G) inf_le_left (w j s) := by
    refine (hres j' (hT j j') inf_le_right _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [F.vecAt_eq_sum j.1.2 j'.1.2 _ (hin (hT j j').1 (inf_le_left.trans j.2.2)) _ (hh j j'), map_sum]
    refine (Finset.sum_of_injOn (Fin.castLE hn) (Fin.castLE_injective hn).injOn (fun _ _ => Finset.mem_univ _)
      (fun s _ h => ?_) fun s _ => ?_).symm
    · have hs : a.castLE hn < s := lt_of_not_ge fun h' => h ⟨⟨s, lt_of_le_of_lt h' a.2⟩, by simp, rfl⟩
      have h0 : (F.B j.1.2 j'.1.2 σ).map (ev _ _ (hh j j')) s (a.castLE hn) = 0 := F.B_map_tri _ _ σ _ hs
      rw [h0, zero_smul, map_zero]
    · rw [map_smul, ← hres j (hT j j') inf_le_left]
      rfl
  have h₃ (j j' : J) : resG C (inf_le_inf (hle j) (hle j')) (M.g (fun _ => j.1.2) fun _ => j'.1.2).val =
      (B j j').det := by
    have ht : (B j j').BlockTriangular id := fun s s' h =>
      F.B_map_tri j.1.2 j'.1.2 σ (ev _ _ (hh j j')) (i := s.castLE hn) (j := s'.castLE hn) h
    rw [Matrix.det_of_upperTriangular ht]
    simp only [B, Matrix.submatrix_apply, Matrix.map_apply, ← map_prod]
    rw [← LL_stepEx_g_inv F σ hn]
    refine left_inv_eq_right_inv (a := ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val) ?_
      ((map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _)))
    have e : ev _ _ (hh j j') ((F.LL (stepEx σ n)).g j.1.2 j'.1.2).val = resG C (inf_le_inf (hle j) (hle j'))
        (((F.LL (stepEx σ n)).pull g).g (fun _ => j.1.2) fun _ => j'.1.2).val := by
      refine Eq.trans ?_ (GlobalTheory.LB.resG_pull_g (L := F.LL _) g _ _ _).symm
      refine (ev_appLE (affPt (hT j j').1) g ((inf_le_inf j.2.2 j'.2.2).trans (Scheme.Hom.preimage_inf g).ge)
        (le_preimage_affPt _) _ _).symm.trans ?_
      exact congr($(ev_tau_self (hT j j').1 _) _)
    refine (congrArg (_ * ·) e).trans ((map_mul _ _ _).symm.trans ?_)
    exact (congrArg _ (Units.inv_mul _)).trans (map_one _)
  obtain ⟨W, i, hi, hW, e⟩ := exists_sub_det (F := Lie t.G) hL w f h₁ B h₂ h₃
  exact ⟨W, i, hi, hW, (cls_eq_iff hM hW.isLB_det).1 (((cls_eq_iff hL hM).2
    (TriangularFrames.lbIso_refine hM _ hle)).symm.trans ((cls_eq_iff hL hW.isLB_det).2 e))⟩

theorem curveTest_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] (σ : E →+* ℂ)
    {n : ℕ} (hn : n ≤ Dw.mult σ) : CurveTest K (F.LL (stepEx σ n)) := fun C _ hs hp hc g => by
  have := LieSemineg.isIntegral_curve hs hc
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : C.IsSeparated := ⟨by rw [← terminal.comp_from (strHom K C)]; infer_instance⟩
  obtain ⟨W, i, _, hW, e⟩ := exists_step_sub F g (sabM Out.proved_CubePullSt (g ≫ π) Y.t) σ hn
  have := (sabT Out.proved_CubePullSt (g ≫ π) Y.t).semi
  have hM := LB.isLB_pull (F.isLB_LL (stepEx σ n)) g
  refine (h.dual_det_nonneg hs hp hc _ hW i).trans_eq (interNum_congr_cls K _ (isLB_vecOne (isLB_dual hW.isLB_det))
    (isLB_vecOne hM) fun j => ?_)
  fin_cases j
  change cls _ (isLB_dual hW.isLB_det) = cls _ hM
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff (isLB_dual hM) hW.isLB_det).2 e, cls_dual hM, neg_neg]

theorem isNef_pull_LL_stepEx (h : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) (k : Type) [Field k]
    [CharZero k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] (g : X ⟶ Z) (σ : E →+* ℂ) {n : ℕ} (hn : n ≤ Dw.mult σ) :
    IsNef k ((F.LL (stepEx σ n)).pull g) :=
  ((curveTest_LL_stepEx F h (AlgebraicClosure k) σ hn).pull (F.isLB_LL _) g).isNef hN (LB.isLB_pull (F.isLB_LL _) g)

end GlobalTheory.NefStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomDescentQb

theorem exists_holUnif (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : ∃ L : LB A.left, Nonempty (HolUnif A L g) := by
  have := hA.proper
  have := hA.comm
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  exact ⟨_, GlobalTheory.RealMultChart.exists_holUnif_of_compact A g hg
    (GlobalTheory.RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq A hA a n hn)⟩

end GlobalTheory.HomDescentQb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS.TorFlagEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem torFlag_of_model (Y : Model Xo c (RingHom.id c.F)) (hs : SmoothOfRelativeDimension Dw.dim Y.s)
    (hb : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (LogKS.boundary Y)) (hk : LogKS.HasLogKS Y.t Y.s (LogKS.interior Y))
    (hp : PushInvertible Y.t.G Y.t.PP.L) : Nonempty (TorFlag Xo c) :=
  ⟨⟨Y, hs, hb, hk, (GlobalTheory.T.nonempty_integralFlagModel_of_smooth_coefficientField E H Dw l Xo c Y hs hp).some⟩⟩

end GlobalTheory.CompHS.TorFlagEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isFactorAH_frame_of_unif :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L₀ : LB A.left) (g : ℕ) (u₀ : HolUnif A L₀ g)
    (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.ex = u₀.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ hA L₀ g u M hL
  have hval := @valAt'_rules
  have hholprod := @holFamily_lift hval
  have hcubet := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hloc := @exists_localFrame_compatible_cube @hface hlock
  have hglob := @CubeFrame.exists_global_frame
  have hfac := @automorphyFactor_exp_linear_of_cube
  have hnf := @appellHumbert_normal_form_of_linear_exponent
  obtain ⟨t, ht⟩ := exists_gen_theta_of_isAbelianScheme ℂ A hA M hL
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hcubet A L₀ M g u hL t ht _ _ rfl rfl
  obtain ⟨fr, κ, hfr, hκ⟩ := hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3
    (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u.Λ u.discrete u.full h6 h7 hT4)
  obtain ⟨a, B, ha, hab, hfa⟩ := hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u.Λ u.discrete u.full
    h6 h7 hT4 fr κ hfr hκ
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩ := hnf g u.Λ u.discrete u.full a B ha hab
  obtain ⟨f1, f2, f3⟩ := hfr
  refine ⟨{ ex := u.ex, ex_add := u.ex_add, ex_onto := u.ex_onto, Λ := u.Λ, ker := u.ker,
            discrete := u.discrete, full := u.full, hol := u.hol,
            fr := fun i z => fr i z * Complex.exp (Q z),
            fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ },
    Hm, χ, rfl, hH, hχ, ?_⟩
  · have := f1 i
    rw [Set.inter_univ] at this
    exact this.mul hQ.cexp.differentiableOn
  · exact mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)
  · have := f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial
    rw [this]
    ring
  · intro l i z hz
    show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))
    rw [← hQn l z, hfa l i z hz, Complex.exp_sub]
    have := Complex.exp_ne_zero (Q (z + l))
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HolUnifSec

open GlobalTheory.CxPts Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ} (u : HolUnif A M g)

def pt (z : Fin g → ℂ) : CxPts A.hom (RingHom.id ℂ) :=
  ⟨(u.ex z).left, (Over.w (u.ex z)).trans (Spec.map_id _).symm⟩

theorem pt_surjective : Function.Surjective (pt u) := fun y => by
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y.1 (y.2.trans (Spec.map_id _)))
  exact ⟨z, Subtype.ext (congrArg (·.left) hz)⟩

theorem sub_mem_of_pt_eq {z w : Fin g → ℂ} (h : pt u z = pt u w) : z - w ∈ u.Λ := by
  have h' : u.ex z = u.ex w := Over.OverMorphism.ext (congrArg Subtype.val h)
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h'] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem isOpen_pre (U : A.left.Opens) : IsOpen (pt u ⁻¹' ptsIn _ _ U) := (u.hol U 0).1

theorem differentiableOn_ev (U : A.left.Opens) (f : Γ(A.left, U)) :
    DifferentiableOn ℂ (ev _ _ U f ∘ pt u) (pt u ⁻¹' ptsIn _ _ U) := (u.hol U f).2

theorem continuous_pt : Continuous (pt u) :=
  CxPts.continuous_iff.2 fun U => ⟨isOpen_pre u U, fun f => (differentiableOn_ev u U f).continuousOn⟩

theorem eq_zero_of_fderiv_eq_zero (z₀ w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) z₀ w = 0) : w = 0 := by
  refine TorusTransfer.eq_zero_of_fderiv_eq_zero u w fun U f h => ?_
  let T : A ⟶ A := (toUnit A ≫ u.ex (-z₀)) * 𝟙 A
  have hT : ∀ z, (u.ex z).left ≫ T.left = (u.ex (-z₀ + z)).left := fun z => by
    rw [← Over.comp_left, u.ex_add]
    congr 1
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _),
      Category.id_comp]
  have h1 := hw (T.left ⁻¹ᵁ U) ((T.left.app U).hom f)
    (by rw [← top_le_preimage_comp, hT, neg_add_cancel]; exact h)
  simp only [valAt'_comp, hT] at h1
  rw [fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), neg_add_cancel] at h1
  exact h1

variable {D : ℕ} (c : AlgChart A.hom (RingHom.id ℂ) D)

theorem isOpen_pre_source : IsOpen (pt u ⁻¹' c.e.source) := c.e.open_source.preimage (continuous_pt u)

theorem analyticOnNhd_chart : AnalyticOnNhd ℂ (c.e ∘ pt u) (pt u ⁻¹' c.e.source) :=
  SCV.analyticOnNhd_of_differentiableOn (isOpen_pre_source u c) (differentiableOn_euclidean.2 fun a =>
    ((differentiableOn_ev u _ (c.x a)).mono fun _ hz => c.source_subset hz).congr fun _ hz => c.apply_eq _ hz a)

theorem injective_fderiv {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) :
    Function.Injective (fderiv ℂ (c.e ∘ pt u) z₀) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => eq_zero_of_fderiv_eq_zero u z₀ w fun U f hU => ?_
  have e : ev _ _ U f ∘ pt u =ᶠ[𝓝 z₀] (ev _ _ U f ∘ c.e.symm) ∘ (c.e ∘ pt u) :=
    eventually_of_mem ((isOpen_pre_source u c).mem_nhds hz) fun z hz =>
      (congrArg (ev _ _ U f) (c.e.left_inv hz)).symm
  change fderiv ℂ (ev _ _ U f ∘ pt u) z₀ w = 0
  rw [e.fderiv_eq, fderiv_comp (f := c.e ∘ pt u) z₀ (c.differentiableAt_ev f hz hU)
    (analyticOnNhd_chart u c z₀ hz).differentiableAt, ContinuousLinearMap.comp_apply, hw, map_zero]

theorem dim_le {z₀ : Fin g → ℂ} (hz : pt u z₀ ∈ c.e.source) : D ≤ g := by
  have h1 : dimH ((c.e ∘ pt u) '' (pt u ⁻¹' c.e.source)) ≤ dimH (pt u ⁻¹' c.e.source) :=
    dimH_image_le_of_locally_lipschitzOn fun z hz => by
      obtain ⟨K, t, ht, h⟩ := (analyticOnNhd_chart u c z hz).contDiffAt.exists_lipschitzOnWith
      exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, h⟩
  rw [Set.image_comp, Set.image_preimage_eq _ (pt_surjective u), c.e.image_source_eq_target,
    Real.dimH_of_mem_nhds (c.e.open_target.mem_nhds (c.e.map_source hz)),
    Real.dimH_of_mem_nhds ((isOpen_pre_source u c).mem_nhds hz), Nat.cast_le,
    finrank_real_of_complex, finrank_real_of_complex] at h1
  simpa using h1

theorem holoOn_of_comp (R : AnRead A.hom (RingHom.id ℂ) D) {S : Set (CxPts A.hom (RingHom.id ℂ))} (hS : IsOpen S)
    {F : CxPts A.hom (RingHom.id ℂ) → ℂ} (hF : DifferentiableOn ℂ (F ∘ pt u) (pt u ⁻¹' S)) : R.HoloOn S F := by
  intro i v hv
  set c := R.chart i
  obtain ⟨z₀, hz₀⟩ := pt_surjective u (c.e.symm v)
  have hz : pt u z₀ ∈ c.e.source := hz₀ ▸ c.e.map_target hv.1
  have hv₀ : (c.e ∘ pt u) z₀ = v := by rw [Function.comp_apply, hz₀, c.e.right_inv hv.1]
  have hinj := injective_fderiv u c hz
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)) hinj
  have hrk : Module.finrank ℂ (Fin g → ℂ) = Module.finrank ℂ (V D) :=
    le_antisymm hle (by simpa using dim_le u c hz)
  let L : (Fin g → ℂ) ≃L[ℂ] V D := (LinearEquiv.ofBijective
    (fderiv ℂ (c.e ∘ pt u) z₀ : (Fin g → ℂ) →ₗ[ℂ] V D)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).1 hinj⟩).toContinuousLinearEquiv
  have hs : HasStrictFDerivAt (c.e ∘ pt u) (L : (Fin g → ℂ) →L[ℂ] V D) z₀ :=
    (analyticOnNhd_chart u c z₀ hz).hasStrictFDerivAt
  have hd := hs.to_localInverse.hasFDerivAt.differentiableAt
  have hr := hs.eventually_right_inverse
  have hl := hs.localInverse_apply_image
  have ht := hs.localInverse_tendsto
  rw [hv₀] at hd hr hl ht
  have hFz : DifferentiableAt ℂ (F ∘ pt u) (hs.localInverse _ _ _ v) := by
    rw [hl]
    exact hF.differentiableAt ((hS.preimage (continuous_pt u)).mem_nhds (show pt u z₀ ∈ S from hz₀ ▸ hv.2))
  refine ((hFz.comp v hd).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hr, ht ((isOpen_pre_source u c).mem_nhds hz)] with w hw hw'
  exact congrArg F ((congrArg c.e.symm hw.symm).trans (c.e.left_inv hw'))

theorem exists_isFn (hA : IsAbelianScheme A) (hp : IsProjOver A.hom) (hM : M.IsLB) {θ : (Fin g → ℂ) → ℂ}
    (hθ : Differentiable ℂ θ)
    (hper : ∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) :
    ∃ s : M.Sec, u.IsFn s θ := by
  classical
  obtain ⟨D, hD⟩ := AbelianDim.exists_relDim ℂ A hA
  let r := Function.surjInv (pt_surjective u)
  have hr : ∀ y, pt u (r y) = y := Function.surjInv_eq (pt_surjective u)
  let s : M.ι → CxPts A.hom (RingHom.id ℂ) → ℂ := fun i y =>
    if y ∈ ptsIn _ _ (M.U i) then θ (r y) * u.fr i (r y) else 0
  have hs : ∀ i z, pt u z ∈ ptsIn _ _ (M.U i) → s i (pt u z) = θ z * u.fr i z := fun i z hz => by
    have := hper _ (sub_mem_of_pt_eq u (hr (pt u z))) i z hz
    rw [add_sub_cancel] at this
    exact (if_pos hz).trans this
  have hmem : s ∈ (AnRead.all A.hom (RingHom.id ℂ) D).holSec M := by
    refine ⟨⟨fun i j y hi hj => ?_, fun i y h => if_neg h⟩, fun i => holoOn_of_comp u _ (isOpen_ptsIn _) ?_⟩
    · obtain ⟨z, rfl⟩ := pt_surjective u y
      have hij : pt u z ∈ ptsIn _ _ (M.U i ⊓ M.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      have e : u.fr i z = gv _ _ M i j (pt u z) * u.fr j z := u.fr_compat i j z hij
      rw [hs i z hi, hs j z hj, e, mul_left_comm]
    · exact (hθ.differentiableOn.mul (u.fr_hol i)).congr fun z hz => hs i z hz
  obtain ⟨σ, hσ⟩ := (GlobalTheory.Published.serreHolomorphicSections_holds A.left A.hom D hD hp _ M hM).2 ⟨s, hmem⟩
  exact ⟨σ, fun i z hz => (congrFun₂ (congrArg Subtype.val hσ) i (pt u z)).trans (hs i z hz)⟩

theorem isUnit_of_ev_ne_zero {Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] {U : Y.Opens} (f : Γ(Y, U))
    (h : ∀ y ∈ ptsIn p (RingHom.id ℂ) U, ev p _ U f y ≠ 0) : IsUnit f := by
  have := LocallyOfFiniteType.jacobsonSpace p
  have hU : U ≤ Y.basicOpen f := by
    by_contra hn
    obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
    obtain ⟨y, hy, hy'⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (Y.basicOpen f : Set Y)ᶜ) ⟨x, hx, hx'⟩
      (U.isOpen.isLocallyClosed.inter (Y.basicOpen f).isOpen.isClosed_compl.isLocallyClosed)
    let q : CxPts p (RingHom.id ℂ) :=
      ⟨pointOfClosedPoint p y hy', (pointOfClosedPoint_comp p y hy').trans (Spec.map_id _).symm⟩
    have hq : q.1 (IsLocalRing.closedPoint ℂ) = y := pointOfClosedPoint_apply p y hy' _
    have hqU : q ∈ ptsIn p _ U := mem_ptsIn.2 (hq ▸ hy.1)
    exact hy.2 (hq ▸ mem_ptsIn.1 ((mem_ptsIn_basicOpen hqU f).2 (h q hqU)))
  exact Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => (Y.mem_basicOpen f x hx).1 (hU hx)

theorem hasGen_of_periodic : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M : LB A.left), M.IsLB → ∀ (g : ℕ) (u : HolUnif A M g) (θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ →
    (∀ z, θ z ≠ 0) →
    (∀ l ∈ u.Λ, ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U i → θ (z + l) * u.fr i (z + l) = θ z * u.fr i z) →
    HasGen M := by
  intro A _ hA hp M hM g u θ hθ h0 hper
  obtain ⟨s, hs⟩ := exists_isFn u hA hp hM hθ hper
  have := hA.proper
  have hu : ∀ i, IsUnit (s.f i) := fun i => isUnit_of_ev_ne_zero A.hom _ fun y hy => by
    obtain ⟨z, rfl⟩ := pt_surjective u y
    exact (hs i z hy).trans_ne (mul_ne_zero (h0 z) (u.fr_ne i z hy))
  exact ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j)⟩

end GlobalTheory.HolUnifSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnframePt

open GlobalTheory.RealGeo GlobalTheory.Unframe Formalism.IndefR.FWT

abbrev fullHeckeRealDatMovedReadings {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) : RealDat3 D A3 Ks :=
  { Rl with toRealDat := moveR Rl.toRealDat w }

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def geoHalf (p : PtAt ex Csz) : GeoHalf p.T p.R.toRealDat (fun _ => 1) :=
  ⟨p.κ, p.v₀, p.fw, p.bar, p.O, p.pins, p.rhoGeo, p.equivAll, p.cTie, fun i hu => by
    have e : phEff p.R = fun _ => (1 : ℂ) := funext p.phEff_one
    rw [← e]
    exact p.phase i hu⟩

end Pt

end GlobalTheory.UnframePt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolRoot

def Root {S T : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (G2 A).left) (t : T ⟶ S) : Prop :=
  ∃ (B : Over T) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left),
    IsGrpPullback B A t β ∧ IsSquare β β₂ ∧ ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂)

theorem Root.comp {S T T' : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {P : LB (G2 A).left}
    {t : T ⟶ S} (h : Root A P t) (σ : T' ⟶ T) : Root A P (σ ≫ t) := by
  obtain ⟨A', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := h
  obtain ⟨B', _, φ, hφ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' σ
  haveI : IsCommMonObj B' := by
    rw [isCommMonObj_iff_isMulCommutative]
    intro T
    refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
      ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
  let V := lift (pushPt hφ.1.w (fst B' B')) (pushPt hφ.1.w (snd B' B'))
  have hV : IsSquare φ V.left := GlobalTheory.LamPull.exists_isSquare hφ.1.w
  refine ⟨B', inferInstance, inferInstance, φ ≫ β, V.left ≫ β₂, hφ.comp hβ,
    GlobalTheory.ZM.SiegPull.isSquare_comp hV hsq, L.pull φ, pull_isLB hL φ, ?_⟩
  refine LBIso.chartPull
    (chartPullLinComb L φ _ _ _ V.left fun I => psum_push hφ _ _ V (fun i => ?_) I.down)
    (chartPullSame P (fun _ : PUnit => V.left ≫ β₂) (fun _ => β₂) (fun _ => 1) V.left fun _ => rfl) H
  fin_cases i <;> simp [V, x2]

def tri {X Y T : Scheme.{0}} (f : X ⟶ Y) (a b c : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) :
    T ⟶ GlobalTheory.LBDescent.Triple f :=
  pullback.lift (pullback.lift a b h₁) (pullback.lift b c h₂) (by rw [pullback.lift_snd, pullback.lift_fst])

def TriCocycle {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (a b c d : T ⟶ X) (h₁ : a ≫ f = b ≫ f) (h₂ : b ≫ f = c ≫ f) (h₃ : c ≫ f = d ≫ f),
    GlobalTheory.CharKer.pullTop (tri f a b c h₁ h₂) D * GlobalTheory.CharKer.pullTop (tri f a c d (h₁.trans h₂) h₃) D =
      GlobalTheory.CharKer.pullTop (tri f b c d h₂ h₃) D * GlobalTheory.CharKer.pullTop (tri f a b d h₁ (h₂.trans h₃)) D

def KillsSq {X Y : Scheme.{0}} (f : X ⟶ Y) (D : Γ(GlobalTheory.LBDescent.Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ) : Prop :=
  D ^ 2 * GlobalTheory.CharKer.pullTop (pullback.fst (pullback.snd f f) (pullback.fst f f)) u *
      GlobalTheory.CharKer.pullTop (pullback.snd (pullback.snd f f) (pullback.fst f f)) u =
    GlobalTheory.CharKer.pullTop (GlobalTheory.LBDescent.pr13 f) u

end GlobalTheory.PolRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.AbelianDeRhamFreeOfHodge

def extSqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem extSqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    extSqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem free_of (hC : GlobalTheory.Published.CrystallineSmoothLift) (hA : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (s : A.left ⟶ Sp R) (hs : s = A.hom) :
    Module.Finite R (FirstDeRham s) ∧ Module.Projective R (FirstDeRham s) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham s) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham s) ≃ₗ[R] SecondDeRham s,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b := by
  subst hs
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  obtain ⟨⟨hfin, hproj, hrank⟩, ⟨eH, heH⟩, -⟩ := hA R A g hab hg
  obtain ⟨hbij, e2, he2⟩ := GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left A.hom inferInstance inferInstance inferInstance
  let E1 : FirstDeRham A.hom ≃ₗ[R] HH1 A.hom := LinearEquiv.ofBijective (cmp1 A.hom) hbij
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, ?_, ?_⟩
  · intro p
    rw [Module.rankAtStalk_eq_of_equiv E1]
    exact hrank p
  · refine ⟨(extSqEquiv E1).trans (eH.trans e2.symm), fun a b => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extSqEquiv_ιMulti, heH, LinearEquiv.symm_apply_eq]
    exact (he2 a b).symm

end GlobalTheory.Proof.AbelianDeRhamFreeOfHodge


open GlobalTheory.Proof.AbelianDeRhamFreeOfHodge in
theorem GlobalTheory.Proof.abelianDeRhamFree_of_hodge :
    GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  intro hC hA R _ A _ g hab hg
  exact free_of hC hA R A g hab hg _ (Category.comp_id _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparisonStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  first | exact @GlobalTheory.Proof.abelianDeRhamFree_of_hodge | exact GlobalTheory.Proof.abelianDeRhamFree_of_hodge | (intros; apply GlobalTheory.Proof.abelianDeRhamFree_of_hodge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UT

set_option maxHeartbeats 1000000

namespace GlobalTheory.UT


open GlobalTheory.EndData in
theorem exists_degenerationEndomorphism_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro R _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hL := GlobalTheory.firstFiveLaws
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := T.uniformisation_endomorphism_character_map_constant hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => T.exists_generator_of_compatible_thickening_generators R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)


open GlobalTheory.EndRosati GlobalTheory.CechPic in
theorem rosatiAdjoint_and_linear_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧ (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB := by
  intro R _ _ I hR D A G _ _ hG U E E' H
  have hLL := GlobalTheory.firstFiveLaws
  have hGF := hLL.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := E.homG
  have := E'.homG
  have := E.homB
  have := E'.homB
  have := hG.geomConnected
  obtain ⟨u, hu, h₀⟩ := (NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB E.aG E'.aG H).1
  have hP : AbLaw.IsProjBy D.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)
  have hB : RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB :=
    loc_gen_of_thickenings hGF I _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D.toPre.P.isAb D.toPre.P.isAb)
      (AbLaw.isProjBy_tensor R _ _ hP hP) D.toPre.P.isLB _ _ fun e => by
      have := EndTorus.connectedSpace_thickening I e
      have : GeometricallyConnected (thickObj R I e G).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
      have : ConnectedSpace (thickObj R I e G).left :=
        GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
      exact exists_gen_thick U.toUnifPre e (E.q_lin e) (E'.q_lin e)
        (FamGerm.surjective_appTop_sq_cube U.toUnifPre).2 u hu h₀
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hB
  refine ⟨rosatiAdj_generic U.toUnifPre E.ext E'.ext u hu, hB, fun χ => ?_, fun χ => ?_⟩
  · have h₁ := cls_of_gen D.toPre E.aB χ _ (E.u χ) (E.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (𝟙 _) (toUnit _ ≫ D.toPre.c χ)
    rw [Category.id_comp, Category.assoc] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ + h₂
  · have h₁ := cls_of_gen D.toPre E'.aB χ _ (E'.u χ) (E'.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (toUnit _ ≫ D.toPre.c χ) (𝟙 _)
    rw [Category.id_comp, Category.assoc, mul_comm _ (𝟙 D.toPre.P.A), mul_comm _ E'.aB] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ - h₂

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def GeomIso {K₀ K' Ω : Type} [CommRing K₀] [CommRing K'] [CommRing Ω] (A₀ : PolAV (Sp K₀)) (A' : PolAV (Sp K'))
    (e₀ : K₀ →+* Ω) (e' : K' →+* Ω) : Prop :=
  ∃ (B : PolAV (Sp Ω)) (b₀ : B.A.left ⟶ A₀.A.left) (b' : B.A.left ⟶ A'.A.left),
    IsGrpPullback B.A A₀.A (spMap e₀) b₀ ∧ LBIso B.L (A₀.L.pull b₀) ∧
    IsGrpPullback B.A A'.A (spMap e') b' ∧ LBIso B.L (A'.L.pull b')

def UniTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (_ : Unif (maximalIdeal W) D' A' G') (_ : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left),
    GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsSemiAbelian G' ∧ IsFib φ A A' a

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TopForm

theorem bijective_formMap_of_bijective {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} (D : ℕ) (ρ : A →+* B) (h : ρ.comp α = β)
    (hρ : Function.Bijective ρ) : Function.Bijective (TopForm.formMap D ρ h) := by
  let e : A ≃+* B := RingEquiv.ofBijective ρ hρ
  let σ : B →+* A := e.symm.toRingHom
  have e1 : σ.comp ρ = RingHom.id A := RingHom.ext fun a => e.symm_apply_apply a
  have e2 : ρ.comp σ = RingHom.id B := RingHom.ext fun b => e.apply_symm_apply b
  have h' : σ.comp β = α := by
    rw [← h, ← RingHom.comp_assoc, e1, RingHom.id_comp]
  refine Function.bijective_iff_has_inverse.mpr ⟨TopForm.formMap D σ h', fun x => ?_, fun y => ?_⟩
  · rw [formMap_formMap ρ σ (RingHom.id A) e1 h h' (RingHom.id_comp α)]
    exact formMap_of_eq_id _ rfl _ x
  · rw [formMap_formMap σ ρ (RingHom.id B) e2 h' h (RingHom.id_comp β)]
    exact formMap_of_eq_id _ rfl _ y

end GlobalTheory.TopForm

namespace GlobalTheory.EtaleKlt

theorem ratPull_bijective_of_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ n : ℕ,
      Function.Bijective (EtaleKlt.ratPull p s n) := by
  intro k _ X Y _ _ p s _ hs n
  exact TopForm.bijective_formMap_of_bijective n _ (functionFieldMap_comp_constFn p s) hs

end GlobalTheory.EtaleKlt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalTopFormPullback_bijective_birational : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ n : ℕ, Function.Bijective (EtaleKlt.ratPull p s n) := by
  first | exact @GlobalTheory.EtaleKlt.ratPull_bijective_of_birational | exact GlobalTheory.EtaleKlt.ratPull_bijective_of_birational | (intros; apply GlobalTheory.EtaleKlt.ratPull_bijective_of_birational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

def secNz {X : Scheme.{0}} {L : LB X} (s : L.Sec) : X.Opens := ⨆ i, X.basicOpen (s.f i)

def farSet {Z Y : Scheme.{0}} (β : Z ⟶ Y) {L : LB Z} (s : L.Sec) : Set Y := {v | ∀ g, β g = v → g ∈ secNz s}

def cubeTen {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x a b c : T ⟶ G) : List (T ⟶ G) :=
  [x * a, x * a⁻¹, a, a⁻¹, x * b, x * c, x * (b * c)⁻¹, b, c, (b * c)⁻¹]

theorem isOpen_farSet {Z Y : Scheme.{0}} (β : Z ⟶ Y) (hβ : IsClosedMap β) {L : LB Z} (s : L.Sec) :
    IsOpen (farSet β s) := by
  have : farSet β s = (β '' (secNz s : Set Z)ᶜ)ᶜ := by
    ext v
    simp only [farSet, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h g hg hgv; exact hg (h g hgv)
    · intro h g hgv; by_contra hg; exact h g hg hgv
  rw [this, isOpen_compl_iff]
  exact hβ _ (secNz s).isOpen.isClosed_compl

end GlobalTheory.Mum
end
end
