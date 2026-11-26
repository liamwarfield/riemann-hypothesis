module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
public import Development.AutomorphicArithmetic.LocalEmbeddings.ArchFlip
public import Development.AutomorphicArithmetic.DivisorFrames.ConjSizeHeckeCharLocalOfMemRangeEmbedding
public import Development.AutomorphicArithmetic.DivisorFrames.LocalGridTensorSizeLeOneOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataBoundOfHalfFlip

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepCusp

section Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory _root_.Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn exOf secZ)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.CompHt (genVal genPoint)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_of_ptY_eq {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (h : GenFrEx Xo c) (Z : Comp Xo c)
    {K : Type} [Field K] [Algebra c.F K] (φ φ' : Om Z →ₐ[c.F] K)
    (e : spMap φ.toRingHom ≫ X.ptY (genFr h Z) = spMap φ'.toRingHom ≫ X.ptY (genFr h Z)) : φ = φ' := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagMod.exists_frMap φ (genFr h Z)
  obtain ⟨y', hy'⟩ := GlobalTheory.FlagMod.exists_frMap φ' (genFr h Z)
  rw [X.ptY_frMap hy, X.ptY_frMap hy'] at e
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY y)
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) (X.lies_ptY y).1 k hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor (X.lies_ptY y)
  obtain ⟨t', ht'⟩ := hQ.exists_frBor (e ▸ X.lies_ptY y')
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  exact eq_of_heq (GlobalTheory.Reg.GenericFlagInj.eq_of_frBor h Z Z φ φ' y y' _ hy hy' (g1 _ _ _ _ _ (g2 _ _ _ ht) ht')).2

theorem exists_val_cuspSec {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (h : GenFrEx Xo c) (w : Sp (Om Z) ⟶ Y₀ X Z)
    (hw : w ≫ inc₀ X Z = X.ptY (genFr h Z)) (hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z) (i : (L₀ X Z la).ι)
    (hi : ⊤ ≤ w ⁻¹ᵁ (L₀ X Z la).U i) :
    ∃ T : Om Z, T ≠ 0 ∧ ∀ g : Cusp Z U la, H0.val w i hU hi (cuspSec X Z U la g) = T * genVal Z g.1 := by
  have e₁ : w ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by rw [X.pt_inc]; exact hw
  have hO₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have hk₂ : ⊤ ≤ (w ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) :=
    (le_iff_ptOf_mem _ _).2 (mem_pull.1 ((le_iff_ptOf_mem _ _).1 hi))
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
  have hQ₂ : X.F.ChartFr (i PUnit.unit) (w ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
  have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
  have v₅ : H0.val w i hU hi (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
      (w ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl w i hU hi hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  rw [v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem val_eq_stalk {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    H0.val x i hO hi f = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom (germ i (ptOf x) hy hj f) := by
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm

theorem gapGe_std (Dw : Datum H) : GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_std (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

private def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')

private theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }

private theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }

private theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }

private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) :=
  map_nsmul (AddMonoidHom.mk' (fun a => cls (B a) (C.isLB a)) (cls_common_add C)) n a

end Geometry

theorem exists_fg_complexPoint (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [Countable K]
    (hfg : (⊤ : IntermediateField K Ω).FG) (L : IntermediateField K Ω) (hL : L = ⊤) :
    ∃ (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ L) ∧
      IntermediateField.adjoin K (A : Set Ω) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ,
        (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧
          ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) := by
  have : Countable Ω := TwoPoint.countable_of_fg _ _ hfg
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨i⟩ := TwoPoint.nonempty_ringHom_complex Ω
  obtain ⟨s, hs⟩ := hfg
  let A : Subalgebra K Ω := Algebra.adjoin K (s : Set Ω)
  exact ⟨i.comp (algebraMap _ _), A, A, ⟨s, rfl⟩, ⟨s, rfl⟩, le_rfl, fun b _ => hL ▸ IntermediateField.mem_top,
    eq_top_iff.2 (hs ▸ IntermediateField.adjoin.mono _ _ _ Algebra.subset_adjoin), fun b _ hb =>
    ⟨i.comp A.val.toRingHom, fun _ => rfl, fun _ => (map_ne_zero i).2 hb, fun y _ h => RingHom.ext fun a => h a a.2⟩⟩

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta
open scoped ENNReal NNReal

theorem gapGe_sub_kap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hu : ∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      (((dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ u τ a - u τ b) :
    GlobalTheory.HSApp.GapGe (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (u - FlagTan.kap Dw) := by
  intro τ k hk
  have h₁ := hu τ ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl
  have h₂ : GlobalTheory.CompHS.gap (FlagTan.kap Dw τ) k ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 := by
    unfold FlagTan.kap GlobalTheory.CompHS.gap
    simp only [dif_pos hk]
    split_ifs <;> push_cast <;> omega
  have h₃ := GlobalTheory.CompHS.gap_eq (u τ) (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl
  have h₄ : (FlagTan.dimFlag Dw + 2).choose 2 ≤ (FlagTan.dimFlag Dw + 3) ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) 2)
  have h₅ : (((FlagTan.dimFlag Dw + 2).choose 2 : ℕ) : ℤ) ≤ ((FlagTan.dimFlag Dw + 3) ^ 2 : ℕ) := by
    exact_mod_cast h₄
  have hgap_sub : GlobalTheory.CompHS.gap (u τ - FlagTan.kap Dw τ) k =
      GlobalTheory.CompHS.gap (u τ) k - GlobalTheory.CompHS.gap (FlagTan.kap Dw τ) k := by
    unfold GlobalTheory.CompHS.gap
    split_ifs <;> simp [Pi.sub_apply] <;> ring
  rw [GlobalTheory.CompHS.dimFlag_eq] at h₁
  rw [Pi.sub_apply, hgap_sub]
  dsimp only at h₃
  push_cast at h₁ h₂ h₅ ⊢
  linarith


end GlobalTheory.SepCusp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.Adjust

theorem valR_const {K R : Type} [CommRing K] [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp K) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, ← Category.comp_id (spMap f),
    HolHom.valR_spMap f (𝟙 _) ⊤ le_rfl, HolHom.valR_eq _ _ le_rfl]
  congr 1
  exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom a)
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id

theorem eq_zero_of_valR_points {X : Scheme.{0}} (U : X.Opens) (s : Γ(X, U))
    (h : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ X), ⊤ ≤ g ⁻¹ᵁ U → valR g U s = 0) : s = 0 := by
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W : X.affineOpens // W.1 ≤ U}) (fun W => W.1.1) (fun W => W.2) ?_ s 0 ?_
  · intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · rintro ⟨⟨W, hW⟩, hWU⟩
    have hW' : IsAffineOpen W := hW
    have hle : ⊤ ≤ hW'.fromSpec ⁻¹ᵁ W := hW'.fromSpec_preimage_self.ge
    have e := h Γ(X, W) hW'.fromSpec (hle.trans (hW'.fromSpec.preimage_mono hWU))
    rw [← HolHom.valR_res (A := Γ(X, W)) hW'.fromSpec hWU s hle, HolHom.valR_eq _ _ hle, HolHom.evalHom] at e
    rw [GlobalTheory.KS.rsT_zero, GlobalTheory.KS.rsT_of_le hWU]
    have e2 : hW'.fromSpec.appLE W ⊤ hle = (Scheme.ΓSpecIso Γ(X, W)).inv := by
      rw [Scheme.Hom.appLE, hW'.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg _ ((Spec Γ(X, W)).presheaf.map_id _)).trans (Category.comp_id _)
    erw [e2] at e
    erw [Iso.inv_hom_id] at e
    exact e

theorem inv_constFn {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    (dd : Fld G.left) (hinv : IsInv G v dd) (V : G.left.Opens) (r : R) : dd V (constFn G.hom V r) = 0 := by
  refine eq_zero_of_valR_points _ _ fun S _ a hV => ?_
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (a ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : a ≫ G.hom = spMap φ := hφ'.symm
  let x : Over.mk (spMap φ) ⟶ G := Over.homMk a hφ
  let φε : R →+* DualNumber S := (algebraMap S (DualNumber S)).comp φ
  let π : Over.mk (spMap φε) ⟶ Over.mk (spMap φ) :=
    Over.homMk (spMap (algebraMap S (DualNumber S))) (by
      show spMap (algebraMap S (DualNumber S)) ≫ spMap φ = spMap φε
      simp only [spMap, φε, ← Spec.map_comp]; rfl)
  let ie : Over.mk (spMap φ) ⟶ Over.mk (spMap φε) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap φε = spMap φ
      simp only [spMap, φε, ← Spec.map_comp]
      congr 1)
  obtain ⟨v'', hv₁, hv₂⟩ := InvWt.exists_tan_over G v φ
  have hιπ : ie ≫ π = 𝟙 _ := by
    ext1
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _
    simp only [spMap, ← Spec.map_comp]
    rw [← Spec.map_id]; congr 1
  have hiev : ie ≫ v'' = 1 := by
    ext1
    exact hv₂
  have hW : ie ≫ (π ≫ x * v'') = x := by
    rw [MonObj.comp_mul, ← Category.assoc, hιπ, Category.id_comp, hiev, _root_.mul_one]
  have hWa : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x * v'').left = a :=
    congrArg (·.left) hW
  have htr : IsTr G φ a v (π ≫ x * v'').left := by
    let e : tEpsG (a ≫ G.hom) ⟶ Over.mk (spMap φε) := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap φε = spMap (algebraMap S (DualNumber S)) ≫ a ≫ G.hom
      rw [hφ]
      simp only [Category.id_comp, spMap, φε]
      rw [← Spec.map_comp]; rfl)
    refine ⟨e ≫ π ≫ x, e ≫ v'', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ spMap (algebraMap S (DualNumber S)) ≫ a = _
      rw [Category.id_comp]
    · show 𝟙 _ ≫ v''.left = _
      rw [Category.id_comp, hv₁]
    · rw [← MonObj.comp_mul]
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  rw [← hinv.2 S φ a (π ≫ x * v'').left V _ hφ hV htr,
    valR_const G.hom φε _ (Over.w (π ≫ x * v'')) V (InvWt.top_le_preimage_of_fst _ a V hWa hV)]
  simp [φε, TrivSqZeroExt.algebraMap_eq_inl]

theorem isField_add_comb {Z : Scheme.{0}} {n : ℕ} {U : Z.Opens} (d₀ : Fld Z) (dd : Fin n → Fld Z)
    (y : Fin n → Γ(Z, U)) (h₀ : IsField U d₀) (h : ∀ a, IsField ⊤ (dd a)) :
    IsField U (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hWW hW f => ?_⟩
  · simp only [h₀.1 W hW, fun a => (h a).1 W le_top, mul_add, Finset.sum_add_distrib]
    ring
  · simp only [h₀.2.1 W hW, fun a => (h a).2.1 W le_top, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have e : ∀ (g : Γ(Z, W)) (u : Fin n → Γ(Z, W)), ∑ a, rsT (y a) W * (g * u a) = ∑ a, g * (rsT (y a) W * u a) :=
      fun g u => Finset.sum_congr rfl fun a _ => by ring
    rw [e, e]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [h₀.2.2 W W' hWW hW, fun a => (h a).2.2 W W' hWW le_top, map_add (f := _), map_sum, map_mul]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← GlobalTheory.KS.rsT_of_le hWW (rsT (y a) W), GlobalTheory.KS.rsT_rsT hW hWW]

theorem isWt_rsT {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {α : Q.X} {V V' : Y.H.left.Opens} (h : V' ≤ V) {f : Γ(Y.H.left, V)}
    (hf : IsWt Y α V f) : IsWt Y α V' (rsT f V') := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [GlobalTheory.KS.rsT_of_le h]
  refine (HolHom.valR_res a' h f hV').trans (Eq.trans ?_ (congrArg _ (HolHom.valR_res a h f hV)).symm)
  exact hf S φ x x' c a a' ha ha' (hV.trans (a.preimage_mono h)) (hV'.trans (a'.preimage_mono h)) hq hc

theorem isLift_add_invComb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (V : Dd.toPre.P.A.left.Opens) (d₀ : Fld Y.H.left) (y : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d₀ → (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d₀ _ f)) → (∀ a, IsWt Y 0 _ (y a)) → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) ∧ (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') ((fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) _ f)) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hinv D V d₀ y hd hw hy
  refine ⟨⟨isField_add_comb d₀ dd y hd.1 fun a => (hinv a).1, fun W hW r => ?_⟩, fun α V' hV' f hf => ?_⟩
  · simp only [hd.2 W hW r, fun a => inv_constFn Y.H (v a) (dd a) (hinv a) W r, mul_zero, Finset.sum_const_zero,
      add_zero]
  · exact WtAlg.isWt_add (hw α V' hV' f hf) (WtAlg.isWt_sum _ _ fun a _ =>
      WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (isWt_rsT Y hV' (hy a)) (IsInv.isWt Y (v a) (dd a) (hinv a) α _ f hf))

end GlobalTheory.Heat.Adjust
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombinationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusInvariantLift_add_invariantCombination : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (V : Dd.toPre.P.A.left.Opens) (d₀ : Fld Y.H.left) (y : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d₀ → (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d₀ _ f)) → (∀ a, IsWt Y 0 _ (y a)) → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) ∧ (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') ((fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) _ f)) := by
  first | exact @GlobalTheory.Heat.Adjust.isLift_add_invComb | exact GlobalTheory.Heat.Adjust.isLift_add_invComb | (intros; apply GlobalTheory.Heat.Adjust.isLift_add_invComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam

def sig : Fin 8 → Fin 4 ⊕ Fin 4 :=
  ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1, .inr 2, .inr 3]

def oMat (d : ℕ) (k : Fin 8) : ord d :=
  ⟨Matrix.single (Sum.inl 0) (sig k) 1, fun i j => by simp [Matrix.single]⟩

def jlMap (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) where
  toFun a := fun
    | .inl i => if hi : (i : ℕ) < h then a (.inl ⟨i, hi⟩) else 0
    | .inr i => if hi : (i : ℕ) < h then a (.inr ⟨i, hi⟩) else 0
  map_zero' := by
    funext i; rcases i with i | i <;> simp
  map_add' a b := by
    funext i; rcases i with i | i <;> simp only [Pi.add_apply] <;> split_ifs <;> simp

def formZ (d h : ℕ) (X Y : Fin 8 → Fin h ⊕ Fin h → ℤ) : ℤ :=
  ∑ k, ∑ l, form d (sig k) (sig l) * omegaStd (X k) (Y l)

def KappaOK (h M d : ℕ) (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) : Prop :=
  (∀ a b, formZ d h (fun k => κ k a) (fun k => κ k b) ≡ omegaStd a b [ZMOD (M : ℤ)]) ∧
    (∀ a, κ 0 (jlMap h a) = a) ∧ ∀ k, k ≠ 0 → ∀ a, κ k (jlMap h a) = 0

section Obj

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

abbrev Zob : Over S := Out.powObj A 4 ⊗ Out.powObj B 4

def pa (i : Fin 4) : Zob A B ⟶ A := fst _ _ ≫ Out.powPr A i

def pb (j : Fin 4) : Zob A B ⟶ B := snd _ _ ≫ Out.powPr B j

def mkZ {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) : T ⟶ Zob A B :=
  lift ((Out.powIsLimit A 4).lift (Fan.mk T u)) ((Out.powIsLimit B 4).lift (Fan.mk T v))

def actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) (N : ord d) : Zob A B ⟶ Zob A B :=
  mkZ A B
    (fun i => ∏ j, (pa A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i)) *
      (pb A B j ≫ mu) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))))
    (fun i => ∏ j, ((pa A B j ≫ la) ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i)) *
      pb A B j ^ ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))))

def incZ : A ⟶ Zob A B := mkZ A B (fun i => if i = 0 then 𝟙 A else 1) (fun _ => 1)

def prZ : Zob A B ⟶ A := pa A B 0

def zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    CechPic.Pic (Zob A B ⊗ Zob A B).left :=
  (∑ i, CechPic.pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i) (snd (Zob A B) (Zob A B) ≫ pa A B i)).left
      (cls P hP)) +
    (∑ i, ∑ j, quat d j i • CechPic.pull (lift (fst (Zob A B) (Zob A B) ≫ pa A B i)
      (snd (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    (∑ i, ∑ j, quat d j i • CechPic.pull (lift (snd (Zob A B) (Zob A B) ≫ pa A B i)
      (fst (Zob A B) (Zob A B) ≫ pb A B j)).left (cls Q hQ)) +
    ∑ j, CechPic.pull (lift (snd (Zob A B) (Zob A B) ≫ pb A B j ≫ mu) (fst (Zob A B) (Zob A B) ≫ pb A B j)).left
      (cls Q hQ)

def zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    LB (Zob A B ⊗ Zob A B).left :=
  (cls_surj (zCls A B hP hQ d mu)).choose

theorem zarhinBundle_isLineBundle {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    (zP A B hP hQ d mu).IsLB :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose

theorem cls_zP {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A) :
    cls (zP A B hP hQ d mu) (zarhinBundle_isLineBundle A B hP hQ d mu) = zCls A B hP hQ d mu :=
  (cls_surj (zCls A B hP hQ d mu)).choose_spec.choose_spec

end Obj

def levZ {S : Scheme.{0}} {A Z : Over S} [GrpObj Z] [IsCommMonObj Z] {O : Type} {h h' n : ℕ}
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (inc : A ⟶ Z) (act : O → (Z ⟶ Z)) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (a : Fin h' ⊕ Fin h' → ℤ) : 𝟙_ (Over S) ⟶ Z :=
  (List.ofFn fun k => lev (κ k a) ≫ inc ≫ act (o k)).prod

def ZData {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t) (d : ℕ)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) : Prop :=
  IsAbelianScheme B ∧ IsDual c.A B Q ∧ IsDual B c.A (swap Q) ∧ IsMonHom la ∧ IsMonHom mu ∧
    la ≫ mu = 𝟙 c.A ^ d ∧ mu ≫ la = 𝟙 B ^ d ∧ LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
namespace GlobalTheory

theorem abelianDualCrystal : GlobalTheory.Published.AbelianDualCrystal :=
  GlobalTheory.abelianDualCrystal_of_dualAbelianScheme GlobalTheory.dualAbelianScheme

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  obtain ⟨t, ht⟩ := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 (G3 A) := by
    ext <;> simp [x3]
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun V _ k => by
    have h := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) k
    rw [e] at h
    refine Eq.trans ?_ (h.symm.trans (Finset.prod_congr rfl fun I _ =>
      congrArg (fun q => k q ^ thε I) (Category.id_comp _)))
    simp [Fin.prod_univ_eight]) t ht
  exact ⟨t', ht'⟩

theorem isGrpPullback_prod {S S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B]
    [GrpObj A'] [GrpObj B'] {b : S' ⟶ S} {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left}
    (m : IsGrpPullback A' A b f) (n : IsGrpPullback B' B b g) {h : (A' ⊗ B').left ⟶ (A ⊗ B).left}
    (h₁ : h ≫ (fst A B).left = (fst A' B').left ≫ f) (h₂ : h ≫ (snd A B).left = (snd A' B').left ≫ g) :
    IsGrpPullback (A' ⊗ B') (A ⊗ B) b h := by
  refine ⟨isPullback_prod m.1 n.1 h₁ h₂, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (grpMor_prod (κ := dp0 ℤ) (κ' := dp0 ℤ) (σ := RingHom.id ℤ) (t := specZIsTerminal.from _) (t' := specZIsTerminal.from _)
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, m.1.w, m.2⟩
    ⟨Cris.isDPMorphism_of_eq_bot _ rfl _ _, specZIsTerminal.hom_ext _ _, n.1.w, n.2⟩ h₁ h₂).mul T x y x₀ y₀ hx hy

theorem lift_left_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {h : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h₁ : h ≫ (fst G G).left = (fst G' G').left ≫ φ)
    (h₂ : h ≫ (snd G G).left = (snd G' G').left ≫ φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    {x y : T ⟶ G} {x' y' : T' ⟶ G'} (hx : x'.left ≫ φ = τ ≫ x.left) (hy : y'.left ≫ φ = τ ≫ y.left) :
    (lift x' y').left ≫ h = τ ≫ (lift x y).left := by
  have p : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  apply p.hom_ext
  · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc, ← Over.comp_left,
      lift_snd]

theorem one_left_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (τ : T'.left ⟶ T.left)
    (hτ : τ ≫ T.hom = T'.hom ≫ f) : (1 : T' ⟶ G').left ≫ φ = τ ≫ (1 : T ⟶ G).left := by
  let σ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk τ hτ
  exact congrArg (fun q => q.left) ((map_one (pushHom hp T')).trans (MonObj.comp_one σ).symm)

theorem lift_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} {x y : T ⟶ G} {N : ℕ} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : lift x y ^ N = 1 := by
  ext1 <;> simp only [MonObj.pow_comp, MonObj.one_comp, lift_fst, lift_snd, hx, hy]

section Algebra

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (B : Type) [CommRing B]

def twoMap [Algebra R B] : B ⊗[R] B →ₐ[R] (K ⊗[R] B) ⊗[K] (K ⊗[R] B) :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft (S := R)).comp Algebra.TensorProduct.includeRight)
    (((Algebra.TensorProduct.includeRight (R := K)).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    fun _ _ => .all _ _

theorem twoMap_tmul [Algebra R B] (a b : B) :
    twoMap (K := K) B (a ⊗ₜ[R] b) = ((1 : K) ⊗ₜ[R] a) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b) := by
  simp [twoMap]

variable {B} [Bialgebra R B] [Module.Finite R B] [Module.Projective R B]

theorem contract_twoMap (χ : CartierDual R B) (u : B ⊗[R] B) :
    TensorProduct.rid K _ ((CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv.lTensor _ (twoMap (K := K) B u)) =
      (1 : K) ⊗ₜ[R] TensorProduct.rid R _ (χ.ofConv.lTensor _ u) := by
  induction u with
  | add x y hx hy => simp only [map_add (f := _), hx, hy, tmul_add]
  | tmul a b =>
    have := CartierDual.baseChange_tmul_tmul K 1 1 χ b
    rw [twoMap_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, rid_tmul, rid_tmul]
    rw [show (CartierDual.baseChange R K B ((1 : K) ⊗ₜ χ)).ofConv ((1 : K) ⊗ₜ b) = χ.ofConv b • (1 * 1 : K) from this,
      _root_.mul_one, smul_assoc, one_smul, tmul_smul]

end Algebra

section Level

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

end Level

end GlobalTheory.WeilIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEmbeddingCompatibilityRows
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwCx

open GlobalTheory.ExportSeries Formalism.IndefR.Datum GlobalTheory.BigOn.Exp.TupLe GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)

def TwQ : Prop := ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (Q : Finset (Pl D.host.E))
  (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), IntegralHeckeForms.TwOK i k Q ψ → ∀ P ∈ Q, ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

theorem twQ : TwQ := by
  intro D i k Q ψ hok P hP hl
  obtain ⟨-, -, -, -, -, hram, htriv⟩ := hok
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P
  obtain ⟨σ, hσ, hne⟩ := (hram P A hA).2 hP
  exact hne (htriv P hl A hA σ (ReciprocityTheory.Gal.Ine_le_Dec A hσ))

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}

end Point

end GlobalTheory.BigOn.Exp.TwCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistUpperBound
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TupLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem baseOf_of_pin {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = GlobalTheory.ConjTwist.liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← GlobalTheory.ConjTwist.liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

end GlobalTheory.BigOn.Exp.TupLe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPair
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_dualPair : ∀ (K : Type) [Field K] (A : AbVar K),
    ∃ (B : AbVar K) (P : LB (A.X ⊗ B.X).left), IsDualPair A B P ∧ B.dim = A.dim := by
  intro K _ A
  obtain ⟨B, hg, P, hB, hdim, h1, h2⟩ := GlobalTheory.dualAbelianScheme (Sp K) A.X A.ab
  exact ⟨{ X := B, grp := hg, ab := hB, dim := A.dim, smooth := hdim A.dim A.smooth }, P, ⟨h1, h2⟩, rfl⟩

end GlobalTheory.AV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPairStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_exists_dual_pair : ∀ (K : Type) [Field K] (A : AbVar K), ∃ (B : AbVar K) (P : LB (A.X ⊗ B.X).left), IsDualPair A B P ∧ B.dim = A.dim := by
  first | exact @GlobalTheory.AV.exists_dualPair | exact GlobalTheory.AV.exists_dualPair | (intros; apply GlobalTheory.AV.exists_dualPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeWeil

theorem triv_theta (hC : GlobalTheory.Published.CubeTheorem) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) := by
  have := hA.comm
  have h := hC S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [CechPic.cls_linComb hL _ _ _, Fin.sum_univ_eight] at e
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [CechPic.cls_linComb hL _ _ _, ← e, ← Equiv.ulift.symm.sum_comp]
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {{0, 1, 2}, {0, 1}, {0, 2}, {1, 2}, {0}, {1}, {2}, ∅} := by
    decide
  rw [u]
  iterate 7 rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have k0 : psum A (x3 A) {0, 1, 2} = x3 A 0 * x3 A 1 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 1 * (x3 A 2 * 1)) from rfl).trans (by rw [_root_.mul_one, _root_.mul_assoc])
  have k1 : psum A (x3 A) {0, 1} = x3 A 0 * x3 A 1 :=
    (show _ = x3 A 0 * (x3 A 1 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k2 : psum A (x3 A) {0, 2} = x3 A 0 * x3 A 2 :=
    (show _ = x3 A 0 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k3 : psum A (x3 A) {1, 2} = x3 A 1 * x3 A 2 :=
    (show _ = x3 A 1 * (x3 A 2 * 1) from rfl).trans (by rw [_root_.mul_one])
  have k4 : psum A (x3 A) {0} = x3 A 0 := _root_.mul_one (x3 A 0)
  have k5 : psum A (x3 A) {1} = x3 A 1 := _root_.mul_one (x3 A 1)
  have k6 : psum A (x3 A) {2} = x3 A 2 := _root_.mul_one (x3 A 2)
  have k7 : psum A (x3 A) ∅ = 1 := rfl
  simp only [Equiv.ulift_symm_down, k0, k1, k2, k3, k4, k5, k6, k7, ← add_assoc]
  rfl

section Point

variable {R D : Type} [CommRing R] [CommRing D] [Bialgebra R D] [Module.Finite R D] [Module.Projective R D]
  [Coalgebra.IsCocomm R D]

end Point

section Tower

variable {p : ℕ} {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {𝒜 ℬ : PDivGroup p R}

end Tower

section Linear

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {𝒜 : PDivGroup p K}
  {w : 𝒜 ⟶ 𝒜.dual} {E : V ≃ₗ[K] 𝒜.RigExt} {β : V →ₗ[K] V →ₗ[K] K} {ε : ℤˣ}


end Linear

end GlobalTheory.HodgeWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatMod

section Values

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def germConstHom (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_id_scal_eq_germConstHom (q : Z ⟶ Sp R) (z : Z) (a : R) :
    gs (𝟙 Z) z ⊤ (scal q a) = germConstHom q z a := by
  rw [gs_eq (𝟙 Z) z ⊤ trivial]; rfl

theorem gs_constFn_eq_germConstHom (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (constFn p ⊤ a) = germConstHom (r ≫ p) z a := by
  have : constFn p ⊤ a = (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    unfold constFn
    rw [← Scheme.Hom.appLE_eq_app]; rfl
  exact (congrArg (gs r z ⊤) this).trans ((gs_eq r z ⊤ trivial _).trans rfl)

theorem sval_sub_constFn_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R)
    (s s' : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (s' - constFn p ⊤ a • s) r z J = sval s' r z J - germConstHom (r ≫ p) z a * sval s r z J := by
  have hm := hJ.mem φ r
  have h₁ : sval (s' - constFn p ⊤ a • s) r z J + sval (constFn p ⊤ a • s) r z J = sval s' r z J :=
    (gs_add r z _ hm _ _).symm.trans (congrArg (gs r z _) (sub_add_cancel _ _))
  have h₂ : sval (constFn p ⊤ a • s) r z J = germConstHom (r ≫ p) z a * sval s r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans (gs_constFn_eq_germConstHom p r z a)) rfl)
  rw [← h₁, h₂, add_sub_cancel_right]

end Values

theorem shiftEq_of_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  intro R _ _ Q k mu α σ σ' σ₁ σ₁' c e e₁ h₀ h₁ u hu hc z J hJ
  have a₀ := h₀ u hu hc z J hJ
  have a₁ := h₁ u hu hc z J hJ
  rw [sval_sub_constFn_smul _ _ _ _ _ _ hJ, sval_sub_constFn_smul _ _ _ _ _ _ hJ, Over.w, Over.w,
    gs_id_scal_eq_germConstHom] at a₁
  rw [gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero] at a₀
  rw [gs_id_scal_eq_germConstHom, map_sub, map_add (f := _)]
  linear_combination a₁ + germConstHom (DegPre.BF Q (FractionRing R)).hom z e * a₀

end GlobalTheory.HeatMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaShiftFunctionalEq_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  first | exact @GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul | exact GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul | (intros; apply GlobalTheory.HeatMod.shiftEq_of_sub_constFn_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerKilledOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

def KerKilledOn (d : ℕ) {S' : Scheme.{0}} (G : Over S') [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 G).left) (V : S'.Opens) : Prop :=
  ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G),
    (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull
        (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen,
        s.IsGen) → x ^ d = 1

end GlobalTheory.KerKilledLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAdjointEndomorphism
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilAdjoint

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem weilIs_algHom {K : Type} [CommRing K] {B : Over (Sp K)} [GrpObj B] (hB : IsAbelianScheme B) {P : LB B.left}
    (hP : P.IsLB) {k : ℤ} {D E : Type} [CommRing D] [Algebra K D] [CommRing E] [Algebra K E] (α : D →ₐ[K] E)
    {x y : SpAlg K D ⟶ B} {x' y' : SpAlg K E ⟶ B} (hx : spOver α ≫ x = x') (hy : spOver α ≫ y = y') {U : Dˣ}
    (hU : Out.WeilIs B P k (T := SpAlg K D) x y (unitOn U)) :
    Out.WeilIs B P k (T := SpAlg K E) x' y' (unitOn (Units.map (α : D →+* E).toMonoidHom U)) := by
  rw [← map_unitOn, ← hx, ← hy]
  exact CommPairing.weilIs_pull GlobalTheory.globalFns_holds hB hP (T := SpAlg K D) (T' := SpAlg K E) (spOver α) hU

end GlobalTheory.WeilAdjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTensorBound
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem infTensAt_of_places {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) {C : ℝ} (hC : 0 ≤ C)
    (hd : DatAt ch (C / 2)) (hc : CoefAt ch (C / 2)) : InfTensAt ch C := by
  intro σ Φ β hβ x y
  set K : ℝ := C / 2 * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 with hK
  have h1 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => ((ch.S.term A.μ0 Φ β v).coef : ℂ)) (fun v => K * placeSz ch.G v)
    (fun v _ => absLe_rat σ _ (by simpa [hK] using hc Φ β hβ v))
  have h2 := absLe_prod (Finset.univ : Finset (locPl ch.G A.μ0)) (σ := σ)
    (fun v => (ch.S.term A.μ0 Φ β v).datum (ch.S.colAt A.μ0 v x) (ch.S.rowAt A.μ0 v y)) (fun v => K * placeSz ch.G v)
    (fun v _ => by simpa [hK] using hd σ Φ β hβ v x y)
  refine absLe_mono (absLe_mul h1 h2) ?_
  rw [← Finset.mul_sum, ← two_mul, ← mul_assoc]
  have : 2 * K = C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 := by rw [hK]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (sum_placeSz_le ch.G A.μ0) (by positivity)

end GlobalTheory.ArchTens


end
end
