module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamLocallyFreeHodgeDegenerates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem val_pow_mul_eq {R : Type} [CommRing R] (t b : Rˣ) (a : R) (k : ℕ) :
    ((t ^ k : Rˣ) : R) * a = a * ((b⁻¹ ^ k : Rˣ) : R) * (((t * b) ^ k : Rˣ) : R) := by
  have e : ((b⁻¹ ^ k : Rˣ) : R) * ((b ^ k : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  rw [mul_pow, Units.val_mul]
  linear_combination (-(((t ^ k : Rˣ) : R) * a)) * e

theorem exists_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)), g.IsGen → ∀ (k : ℕ) (σ : SecM (𝟙 X) L k), ∃ ω : Ω, IsValue (𝟙 _) L x g k σ ω := by
  intro X L hL Ω _ _ x g hg k σ
  obtain ⟨j₀, hj₀⟩ : ∃ i, ∀ p : Sp Ω, x.base p ∈ L.U i := by
    have hc : x.base (IsLocalRing.closedPoint Ω) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, fun p => ((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open (L.U i).isOpen hi⟩
  have hW : (⊤ : (Sp Ω).Opens) ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  have hG : (⊤ : (Sp Ω).Opens) ≤ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  let ωs : Γ(Sp Ω, ⊤) := ((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)) *
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs, ?_⟩
  intro Z r z J hJ
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs) = ωs := by
    simp
  rw [hinv]
  have hj : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => J ((r ≫ x) ≫ 𝟙 X)) := hJ.mem _ (r ≫ x)
  have hj0 : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) := hW (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hgj : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => J (r ≫ x ≫ 𝟙 X)) := hJ.mem _ r
  have hg0 : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) := hG (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  rw [sval_of σ (r ≫ x) z J _ (fun _ => rfl), sec_trans σ (r ≫ x) z hj hj0, val_of g r z J _ (fun _ => rfl),
    gen_trans hg r z hgj hg0]
  have hT : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (r ≫ x) z (fun _ => J ((r ≫ x) ≫ 𝟙 X)) (fun _ => j₀) =
      trF (L := L) (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => 1) r z (fun _ => J (r ≫ x ≫ 𝟙 X)) (fun _ => j₀) ^ k := by
    simp only [trF]
    rw [Category.assoc]
    simp
  have hp := (gs_pull r x z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀)) hj0 (σ.f fun _ => j₀)).symm
  have hm : r z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have h1 := gs_mul r z ⊤ hm (((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)))
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  have h2 := gm_res r z hG hm (g.s fun _ => j₀)
  rw [gs_res r z hW hm, gs_unit r z ⊤ hm, map_pow, map_inv] at h1
  erw [h2] at h1
  rw [hT, hp, h1]
  exact val_pow_mul_eq _ _ _ _

end GlobalTheory.HeatV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sectionValue_in_frame_localRing_point : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)), g.IsGen → ∀ (k : ℕ) (σ : SecM (𝟙 X) L k), ∃ ω : Ω, IsValue (𝟙 _) L x g k σ ω := by
  first | exact @GlobalTheory.HeatV.exists_isValue | exact GlobalTheory.HeatV.exists_isValue | (intros; apply GlobalTheory.HeatV.exists_isValue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilLagrangianOfLocal
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLagr


open GlobalTheory GlobalTheory.CatCoh GlobalTheory.PDiv GlobalTheory.PtExt in
theorem mem_fil_of_orth_of_ker (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (P : LB (A ⊗ B).left) (hLB : P.IsLB)
    (hz : GlobalTheory.AbLaw.Triv (AbDual.ev P (𝟙 A) (1 : A ⟶ B))) (e : ℕ) (he : IsUnit (e : R))
    (hker : ∀ v : epsR R ⟶ B, GlobalTheory.AbLaw.Triv (AbDual.ev P (fst A (epsR R)) (snd A (epsR R) ≫ v)) → v ^ e = 1)
    (φ : HdR A →ₗ[R] HdR B →ₗ[R] R) (hφ : AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ) (y : HdR B)
    (hy : ∀ x ∈ Fil A, φ x y = 0) : y ∈ Fil B := by
  have hHDR := GlobalTheory.AbCoh.abelianHodgeDeRham
  obtain ⟨-, hHodge, -⟩ := GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hHDR
  obtain ⟨v, hv⟩ := ((hHodge R B g hB hgB).1.1 y).exists
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial R A B P hLB
  have horth := GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hHDR R A B g hA hB hgA hgB P hLB φ hφ
  obtain ⟨k, hk⟩ := GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal hHDR R A B g hA hB hgA hgB P hLB φ hφ horth y v hv 0
    (fun h hh ↦ by rw [hy h hh, map_zero]) 0 (by simp) j hj
  have hk' : IsCob (chartsA P) (tanCoc P j v) k := by
    intro D _ _ D' _ _ ψ x hx
    have e := hk D D' ψ x hx
    simp only [Fn1.add, Fn1.neg, fv, neg_neg] at e
    rw [show ev (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (trivMap ψ x) = 0 from rfl, zero_add] at e
    exact e
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback R (A ⊗ B) A P hLB (AbDual.inl A B) hz
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary R A B P hLB v hv.1 j hj s hs k hk'
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hLB v hv.1 T hT
  have htriv := GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator R (A ⊗ B) (A ⊗ epsR R) P hLB _ t ht
  have hv1 : v ^ e = 1 := hker v htriv
  have hpow : ∀ n : ℕ, IsLieImage (n • y) (v ^ n) := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact isLieImage_one_iff.2 (Submodule.zero_mem _)
    | succ n ih => rw [succ_nsmul, pow_succ]; exact ih.add hv
  have h1 : (e : R) • y ∈ Fil B := by
    rw [Nat.cast_smul_eq_nsmul]
    have := hpow e
    rw [hv1] at this
    exact isLieImage_one_iff.1 this
  obtain ⟨u, hu⟩ := he
  have hyu : y = ((u⁻¹ : Rˣ) : R) • ((e : R) • y) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [hyu]
  exact Submodule.smul_mem _ _ h1

theorem fil_lagrangian : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] (s : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ' : HdR o₀.A →ₗ[C₀] HdR o₀.A →ₗ[C₀] C₀), (∃ g : ℕ, SmoothOfRelativeDimension g o₀.A.hom) →
    GlobalTheory.AbDual.IsCorrForm (dp0 C₀) (𝟙 _) o₀.A o₀.A o₀.P φ' →
    (∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ' x y = 0) ∧ ∀ x, (∀ y ∈ Fil o₀.A, φ' x y = 0) → x ∈ Fil o₀.A := by
  intro p _ D R _ b N C₀ _ s o₀ φ' ⟨g, hg⟩ hφ
  refine ⟨GlobalTheory.PtExt.HodgeOrth.fil_orthogonal GlobalTheory.AbCoh.abelianHodgeDeRham C₀ o₀.A o₀.A g o₀.ab o₀.ab hg hg o₀.P
    o₀.isLB φ' hφ, fun x hx ↦ ?_⟩
  rcases subsingleton_or_nontrivial C₀ with hC | hC
  · haveI : Subsingleton (HdR o₀.A) := Module.subsingleton C₀ _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  obtain ⟨e, hep, hker⟩ := o₀.kerP
  have heu : IsUnit (e : C₀) := by
    have := (b.unit e hep).map (Spec.preimage s).hom
    rwa [map_natCast] at this
  have hs : (AbDual.swap o₀.P).IsLB := pull_isLB o₀.isLB _
  refine mem_fil_of_orth_of_ker C₀ o₀.A o₀.A g o₀.ab o₀.ab hg hg (AbDual.swap o₀.P) hs ?_ e heu ?_ (-φ'.flip)
    (GlobalTheory.SymmPoincare.isCorrForm_swap hφ) x ?_
  · rw [AbDual.triv_ev_iff hs, AbDual.evc_swap o₀.isLB, ← AbDual.triv_ev_iff o₀.isLB]
    exact o₀.rig₁
  · intro v hv
    rw [AbDual.triv_ev_iff hs, AbDual.evc_swap o₀.isLB, ← AbDual.triv_ev_iff o₀.isLB] at hv
    exact hker _ v hv
  · intro y hy
    simp [hx y hy]

end GlobalTheory.HTLagr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens)

def IsCoc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')

def CechFG (R : Type) [CommRing R] (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) : Prop :=
  ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, IsCoc W (e k)) ∧
    ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (r : Fin N → R) (h : ∀ i : J, Γ(Z, W i)),
      ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') + ∑ k, act i i' (r k) * e k i i'

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

def fv (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) : Γ(Z, B.1) :=
  f (Opposite.op A) (Opposite.op B) (homOfLE h).op

def gv (g : C0 (OAff s)) (A : Z.affineOpens) : Γ(Z, A.1) := g (Opposite.op A)

theorem fv_d0 (g : C0 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (d0 (OAff s) g) h = gv s g B - resG Z h (gv s g A) := rfl

theorem fv_add (f f' : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (f + f') h = fv s f h + fv s f' h := rfl

theorem fv_smul (r : R) (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (r • f) h = (secMap s B.1).hom r * fv s f h := rfl

theorem res_val (f : Z1 (OAff s)) {A B C : Z.affineOpens} (hBA : B.1 ≤ A.1) (hCB : C.1 ≤ B.1) :
    resG Z hCB (fv s f.1 hBA) = fv s f.1 (hCB.trans hBA) - fv s f.1 (A := B) hCB :=
  eq_sub_of_add_eq (f.2 (homOfLE hBA).op (homOfLE hCB).op).symm

variable (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))

def rho (f : C1 (OAff s)) (i i' : J) : Γ(Z, W i ⊓ W i') :=
  fv s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
    fv s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right

theorem rho_isCoc (hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (f : Z1 (OAff s)) :
    IsCoc W (rho W s hW hW2 f.1) := by
  intro i i' i''
  let T : Z.affineOpens := ⟨W i ⊓ W i' ⊓ W i'', hW3 i i' i''⟩
  have h1 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_left inf_le_left
  have h2 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_right inf_le_left
  have h3 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h4 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h5 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have h6 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  simp only [rho, map_sub]
  rw [h1, h2, h3, h4, h5, h6]
  ring

theorem rho_add (f f' : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (f + f') i i' = rho W s hW hW2 f i i' + rho W s hW hW2 f' i i' := by
  simp only [rho, fv_add]
  ring

theorem rho_smul (r : R) (f : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (r • f) i i' = (secMap s (W i ⊓ W i')).hom r * rho W s hW hW2 f i i' := by
  simp only [rho, fv_smul]
  ring

theorem rho_zero (i i' : J) : rho W s hW hW2 0 i i' = 0 := sub_self (0 : Γ(Z, W i ⊓ W i'))

theorem rho_sum {N : ℕ} (r : Fin N → R) (f : Fin N → C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (∑ k, r k • f k) i i' = ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * rho W s hW hW2 (f k) i i' := by
  induction N with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact rho_zero W s hW hW2 i i'
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, rho_add, rho_smul, ih]

theorem rho_d0 (g : C0 (OAff s)) (i i' : J) :
    rho W s hW hW2 (d0 (OAff s) g) i i' =
      resG Z inf_le_left (-gv s g ⟨W i, hW i⟩) - resG Z inf_le_right (-gv s g ⟨W i', hW i'⟩) := by
  simp only [rho, fv_d0, map_neg]
  ring

end GlobalTheory.CechFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartOfPeriodTauMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartOfPeriodTauMonomial
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTau

theorem commGroup_seven_term_product_rearrange {G : Type} [CommGroup G] (a b c A B C D : G) :
    a * b * c * A * (b * B)⁻¹ * (c * C)⁻¹ * D⁻¹ = a * (A * B⁻¹ * C⁻¹ * D⁻¹) := by
  simp only [mul_inv]
  calc _ = a * (A * B⁻¹ * C⁻¹ * D⁻¹) * (b * b⁻¹) * (c * c⁻¹) := by ac_rfl
    _ = _ := by simp


set_option maxHeartbeats 1000000 in
theorem exists_isUnitTau : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → (∀ i y z, gam i y z = gam i z y) → (∀ i, t i ≠ 0) → ∀ y z, ∃ τ₀, IsUnitTau Q t gam y z τ₀ := by
  intro R _ _ Q m t gam hM hsym ht y z
  obtain ⟨n1, p1, hp1⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM (y + z)
  obtain ⟨n2, p2, hp2⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM y
  obtain ⟨n3, p3, hp3⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q t gam hM z
  have hc0 : Q.c 0 = η[Q.P.A] := by
    have h := Q.c_add 0 0
    rw [add_zero] at h
    have h' : Q.c 0 * Q.c 0 = Q.c 0 := h.symm
    have h1 : Q.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hc0' : (Q.c 0).left = eSec Q.P.A := by rw [hc0]; rfl
  let T := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ p1 (LB.invGen Q.P.L _ _ p2))
    (LB.invGen Q.P.L _ _ p3)) (LB.invGen Q.P.L _ _ Q.rig)

  have hT : T.IsGen :=
    LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _
      (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ hp1.1 (LB.isGen_invGen (L := Q.P.L) _ _ _ hp2.1))
      (LB.isGen_invGen (L := Q.P.L) _ _ _ hp3.1)) (LB.isGen_invGen (L := Q.P.L) _ _ _ Q.rig_gen)
  have hF : FormEq (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (Q.c (y + z)).left) (fun _ : PUnit => (Q.c y).left))
      (fun _ : PUnit => (Q.c z).left)) (fun _ : PUnit => eSec Q.P.A))
      (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => -(-1 : ℤ))) (fun _ : PUnit => -(-1 : ℤ)))
        (fun _ : PUnit => -(1 : ℤ)))
      (K' := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hc0', neg_neg]
    simp [Matrix.vecHead, Matrix.vecTail, hc0']
  obtain ⟨τ₀, hτ, hv⟩ := exists_gen Q.P.isLB hF T hT
  refine ⟨τ₀, hτ, ?_⟩

  obtain ⟨-, hn1, e1, he1, hv1⟩ := hp1
  obtain ⟨-, hn2, e2, he2, hv2⟩ := hp2
  obtain ⟨-, hn3, e3, he3, hv3⟩ := hp3
  have hne : ∀ i, algebraMap R (FractionRing R) (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (ht i)
  let e' : (FractionRing R)ˣ := ∏ i, Units.mk0 _ (hne i) ^ gam i y z
  have he' : (e' : FractionRing R) = ∏ i, algebraMap R _ (t i) ^ gam i y z := by
    simp [e', Units.coe_prod]
  have hexp : ∀ i, (n1 i : ℤ) = gam i y z + n2 i + n3 i := by
    intro i
    have a := hn1 i
    have b := hn2 i
    have c := hn3 i
    have s := hsym i y z
    simp only [map_add (f := _), LinearMap.add_apply] at a
    linarith
  have hee : e1 = e' * e2 * e3 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he2, he3, he']
    simp only [map_prod, map_pow]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne i), ← zpow_add₀ (hne i), hexp i]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  refine ⟨e', he', fun zz J hJ => ?_⟩
  rw [hv _ _ zz J hJ]
  simp only [DegPre.tau, DegPre.rigK, T, val_mul hJ, val_inv, val_pull hJ]
  rw [hv1 zz J hJ, hv2 zz J hJ, hv3 zz J hJ, hee, hu, hu, map_mul, map_mul, Category.id_comp]
  exact commGroup_seven_term_product_rearrange _ _ _ _ _ _ _

end GlobalTheory.UnitTau
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartOfPeriodTauMonomialStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitPartOfPeriodTau_monomial : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → (∀ i y z, gam i y z = gam i z y) → (∀ i, t i ≠ 0) → ∀ y z, ∃ τ₀, IsUnitTau Q t gam y z τ₀ := by
  first | exact @GlobalTheory.UnitTau.exists_isUnitTau | exact GlobalTheory.UnitTau.exists_isUnitTau | (intros; apply GlobalTheory.UnitTau.exists_isUnitTau <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixTransposeEqAtPolarizedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixTransposeEqAtPolarizedPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.KS GlobalTheory.KS.Sym

noncomputable section

namespace GlobalTheory.FibSym

def chartPullComp {X X' Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ X') :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h :=
  have hm : ∀ (y : Y') (J : PUnit → L.ι), y ∈ (L.pull (h ≫ F)).U J → h y ∈ (L.pull F).U J := fun y J hy =>
    (mem_pull (L := L) (F := F) (x := h y) (J := J)).2 ((mem_pull (L := L) (F := h ≫ F) (x := y) (J := J)).1 hy)
  { idx := fun J => J
    le := fun J y hy => hm y J hy
    g := fun y J J' hj hj' => (gm_pull_g L (h ≫ F) (𝟙 _) y J J' hj hj').trans
      (by rw [Category.id_comp]; exact (gm_pull_g L F h y J J' (hm y J hj) (hm y J' hj')).symm) }

theorem square_fibre_affine_opens_grp (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R]
    (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G] [IsSeparated G.hom] (m : P₀.A.left ⟶ G.left)
    (h : IsGrpPullback P₀.A G (spMap x₀) m) :
    (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (G ⊗ G).left, IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧
    IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧
    (∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧
    ∀ W W' : G.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from G.left) := by
      rw [← terminal.comp_from G.hom]; infer_instance
    exact hW.inf hW'

theorem exists_symm_of_ksCoc_grp (l₁ : Out.Laws) (l₂ : Out.Laws2)
    (hT : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A))
    (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hv : IsLieBasis v)
    (hdd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G]
    [IsSeparated G.hom] (m : P₀.A.left ⟶ G.left) (L : LB G.left) [Finite L.ι] (D : R → K)
    (d : L.ι → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i))
    (hpb : IsGrpPullback P₀.A G (spMap x₀) m) (hL : L.IsLB) (haff : ∀ i, IsAffineOpen (L.U i))
    (hiso : LBIso P₀.L (L.pull m)) (hks : KSCoc P₀.A.hom G.hom m D L.U dd d θ) (hφ : IsDlog m L dd φ) :
    ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ) := by
  obtain ⟨⟨m₂, hsq, sq₀, sqb⟩, hsep, hpull, hpre, hinf⟩ := square_fibre_affine_opens_grp K P₀ R x₀ G m hpb
  obtain ⟨hc, hind⟩ := (GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd _ m L hL hiso).2 φ hφ
  have hm : m ≫ G.hom = P₀.A.hom ≫ spMap x₀ := hpb.1.w
  have prod := fun W W' hW hW' => GlobalTheory.KS.ProdLift.main K R x₀ G P₀.A m m₂ D W W' hm hsq hW hW' _ rfl
  choose d₂ hd₂ c₁ c₂ using fun i j => (prod _ _ (haff i) (haff j)).1 (d i) (d j) (hks.der i) (hks.der j)
  choose w a₁ a₂ a₃ a₄ w₀ w₁ w₂ using fun a =>
    GlobalTheory.KS.SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a) _ _ (Or.inl ⟨rfl, rfl⟩)
  choose w' b₁ b₂ b₃ b₄ w₀' w₂' w₁' using fun a =>
    GlobalTheory.KS.SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a) _ _ (Or.inr ⟨rfl, rfl⟩)
  have hw : ∀ a, IsVF _ (w a) := fun a => ⟨a₁ a, a₂ a, a₃ a, a₄ a⟩
  have hw' : ∀ a, IsVF _ (w' a) := fun a => ⟨b₁ a, b₂ a, b₃ a, b₄ a⟩
  have cov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := top_le_iff.1
    ((le_iSup_inf_preimage m L.U hL.cover ⊤).trans (iSup_mono fun _ => inf_le_right))
  obtain ⟨k, e, e', h₁, h₂, h₃, h₄, h₅⟩ := exists_square_data (θ := θ) sq₀ hsq.1 hsq.2 hL hd₂ hφ hc hw hw' w₀ w₁ w₂ w₀' w₂' w₁'
    (fun i i' j O hO f => diff_prod x₀ (hks.der i) (hks.der i') (hks.der j) (haff i) (haff i') (haff j) sqb
      (hd₂ i j) (hd₂ i' j) hsq.1 hsq.2 inf_le_left inf_le_left inf_le_right inf_le_right
      (fun x hx => by exact ⟨hx.1.1, hx.2⟩) (fun x hx => by exact ⟨hx.1.2, hx.2⟩) (c₁ i j) (c₂ i j) (c₁ i' j) (c₂ i' j)
      (prod _ _ (hinf _ _ (haff i) (haff i')) (haff j)).2 (fun a => θ a i i') (hks.diff i i' _ le_rfl) hw w₁ w₂ O hO f)
    (fun i j j' O hO f => diff_prod x₀ (hks.der j) (hks.der j') (hks.der i) (haff j) (haff j') (haff i) sqb
      (hd₂ i j) (hd₂ i j') hsq.2 hsq.1 inf_le_right inf_le_right inf_le_left inf_le_left
      (fun x hx => by exact ⟨hx.1, hx.2.1⟩) (fun x hx => by exact ⟨hx.1, hx.2.2⟩) (c₂ i j) (c₁ i j) (c₂ i j') (c₁ i j')
      (fun a b ha hb u u' => (prod _ _ (haff i) (hinf _ _ (haff j) (haff j'))).2 a b ha hb u' u)
      (fun a => θ a j j') (hks.diff j j' _ le_rfl) hw' w₂' w₁' O hO f)
    _ (fun _ => le_rfl) (fun a => GlobalTheory.KS.Primitive.cech_primitive l₁ l₂ hT K P₀ _ _ (φ a) cov (hc a))
  refine GlobalTheory.KS.exists_isSymm_of_square K _ _ P₀.A.hom _ _ L.ι _ g θ φ hsep hpull (fun i => hpre _ (haff i)) hind _ _ k e e' ?_
    h₁ h₂ h₃ h₄ h₅
  refine top_le_iff.1 fun x _ => ?_
  have pt : ∀ y : P₀.A.left, ∃ i, y ∈ m ⁻¹ᵁ L.U i := fun y =>
    TopologicalSpace.Opens.mem_iSup.1 (cov.ge trivial)
  obtain ⟨i, hi⟩ := pt ((fst P₀.A P₀.A * snd P₀.A P₀.A).left x)
  obtain ⟨j, hj⟩ := pt ((fst P₀.A P₀.A).left x)
  obtain ⟨l, hl⟩ := pt ((snd P₀.A P₀.A).left x)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, l), ⟨hi, hj⟩, hl⟩


open GlobalTheory.LogKSBal in
theorem map_transpose_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (x₀ : Γ(X, U.1) →+* K) (P₀ : Out.PolAV (Sp K)) (mm : P₀.A.left ⟶ t.G.left), IsGrpPullback P₀.A t.G (spMap x₀ ≫ chart U) mm → LBIso P₀.L (t.PP.L.pull mm) → U.1 ≤ V → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → (Θ.map x₀)ᵀ = Θ.map x₀ := by
  intro E _ _ _ H X t V U n v hv hb K _ _ x₀ P₀ mm hpq hPL hUV D Θ hKS
  letI : GrpObj ((Over.pullback (chart U)).obj t.G) := Functor.grpObjObj
  let G := (Over.pullback (chart U)).obj t.G
  have hs := IsSemiAbelian.pullback (chart U) t.G t.semi
  have : IsSeparated G.hom := hs.separated
  have : QuasiCompact G.hom := hs.quasiCompact
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := P₀.isAb.comm
  let io : G.left ⟶ t.G.left := pullback.fst t.G.hom (chart U)
  have hpb : IsGrpPullback G t.G (chart U) io := isGrpPullback_pullback t.G (chart U)
  have hw : mm ≫ t.G.hom = (P₀.A.hom ≫ spMap x₀) ≫ chart U := by
    rw [hpq.1.w, Category.assoc]
  let m : P₀.A.left ⟶ G.left := pullback.lift mm (P₀.A.hom ≫ spMap x₀) hw
  have hmio : m ≫ io = mm := pullback.lift_fst _ _ _
  have hmG : m ≫ G.hom = P₀.A.hom ≫ spMap x₀ := pullback.lift_snd _ _ _
  rw [← hmio] at hpq hPL
  have hm : IsGrpPullback P₀.A G (spMap x₀) m := IsGrpPullback.cancel hpb hpq hmG
  obtain ⟨b₁, b₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t x₀ _ n v hv hb
  obtain ⟨u, hu, hbas, -⟩ := exists_lieBasis t hpq _ b₁ b₂
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hbas.1 a)).1
  obtain ⟨L, hfin, hL, haff, hiso, d, hd⟩ := exists_ksCoc t hUV hKS hpb.1 x₀ hpq hbas.1 hu hdd
  have hI : LBIso P₀.L (L.pull m) := LBIso.trans P₀.isLB (pull_isLB t.PP.isLB _) (pull_isLB hL _) hPL
    (hiso.chartPull (chartPullComp t.PP.L io m) (Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hbas hdd _ _ L hL hI
  obtain ⟨Θ', hs', hΘ'⟩ := exists_symm_of_ksCoc_grp GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.T.theorem_of_cube_polAbelianScheme K P₀ n u dd hbas hdd _ x₀ G m L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e : Θ' = -Θ.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [lc_sub]
    exact hΘ' b
  have h : Θ'ᵀ = Θ' := hs'
  rwa [e, Matrix.transpose_neg, neg_inj] at h

end GlobalTheory.FibSym

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixTransposeEqAtPolarizedPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_transpose_eq_at_polarized_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (x₀ : Γ(X, U.1) →+* K) (P₀ : Out.PolAV (Sp K)) (mm : P₀.A.left ⟶ t.G.left), IsGrpPullback P₀.A t.G (spMap x₀ ≫ chart U) mm → LBIso P₀.L (t.PP.L.pull mm) → U.1 ≤ V → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → (Θ.map x₀)ᵀ = Θ.map x₀ := by
  first | exact @GlobalTheory.FibSym.map_transpose_eq | exact GlobalTheory.FibSym.map_transpose_eq | (intros; apply GlobalTheory.FibSym.map_transpose_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtInvariantFieldTranslateSqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtInvariantFieldTranslateSqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertCoeffRing

theorem spMap_fstHom_surjective (B : Type) [CommRing B] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
  intro p
  haveI := p.isPrime
  refine ⟨(⟨p.asIdeal.comap (algebraMap B (DualNumber B)), Ideal.IsPrime.comap _⟩ : PrimeSpectrum B), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change (algebraMap B (DualNumber B)) x.fst ∈ p.asIdeal ↔ x ∈ p.asIdeal
  have hx : x = algebraMap B (DualNumber B) x.fst + TrivSqZeroExt.inr x.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hn : (TrivSqZeroExt.inr x.snd : DualNumber B) ∈ p.asIdeal := by
    apply p.isPrime.mem_of_pow_mem 2
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
    exact zero_mem _
  constructor
  · intro h
    rw [hx]
    exact add_mem h hn
  · intro h
    have h2 := sub_mem h hn
    rwa [show x - TrivSqZeroExt.inr x.snd = algebraMap B (DualNumber B) x.fst by
      rw [sub_eq_iff_eq_add]; exact hx] at h2

theorem evalPt_tvE_mul : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  intro R _ G _ _ u dd hinv B _ _ e he z O h
  set φ : R →+* B := algebraMap R B with hφ
  have hz : z.left ≫ G.hom = spMap φ := Over.w z
  have eφ : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap B (DualNumber B)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hv : (tv u).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
    (Over.w (tv u)).trans (Category.comp_id _)
  have h2 : (spMap (dualMap φ) ≫ (tv u).left) ≫ G.hom = (tEpsG (z.left ≫ G.hom)).hom := by
    show _ = spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom
    refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
    rw [hz, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eφ]
  let g' : tEpsG (z.left ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap B (DualNumber B)) ≫ z.left) (Category.assoc _ _ _)
  let v' : tEpsG (z.left ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv u).left) h2
  have htr : IsTr G φ z.left u (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩

  have hk : ∀ (t : B) (ht : t * t = 0), ∃ kt : Chart.sp (R₀ := R) B ⟶ tEpsG (z.left ≫ G.hom),
      kt.left = spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ∧ kt ≫ g' = z ∧
        kt ≫ v' = Chart.spMap (GlobalTheory.SqZero.epsTo R t ht) ≫ tvE u := by
    intro t ht
    have hτa : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom.comp (algebraMap B (DualNumber B)) =
        RingHom.id B := by
      ext b
      simp [GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl]
    have hsp : spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ≫ spMap (algebraMap B (DualNumber B)) =
        𝟙 _ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτa, CommRingCat.ofHom_id, Spec.map_id]
    refine ⟨Over.homMk (spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom) ?_, rfl, ?_, ?_⟩
    · show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom = _
      rw [← Category.assoc, hsp, Category.id_comp]
      exact hz
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left = z.left
      rw [← Category.assoc, hsp, Category.id_comp]
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (dualMap φ) ≫ (tv u).left = (Chart.spMap (GlobalTheory.SqZero.epsTo R t ht)).left ≫ (tv u).left
      rw [Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.dualTo_apply, GlobalTheory.SqZero.epsTo, dualMap, hφ, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def]
  obtain ⟨k, hkl, hkg, hkv⟩ := hk e he
  obtain ⟨k0, hk0l, hk0g, hk0v⟩ := hk 0 (mul_zero 0)

  have hone : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u = 1 := by
    let K : Chart.sp (R₀ := R) B ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)).toRingHom) (by
        show _ ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ = spMap φ
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun a => ?_
        simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, hφ])
    have e1 : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u =
        K ≫ smT (𝟙 (Sp R)) 0 (tv u) := by
      apply Over.OverMorphism.ext
      show (Chart.spMap _).left ≫ (tv u).left = spMap _ ≫ (smT (𝟙 (Sp R)) 0 (tv u)).left
      rw [smT_left, Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, epsMul]
    rw [e1, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.comp_one]
  have hp : (Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z = k ≫ (g' * v') := by
    rw [MonObj.comp_mul, hkg, hkv, mul_comm]
  have hp0 : k0 ≫ (g' * v') = z := by
    rw [MonObj.comp_mul, hk0g, hk0v, hone, _root_.mul_one]
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = z.left := by
    have := congrArg (fun q => q.left) hp0
    simp only [Over.comp_left, hk0l] at this
    have hfh : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) (0 : B) (mul_zero 0)).toRingHom =
        (TrivSqZeroExt.fstHom B B B).toRingHom := RingHom.ext fun a => by
      simp [GlobalTheory.SqZero.dualTo_apply]
    rw [← hfh]
    exact this
  have hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O := by
    intro p _
    obtain ⟨q, rfl⟩ := spMap_fstHom_surjective B p
    rw [← hfst] at h
    exact h (Set.mem_univ q)
  have hpl : ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left =
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left := by
    rw [hp, Over.comp_left, hkl]
  have h' : ⊤ ≤ ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left ⁻¹ᵁ O := by
    rw [hpl]
    intro q _
    exact hw (Set.mem_univ _)
  refine ⟨h', fun f => ?_⟩
  have hval : valR (g' * v').left O f = evalPt (g' * v').left O hw f := by
    unfold valR; rw [dite_eq_left hw]; rfl
  have hvalz : valR z.left O (dd O f) = evalPt z.left O h (dd O f) := by
    unfold valR; rw [dite_eq_left h]; rfl
  have hsnd := hinv.2 B φ z.left (g' * v').left O f hz h htr
  rw [hval, hvalz] at hsnd
  have key : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst + (evalPt (g' * v').left O hw f).snd * e := by
    rintro y hy rfl
    rw [evalPt_spMap_comp _ _ O hw hy f]
    exact GlobalTheory.SqZero.dualTo_apply _ _ _ _
  have key0 : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst := by
    rintro y hy rfl
    exact evalPt_spMap_comp _ _ O hw hy f
  rw [key _ h' hpl.symm, key0 _ h hfst, hsnd]
  ring

end GlobalTheory.VertCoeffRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtInvariantFieldTranslateSqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_at_invariantField_translate_sqZero : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  first | exact @GlobalTheory.VertCoeffRing.evalPt_tvE_mul | exact GlobalTheory.VertCoeffRing.evalPt_tvE_mul | (intros; apply GlobalTheory.VertCoeffRing.evalPt_tvE_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHom
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

namespace GlobalTheory.BalProj

theorem actMat_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  intro E _ _ _ H X t S _ x0 n v A hv hb hA
  classical
  let T : Fin n → TanM x0 t.G := fun i => GlobalTheory.LieMet.tanOf (hv i)
  have uniq : ∀ c c' : Fin n → S, ∑ j, c j • T j = ∑ j, c' j • T j → c = c' := by
    intro c c' h
    obtain ⟨cf, _, hcf⟩ := hb _ (GlobalTheory.LieMet.isTan_tv (∑ j, c j • T j))
    have h1 : IsCombAtG t x0 v c (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c _).2 rfl
    have h2 : IsCombAtG t x0 v c' (tv (∑ j, c j • T j)).left := (GlobalTheory.LieMet.isComb_iff T c' _).2 h
    exact (hcf _ h1).trans (hcf _ h2).symm
  have hact : ∀ a i, ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i) = ∑ j, A a i j • T j := fun a i =>
    (GlobalTheory.LieMet.isComb_iff T (A a i) (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (T i))).1 (hA a i)
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have e : ∑ k, A 1 i k • T k = ∑ k, (1 : Matrix (Fin n) (Fin n) S) i k • T k := by
      rw [← hact, map_one, Module.End.one_apply]
      simp [Matrix.one_apply]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a + b) i k • T k = ∑ k, (A a + A b) i k • T k := by
      rw [← hact, map_add (f := _), LinearMap.add_apply, hact, hact]
      simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
    exact congrFun (uniq _ _ e) j
  · intro a b
    ext i j
    have e : ∑ k, A (a * b) i k • T k = ∑ k, (A a * A b) i k • T k := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hact, mul_comm a b, map_mul, Module.End.mul_apply, hact, map_sum]
      simp only [map_smul, hact, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (uniq _ _ e) j

end GlobalTheory.BalProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionMatricesRingHomStatement
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
theorem _root_.GlobalTheory.T.tangentBasis_actionMatrices_ringHom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X : Scheme.{0}} (t : SAB H X) (S : Type) [CommRing S] (x0 : Spec (CommRingCat.of S) ⟶ X) (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) S), (∀ i, IsTanAtG t x0 (v i)) → (∀ w, IsTanAtG t x0 w → ∃! cf : Fin n → S, IsCombAtG t x0 v cf w) → (∀ a i, IsCombAtG t x0 v (A a i) (v i ≫ (t.act.act a).left)) → A 1 = 1 ∧ (∀ a b, A (a + b) = A a + A b) ∧ (∀ a b, A (a * b) = A a * A b) := by
  first | exact @GlobalTheory.BalProj.actMat_ringHom | exact GlobalTheory.BalProj.actMat_ringHom | (intros; apply GlobalTheory.BalProj.actMat_ringHom <;> assumption)
end
end
