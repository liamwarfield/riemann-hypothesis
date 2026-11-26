module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTripleOfSquareGridLatticeCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPolynomialVectorReachedByRealDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareFlipReachesLocalQuotientClasses

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
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

namespace GlobalTheory.Heat.WtAlg

theorem valR_eq' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq' x U h, map_add (f := _)]

theorem valR_sub' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq' x U h, map_sub]

theorem valR_mul'' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq' x U h, map_mul]

theorem valR_zero' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) :
    valR x U (0 : Γ(X, U)) = 0 := by
  unfold valR; split_ifs <;> simp

theorem valR_natCast' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (m : ℕ) : valR x U (m : Γ(X, U)) = m := by
  simp only [valR_eq' x U h, map_natCast]

theorem appLE_congr_top {P P' : Scheme.{0}} (b b' : P ⟶ P') (e : b = b') (h h') :
    b.appLE ⊤ ⊤ h = b'.appLE ⊤ ⊤ h' := by
  subst e; rfl

theorem valR_constFn_congr {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (x x' : Sp A ⟶ X) (p : X ⟶ Sp B)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : x ≫ p = x' ≫ p) (r : B) :
    valR x U (constFn p U r) = valR x' U (constFn p U r) := by
  have key : ∀ (b : Sp A ⟶ X) (hb : ⊤ ≤ b ⁻¹ᵁ U) (y : Γ(Sp B, ⊤)),
      (b.appLE U ⊤ hb).hom ((p.appLE ⊤ U (fun _ _ => trivial)).hom y) = ((b ≫ p).appLE ⊤ ⊤ (fun _ _ => trivial)).hom y := by
    intro b hb y
    rw [← Scheme.Hom.appLE_comp_appLE]; rfl
  rw [valR_eq' x U h, valR_eq' x' U h', constFn, key, key]
  have hh := appLE_congr_top (x ≫ p) (x' ≫ p) e (fun _ _ => trivial) (fun _ _ => trivial)
  rw [hh]

theorem rsT_self {X : Scheme.{0}} {O : X.Opens} (s : Γ(X, O)) : rsT s O = s := by
  simp [rsT, resG]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem c_zero {S : Type} [CommRing S] {φ : R →+* S} (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    c 0 = 1 := by
  have hu : unitOn (c 0) = 1 := unit_ext fun y _ => by
    obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB y (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have e := hc 0 y J hJ
    rw [(val_corr hJ (Y.Φ _ x').s_zero _).trans (val_one _), (val_corr hJ (Y.Φ _ x).s_zero _).trans (val_one _),
      _root_.mul_one] at e
    rw [map_one]; exact e.symm
  have := congrArg (fun u : (Γ(Sp S, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom u.val) hu
  simp only [unitOn, Units.coe_map, Units.val_one, map_one] at this
  exact Units.ext ((Iso.inv_hom_id_apply _ _).symm.trans this)

theorem isWt_add {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f + g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_add' _ _ hV', valR_add' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_add]

theorem isWt_sub {α : Q.X} {V : Y.H.left.Opens} {f g : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hg : IsWt Y α V g) :
    IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_sub' _ _ hV', valR_sub' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    hg S φ x x' c a a' ha ha' hV hV' hq hc, mul_sub]

theorem isWt_zero (α : Q.X) (V : Y.H.left.Opens) : IsWt Y α V 0 := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_zero', valR_zero', mul_zero]

theorem isWt_sum {α : Q.X} {V : Y.H.left.Opens} {I : Type} (s : Finset I) (f : I → Γ(Y.H.left, V))
    (hf : ∀ i ∈ s, IsWt Y α V (f i)) : IsWt Y α V (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsWt Y α V) (fun _ _ => isWt_add) (isWt_zero α V) hf

theorem isRaynaudTorusWeightFunction_weightZero_mul {α : Q.X} {V : Y.H.left.Opens} {g f : Γ(Y.H.left, V)} (hg : IsWt Y 0 V g) (hf : IsWt Y α V f) :
    IsWt Y α V (g * f) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_mul'' _ _ hV', valR_mul'' _ _ hV, hg S φ x x' c a a' ha ha' hV hV' hq hc,
    hf S φ x x' c a a' ha ha' hV hV' hq hc, c_zero x x' c hc, Units.val_one, _root_.one_mul]
  ring

theorem isWt_natCast (V : Y.H.left.Opens) (m : ℕ) : IsWt Y 0 V (m : Γ(Y.H.left, V)) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  rw [valR_natCast' _ _ hV', valR_natCast' _ _ hV, c_zero x x' c hc, Units.val_one, _root_.one_mul]

theorem isWt_constFn (V : Y.H.left.Opens) (r : R) : IsWt Y 0 V (constFn Y.H.hom V r) := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  subst ha ha'
  rw [valR_constFn_congr x'.left x.left Y.H.hom V hV' hV ((Over.w x').trans (Over.w x).symm) r,
    c_zero x x' c hc, Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.WtAlg

namespace GlobalTheory.Heat.WtAlg

theorem op_isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB i k α f hf
  obtain ⟨⟨V, hV⟩, hp, hp', hd⟩ := hB i
  have key : ∀ g : Γ(Y.H.left, h.W i), IsWt Y α (h.W i) g → IsWt Y α (h.W i) (h.d i (h.W i) g) := by
    have := hd α V hV.ge
    rw [← hV] at this
    exact this
  have h2 : IsWt Y 0 (h.W i) (2 : Γ(Y.H.left, h.W i)) := by simpa using isWt_natCast (Y := Y) (h.W i) 2
  have hk : IsWt Y 0 (h.W i) (k : Γ(Y.H.left, h.W i)) := isWt_natCast (h.W i) k
  have hk2 : IsWt Y 0 (h.W i) ((k : Γ(Y.H.left, h.W i)) ^ 2) := by rw [sq]; exact isRaynaudTorusWeightFunction_weightZero_mul hk hk
  have hrp : IsWt Y 0 (h.W i) (rsT (h.p i) (h.W i)) := by rw [rsT_self]; exact hp
  have hrp' : IsWt Y 0 (h.W i) (rsT (h.p' i) (h.W i)) := by rw [rsT_self]; exact hp'
  unfold op
  refine isWt_add (isWt_add (isWt_sub ?_ ?_) ?_) ?_
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) (key f hf)
  · exact isWt_sum _ _ fun a _ => isWt_sum _ _ fun b _ =>
      isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul h2 (isWt_sum _ _ fun a _ => isRaynaudTorusWeightFunction_weightZero_mul (isWt_constFn _ _) (hdd _ _ _ _ hf))
  · exact isRaynaudTorusWeightFunction_weightZero_mul (isWt_add (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk2) hrp) (isRaynaudTorusWeightFunction_weightZero_mul (isRaynaudTorusWeightFunction_weightZero_mul h2 hk) hrp')) hf

end GlobalTheory.Heat.WtAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeightStatement
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
theorem _root_.GlobalTheory.T.torusInvariant_heatOperator_preserves_weight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  first | exact @GlobalTheory.Heat.WtAlg.op_isWt | exact GlobalTheory.Heat.WtAlg.op_isWt | (intros; apply GlobalTheory.Heat.WtAlg.op_isWt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

abbrev bo (R : Type) [CommRing R] (f : R) : (Sp R).affineOpens :=
  (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)

abbrev resV (R : Type) [CommRing R] (f : R) : R →+* Γ(Sp R, (bo R f).1) :=
  ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

abbrev cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) : Γ(X, V) →+* Γ(Y, O) :=
  (π.appLE V O h).hom

def opV {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → Fld Y) (Θ : Matrix (Fin n) (Fin n) Γ(X, V))
    (u : Fin n → Γ(X, V)) (d : Fld Y) {W : Y.Opens} (p p' : Γ(Y, W)) (k : ℕ) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ V)
    (f : Γ(Y, O)) : Γ(Y, O) :=
  2 * (k : Γ(Y, O)) * d O f - ∑ a, ∑ b, cst π V h (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, cst π V h (u a) * dd a O f + (2 * (k : Γ(Y, O)) ^ 2 * rsT p O + 2 * (k : Γ(Y, O)) * rsT p' O) * f

end GlobalTheory.HeatV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

variable {O : Type} [Ring O]

def ActPB {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (z' : SiegPre h M ζ s') (act' : O → (z'.A ⟶ z'.A)) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A))
    (f : S' ⟶ S) : Prop :=
  ∃ (φ : z'.A.left ⟶ z.A.left) (φ₂ : (G2 z'.A).left ⟶ (G2 z.A).left),
    IsGrpPullback z'.A z.A f φ ∧ IsSquare φ φ₂ ∧ LBIso z'.P (z.P.pull φ₂) ∧
      (∀ a, (z'.lev a).left ≫ φ = f ≫ (z.lev a).left) ∧ ∀ o, (act' o).left ≫ φ = φ ≫ (act o).left

theorem ActPB.trans {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S' ⟶ Sp B} {s'' : S'' ⟶ Sp B} {z : SiegPre h M ζ s} {z' : SiegPre h M ζ s'} {z'' : SiegPre h M ζ s''}
    {act : O → (z.A ⟶ z.A)} {act' : O → (z'.A ⟶ z'.A)} {act'' : O → (z''.A ⟶ z''.A)} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m' : ActPB z'' act'' z' act' f') (m : ActPB z' act' z act f) :
    ActPB z'' act'' z act (f' ≫ f) := by
  obtain ⟨φ, φ₂, hφ, hs, hw, hl, ha⟩ := m
  obtain ⟨ψ, ψ₂, hψ, hs', hw', hl', ha'⟩ := m'
  refine ⟨ψ ≫ φ, ψ₂ ≫ φ₂, hψ.comp hφ, GlobalTheory.TChart.AbPol.isSquare_comp hs' hs,
    GlobalTheory.TChart.AbLevel.lbIso_comp z.isLB z'.isLB z''.isLB hw hw', fun a => ?_, fun o => ?_⟩
  · rw [← Category.assoc, hl' a, Category.assoc, hl a, Category.assoc]
  · rw [← Category.assoc, ha' o, Category.assoc, ha o, Category.assoc]

def ZRel {h h' M : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {t : S ⟶ Sp B} (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) {n : ℕ} (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (c : SiegPre h M ζ t) (z : SiegPre h' M ζ t)
    (act : O → (z.A ⟶ z.A)) : Prop :=
  ∃ (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 c.A ∧ pr ≫ inc = act e ∧
    LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) ∧ (∀ a, c.lev a ≫ inc = z.lev (jl a)) ∧
    ∀ a, z.lev a = (List.ofFn fun k => c.lev (κ k a) ≫ inc ≫ act (o k)).prod

theorem isQProjOver_comp_immersion {R : Type} [CommRing R] {X Y : Scheme.{0}} (j : X ⟶ Y) (s : Y ⟶ Sp R)
    (hj : IsImmersion j) (hq : QuasiCompact j) (hs : IsQProjOver s) : IsQProjOver (j ≫ s) := by
  obtain ⟨N, i, hi, hiq, rfl⟩ := hs
  exact ⟨N, j ≫ i, inferInstance, inferInstance, (Category.assoc _ _ _).symm⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

section Linear

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {H : Type*} [AddCommGroup H] [Module K H] [Module R H]
  [IsScalarTower R K H]

end Linear

section Sheaf

variable {O : Type} [CommRing O] {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T}

def resSec (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) (A : X.Modules) (t : Γ((Scheme.Modules.pullback f).obj A, ⊤)) :
    Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤) :=
  ((sqIso w).hom.app A).app ⊤ (QCoh.pullbackSections (spMap (algebraMap R K)) _ (V := ⊤) le_top t)


variable (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {A B A' B' : X.Modules} {D : T.Modules}
  (a : (Scheme.Modules.pullback f₀).obj A ⟶ D) (b : D ⟶ (Scheme.Modules.pullback f₀).obj B)

def Reads {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    (E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H) (β : LinearMap.BilinForm K H) (F : Submodule K H)
    (N : Submodule R H) : Prop :=
  (∀ s, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = 0 ↔ E s ∈ F) ∧
    (∀ s, E s ∈ N ↔ ∃ t, s = ((Scheme.Modules.pullback ξ).map a).app ⊤ (resSec w A t)) ∧
    (∀ s, E s ∈ β.dualSubmodule N ↔ ∃ t, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = resSec w B t) ∧
    Function.Surjective (((Scheme.Modules.pullback ξ).map b).app ⊤)


variable {α : O →+* End A} {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {r : ℕ}

end Sheaf

section Forms

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

end Forms

section Tower

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

structure FinTower (Γ : PDivGroup p R) (G : Over (Sp R)) [GrpObj G] : Type where

  y : ∀ n, SpAlg R (Γ.A n) ⟶ G

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : WithConv (Γ.A n →ₐ[R] B)),
    spOver (φ * ψ).ofConv ≫ y n = (spOver φ.ofConv ≫ y n) * (spOver ψ.ofConv ≫ y n)

  inj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : Γ.A n →ₐ[R] B),
    spOver φ ≫ y n = spOver ψ ≫ y n → φ = ψ

  surj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (z : SpAlg R B ⟶ G),
    z ^ p ^ n = 1 → ∃ φ : Γ.A n →ₐ[R] B, spOver φ ≫ y n = z

  res : ∀ n, spOver (Γ.res n : Γ.A (n + 1) →ₐ[R] Γ.A n) ≫ y (n + 1) = y n

def FinTower.ofTower {Γ : PDivGroup p R} {G : Over (Sp R)} [GrpObj G] (t : Γ.TorsionTower G) : FinTower Γ G :=
  ⟨t.y, t.mul, t.inj, fun n B _ _ _ => t.surj n B, t.res⟩

def IsWeilHom {𝒜 ℬ : PDivGroup p R} {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (t : 𝒜.TorsionTower A)
    (u : ℬ.TorsionTower B) (P : LB (A ⊗ B).left) (w : 𝒜 ⟶ ℬ.dual) : Prop :=
  ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ,
    Out.WeilIs (A ⊗ B) P ((p ^ n : ℕ) : ℤ) (T := SpAlg R (𝒜.A n ⊗[R] ℬ.A n))
      (CartesianMonoidalCategory.lift
        (spOver (Algebra.TensorProduct.includeLeft : 𝒜.A n →ₐ[R] 𝒜.A n ⊗[R] ℬ.A n) ≫ t.y n) 1)
      (CartesianMonoidalCategory.lift 1
        (spOver (Algebra.TensorProduct.includeRight : ℬ.A n →ₐ[R] 𝒜.A n ⊗[R] ℬ.A n) ≫ u.y n))
      (unitOn U) ∧
    ∀ χ : CartierDual R (ℬ.A n), w.app n χ = TensorProduct.rid R _ (χ.ofConv.lTensor _ U.val)

variable [Fact p.Prime] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

variable [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

end Tower

end GlobalTheory.BadPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
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

namespace GlobalTheory.Heat.InvWt

theorem top_le_preimage_of_fst {S : Type} [CommRing S] {X : Scheme.{0}} (w : Sp (DualNumber S) ⟶ X) (a : Sp S ⟶ X) (U : X.Opens)
    (h : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = a) (ha : ⊤ ≤ a ⁻¹ᵁ U) : ⊤ ≤ w ⁻¹ᵁ U := by
  intro p _
  let p0 : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (DualNumber S)) p
  have hp : (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) p0 = p := by
    apply PrimeSpectrum.ext
    ext z
    show algebraMap S (DualNumber S) (TrivSqZeroExt.fst z) ∈ p.asIdeal ↔ z ∈ p.asIdeal
    have hz : TrivSqZeroExt.inr (TrivSqZeroExt.snd z) ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    constructor
    · intro h1
      rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
      exact p.asIdeal.add_mem h1 hz
    · intro h1
      have e : TrivSqZeroExt.inl (TrivSqZeroExt.fst z) = z - TrivSqZeroExt.inr (TrivSqZeroExt.snd z) := by
        rw [eq_sub_iff_add_eq, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
      rw [e]
      exact p.asIdeal.sub_mem h1 hz
  have hm : p0 ∈ a ⁻¹ᵁ U := ha (Set.mem_univ _)
  rw [← h] at hm
  show w p ∈ U
  rw [← hp]
  exact hm

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map f.toMonoidHom u) := by
  ext
  have e := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem exists_tan_over {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    {S : Type} [CommRing S] (φ : R →+* S) :
    ∃ v' : Over.mk (spMap ((algebraMap S (DualNumber S)).comp φ)) ⟶ G,
      v'.left = spMap (dualMap φ) ≫ (tv v).left ∧
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v'.left = (1 : Over.mk (spMap φ) ⟶ G).left := by
  refine ⟨Over.homMk (spMap (dualMap φ) ≫ (tv v).left) ?_, rfl, ?_⟩
  · rw [Category.assoc, Over.w (tv v)]
    simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
    congr 1
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp]
  · let ψ : Over.mk (spMap φ) ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) (by
        simp only [overAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp]
        congr 1
        ext r
        simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hψ : ψ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp R)) (tm ((0 : R) • LinearMap.id)) = ψ := by
      apply Over.OverMorphism.ext
      show (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ spMap _ =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)
      simp only [spMap, ← Spec.map_comp, Category.assoc]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      simp [dualMap, CommRingCat.hom_comp, tm]
    have e := congrArg (·.left) (Formalism.L2.Pj.tan_pull (𝟙 (Sp R)) ψ hψ (tv v) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v))
    simpa [ψ] using e

theorem cv_pull_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T T' : Over (Sp R)} (k : T' ⟶ T) (x x' : T ⟶ Y.H) (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (k ≫ x')).s χ) (𝟙 _) y J =
        gm (𝟙 T'.left) y ⊤ (Units.map k.left.appTop.hom.toMonoidHom (u χ)) * val ((Y.Φ _ (k ≫ x)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have p' := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x')).2 χ y J hJ
  have p := ((GlobalTheory.TorusModel.isPull_iff k _ _).1 (Y.rep.1 _ _ k x)).2 χ y J hJ
  let g : LB.Gen (LB.LinComb Q.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top (u χ)⟩
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) z J', Good Q.P.L z J' → val g r z J' = gm r z ⊤ (u χ) :=
    fun Z r z J' hJ' => gm_res r z le_top (hJ'.mem PEmpty.elim r) (u χ)
  have hC := corr_of_val Q.P.isLB (t := (Y.Φ _ x').s χ) (t' := LB.mulGen Q.P.L _ _ _ _ g ((Y.Φ _ x).s χ))
    (fun y' J' hJ' => by rw [val_mul hJ', hg _ _ _ _ hJ']; exact h χ y' J' hJ')
  have e := val_corr hJ hC k.left
  rw [val_mul hJ, hg _ _ _ _ hJ] at e
  show GlobalTheory.TorusModel.cv _ χ y J = _ * GlobalTheory.TorusModel.cv _ χ y J
  rw [p', p, e]
  congr 1
  have e2 := gm_pull (𝟙 _) k.left y ⊤ trivial (u χ)
  rw [Category.id_comp] at e2
  rw [← e2]
  rfl

theorem cv_mul_of_unit {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) {T : Over (Sp R)} (X X' v : T ⟶ Y.H) (hq : X' ≫ Y.q = X ≫ Y.q)
    (u : Q.X → (Γ(T.left, ⊤))ˣ)
    (h : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ X').s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ X).s χ) (𝟙 _) y J) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (X' * v)).s χ) (𝟙 _) y J = gm (𝟙 T.left) y ⊤ (u χ) * val ((Y.Φ _ (X * v)).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X v)).2 χ y J hJ
  have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ X' v)).2 χ y J hJ
  rw [Y.Φ_b, Y.Φ_b] at h1 h2
  rw [hq] at h2
  have h3 := h χ y J hJ
  apply mul_right_cancel (b := DVR.th Q y J (DVR.cP Q _ χ) (X ≫ Y.q) (v ≫ Y.q))
  show GlobalTheory.TorusModel.cv _ χ y J * _ = _ * GlobalTheory.TorusModel.cv _ χ y J * _
  rw [h2, _root_.mul_assoc, h1, ← _root_.mul_assoc]
  congr 1

theorem _root_.GlobalTheory.Heat.IsInv.isWt : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  intro R _ _ Q O _ _ _ oa Y v dd hinv α V f hf
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
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
  obtain ⟨v'', hv₁, hv₂⟩ := exists_tan_over Y.H v φ
  have hιπ : ie ≫ π = 𝟙 _ := by
    ext1
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _
    simp only [spMap, ← Spec.map_comp]
    rw [← Spec.map_id]; congr 1
  have hiev : ie ≫ v'' = 1 := by
    ext1
    exact hv₂
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have hW : ∀ z : Over.mk (spMap φ) ⟶ Y.H, ie ≫ (π ≫ z * v'') = z := by
    intro z
    rw [MonObj.comp_mul, ← Category.assoc, hιπ, Category.id_comp, hiev, _root_.mul_one]
  have hWa : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x * v'').left = a := by
    rw [ha]; exact congrArg (·.left) (hW x)
  have hWa' : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (π ≫ x' * v'').left = a' := by
    rw [ha']; exact congrArg (·.left) (hW x')
  have htr : ∀ z : Over.mk (spMap φ) ⟶ Y.H, IsTr Y.H φ z.left v (π ≫ z * v'').left := by
    intro z
    let e : tEpsG (z.left ≫ Y.H.hom) ⟶ Over.mk (spMap φε) := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ spMap φε = spMap (algebraMap S (DualNumber S)) ≫ z.left ≫ Y.H.hom
      rw [Over.w z]
      simp only [Over.mk_hom, Category.id_comp, spMap, φε]
      rw [← Spec.map_comp]; rfl)
    refine ⟨e ≫ π ≫ z, e ≫ v'', ?_, ?_, ?_⟩
    · show 𝟙 _ ≫ spMap (algebraMap S (DualNumber S)) ≫ z.left = _
      rw [Category.id_comp]
    · show 𝟙 _ ≫ v''.left = _
      rw [Category.id_comp, hv₁]
    · rw [← MonObj.comp_mul]
      show 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  let c' : Q.X → (DualNumber S)ˣ := fun χ => Units.map (algebraMap S (DualNumber S)).toMonoidHom (c χ)
  have hqW : (π ≫ x' * v'') ≫ Y.q = (π ≫ x * v'') ≫ Y.q := by
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, hq]
  have hcW := cv_mul_of_unit Y (π ≫ x) (π ≫ x') v'' (by rw [Category.assoc, Category.assoc, hq])
    (fun χ => Units.map π.left.appTop.hom.toMonoidHom (unitOn (c χ))) (cv_pull_of_unit Y π x x' (fun χ => unitOn (c χ)) hc)
  have key := hf (DualNumber S) φε (π ≫ x * v'') (π ≫ x' * v'') c' _ _ rfl rfl
    (top_le_preimage_of_fst _ a V hWa hV) (top_le_preimage_of_fst _ a' V hWa' hV') hqW (fun χ y J hJ => by
      rw [hcW χ y J hJ]
      congr 2
      exact map_unitOn _ _)
  have e₁ := hinv.2 S φ a (π ≫ x * v'').left V f (by rw [ha]; exact Over.w x) hV (ha ▸ htr x)
  have e₂ := hinv.2 S φ a' (π ≫ x' * v'').left V f (by rw [ha']; exact Over.w x') hV' (ha' ▸ htr x')
  rw [← e₁, ← e₂, key]
  show ((c' α : DualNumber S) * _).snd = _
  rw [TrivSqZeroExt.snd_mul]
  simp [c', TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.Heat.InvWt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantFieldStatement
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
theorem _root_.GlobalTheory.T.isRaynaudTorusWeightFunction_invariantField : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (v : TanM (𝟙 (Sp R)) Y.H) (dd : Fld Y.H.left), IsInv Y.H v dd → ∀ (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)), IsWt Y α V f → IsWt Y α V (dd V f) := by
  first | exact @GlobalTheory.Heat.IsInv.isWt | exact GlobalTheory.Heat.IsInv.isWt | (intros; apply GlobalTheory.Heat.IsInv.isWt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
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
namespace GlobalTheory.LocReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def chartHom (Y : Model Xo c β) (U : Y.X.affineOpens) {k : Type} [Field k] {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ gen Y)
    (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) : Γ(Y.X, U.1) →+* ChartRing k m d :=
  (Scheme.stalkClosedPointTo ξ).hom.comp
    (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)

end GlobalTheory.LocReg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
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

namespace GlobalTheory.HeatConn

def IsConnK {R : Type} [CommRing R] {k : Type} [Field k] (A : Over (Sp R)) (L : LB A.left) (A₀ : Over (Sp k))
    (m₀ : A₀.left ⟶ A.left) (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (ed : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)) : Prop :=
  GlobalTheory.KS.LocDerK A₀.hom A.hom m₀ D' ⊤ ed ∧ ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ L.U (jj i)) ∧
    ∀ i i', ed (V i ⊓ V i') (rsT (L.g (jj i) (jj i')).val (V i ⊓ V i')) =
      pbT m₀ (L.g (jj i) (jj i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) *
        (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i')))

end GlobalTheory.HeatConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchedFlipThetaIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigNZ

theorem blkU_mul {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (x y : GA D A × GA D B) : blkU A B e h x * blkU A B e h y = blkU A B e h (x * y) := by
  refine Subtype.ext (Units.ext ?_)
  exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul e _ _ _ _

theorem exists_integral_ne_zero (hSA : GlobalTheory.Published.StrongApproxSU) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) :
    ∃ M : Vol G, M.Is t ∧ ∃ a τ τ' n Φ,
      (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip B t ρ i j n Φ τ τ' ∧
      ∃ g g₁, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := exists_vol G hL t
  obtain ⟨e, Bs, Γ, X, om, om', h, hT, hti⟩ := GlobalTheory.T.exists_thetaTripleOfSquareGrid_latticeCompatible hL W t i j hst M hM
  obtain ⟨R, Rf, hm⟩ := hLM _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := GlobalTheory.T.exists_adm_eq_thetaIntegral_of_conv Γ.M Bs.ψ _ _ om hT.weil dec.1
  have hw0 : G.pl.w G.pl.v0 ∈ locPl G t :=
    Finset.mem_union_left _ (by
      have : G.pl.v0 ∈ G.pl.S0 := by unfold Places.S0; convert Finset.mem_insert_self _ _
      unfold Places.W0; convert Finset.mem_image_of_mem _ this)
  have hv0 := (hti.2.2.1 _).2 ⟨_, hw0, rfl⟩
  have hd : 0 < (spW G i j).rank + (spW₁ G i j).rank := by have := hT.geo.aBig; omega
  obtain ⟨f, hf, h0⟩ := exists_I_ne_zero_at hm hc hco hla hl (GlobalTheory.T.theta_distribution_rational_points_invariant_triple Bs Γ X om om' hT 1 (one_mem _)) hv0
    (GlobalTheory.T.weilRepresentationLocality_tensorModelVW Bs Γ X om om' hT _) (GlobalTheory.T.strongApproximation_splitPlace_skewHermitian_unitary hSA Bs Γ X om om' hT ⟨_, hT.chars.sub hv0⟩)
    (H := Set.range (blkU _ _ e h.JWW)) fun x => by
      obtain ⟨s, g, h1, h2⟩ := GlobalTheory.T.exists_detOne_mul_blockUnitary_decomposition _ _ e h.JWW hd x
      exact ⟨s, _, ⟨g, rfl⟩, h1, h2⟩
  obtain ⟨φ, hφ, hP, _, ⟨g, rfl⟩, hne⟩ := exists_I_ne_zero_kind hm hc hco (H := Set.range (blkU _ _ e h.JWW))
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, (blkU_mul _ _ e h.JWW x y).symm⟩)
    (fun v χ => ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → ∃ n Φ, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) χ)
    (fun v hv φ₀ hφ₀ => by
      obtain ⟨w, hw, ew⟩ := (hti.2.2.1 v).1 hv
      obtain ⟨n, Φ, φ₂, k, φ₃, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.squareFlip_reaches_localQuotient_classes hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ew φ₀ hφ₀
      refine ⟨φ₂, h3.1, fun w' hw' ew' => ?_, _, ⟨k, rfl⟩, φ₃, h4, h5, h6⟩
      obtain rfl : w = w' := (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w hw ew).symm.trans (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w' hw' ew')
      exact ⟨n, Φ, h1, h2, h3⟩) hf h0
  have H : ∀ w, ∃ n Φ, w ∈ locPl G t → depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w (w.under (𝓞 D.host.F)) (flipAt W t i j w n Φ) (φ (w.under (𝓞 D.host.F))) := fun w => by
    by_cases hw : w ∈ locPl G t
    · obtain ⟨n, Φ, H⟩ := hP _ ((hti.2.2.1 _).2 ⟨w, hw, rfl⟩) w hw rfl
      exact ⟨n, Φ, fun _ => H⟩
    · exact ⟨0, 0, fun h => absurd h hw⟩
  choose n Φ H using H
  have hnat : ∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w) := fun w hw => ⟨(H w hw).1, (H w hw).2.1⟩
  obtain ⟨τ, τ', hF, -⟩ := (LocTensor.local_tensors hL B ρ t i j).2.2.2 (fun w hw hmem => hst.2 w hw (by
    have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
    rw [e]; exact Ideal.mul_mem_left _ _ hmem)) n Φ hnat
  obtain ⟨f₀, h1, h2, h3⟩ := GlobalTheory.T.exists_gaussianDatum_flippedFiniteTensor_bigRoute hL W B ρ t i j M hst e Bs Γ X om om' h hT hti n Φ τ τ' hnat hF φ hφ
    fun w hw => (H w hw).2.2
  obtain ⟨a, ha⟩ := GlobalTheory.T.realPolynomialVector_reached_by_realDatum hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f₀ h1 h2 h3 f hf
  obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hF, rfl, rfl⟩
  obtain ⟨ξ, hξ, hker⟩ := GlobalTheory.T.big_route_kernel_eq_const_mul_theta hL W B ρ t i j M _ _ hΘ e Bs Γ X om om' h hT _ ha g.1 g.2
  refine ⟨M, hM, a, τ, τ', n, Φ, hnat, hF, g.1, g.2, ?_⟩
  have hfd := (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  simp only [hker]
  rw [integral_const_mul, GlobalTheory.T.setIntegral_conjugate_scaled_unitaryGroup_eq _ 1 one_ne_zero h.JW _ _ hfd.1 hfd.2 Γ.M.dom (h.μW ▸ hT.geo.hM.dom)
    (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om _ x _) fun γ hγ x => ?_, ← h.μW]
  · exact mul_ne_zero hξ hne
  · have e3 : ((γ * x, blkU _ _ e h.JWW (g.1, g.2)) : UB Γ.V.J × UB Γ.W.J) = (γ, 1) * (x, blkU _ _ e h.JWW (g.1, g.2)) := by
      simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta]
    rw [e3, map_mul, Module.End.mul_apply,
      GlobalTheory.T.theta_distribution_rational_points_invariant_triple Bs Γ X om om' hT γ hγ 1 (one_mem _) _ (hT.weil.isUSplitting.pres _ _ ha.1)]

open Formalism.IndefR GlobalTheory.RowTest GlobalTheory.RowClaim

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound :=
  ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and GlobalTheory.PlacesPrime.places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

end GlobalTheory.BigNZ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmRec.CutSec

section General

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

theorem dim_closure_of_coheight_field {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (t : X ⟶ Spec (.of K))
    [LocallyOfFiniteType t] {n : ℕ} (hX : topologicalKrullDim X = (n + 1 : ℕ)) {w : X} (hw : Order.coheight w = 1) :
    topologicalKrullDim (closure ({w} : Set X)) = n := by
  have hgen : genericPoint X ∉ closure ({w} : Set X) := by
    intro h
    have e : w = genericPoint X :=
      ((genericPoint_specializes w).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
    rw [e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)] at hw
    exact zero_ne_one hw
  have hX1 : topologicalKrullDim (Set.univ : Set X) = (n + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX
  have hup : topologicalKrullDim (closure ({w} : Set X)) + 1 ≤ (n + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x _ => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩
  refine le_antisymm (GlobalTheory.PullVanish.withBot_le_of_add_one_le hup) ?_
  obtain ⟨A, _, _, _, _, _, j, _, ⟨a, ha⟩, -, hA⟩ := exists_affine_chart_trdeg_eq t w
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast K (A := A)
  have hdimX : topologicalKrullDim X ≤ (d : ℕ) := by
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
    refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
    exact ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).trans
      (ringKrullDim_eq_of_trdeg_eq K B (hB.trans (hA.symm.trans hd)))).le
  have hh : a.asIdeal.height = 1 := by
    rw [← hw, ← ha, coheight_apply_of_isOpenImmersion]
    exact idealHeight_eq_coheight (CommRingCat.of A) a
  have : a.asIdeal.IsPrime := a.isPrime
  have hF := height_add_ringKrullDim_quotient_of_finiteType K a.asIdeal
  rw [hh, ringKrullDim_eq_of_trdeg_eq K A hd] at hF
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({w} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  refine le_trans ?_ hlow
  rw [hX, ← hF] at hdimX
  generalize ringKrullDim (A ⧸ a.asIdeal) = u at hdimX
  induction u using WithBot.recBotCoe with
  | bot => simp at hdimX
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe u =>
      have : n + 1 ≤ 1 + u := by exact_mod_cast hdimX
      exact_mod_cast (by omega : n ≤ u)

theorem dim_closure_of_coheight {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] {n : ℕ} (hZ : topologicalKrullDim Z = (n + 1 : ℕ)) {w : Z}
    (hw : Order.coheight w = 1) : topologicalKrullDim (closure ({w} : Set Z)) = n := by
  obtain ⟨l, hl⟩ := CharP.exists Γ(Z, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Z, ⊤) l with hp | rfl
  · have : Fact l.Prime := ⟨hp⟩
    let := ZMod.algebra Γ(Z, ⊤) l
    obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hjN ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    have e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : LocallyOfFiniteType (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := e ▸ inferInstance
    have : LocallyOfFiniteType (strHom (ZMod l) (X := Z)) := locallyOfFiniteType_of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact dim_closure_of_coheight_field (strHom (ZMod l) Z) hZ hw
  · have := CharP.charP_to_charZero Γ(Z, ⊤)
    have h := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one k Z (i ≫ p) n (hX.of_isClosedImmersion i this hZ) _
      (redι (clo w)) (by rw [GlobalTheory.PullVanish.redι_genericPoint]; exact hw)
    exact (topologicalKrullDim_eq_of_isEmbedding (redι (clo w)).isClosedEmbedding.isEmbedding
      (range_redι _)).trans h

end General

section Cut

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

end Cut

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VdmRec

end GlobalTheory.VdmRec.CutSec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TvELeft
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
namespace GlobalTheory.VertCoeffRing
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def tvE (u : TanM (𝟙 (Sp R)) G) : epsR R ⟶ G := Over.homMk (tv u).left (by
  have := Over.w (tv u)
  simpa using this)

theorem tvE_left (u : TanM (𝟙 (Sp R)) G) : (tvE u).left = (tv u).left := rfl

end GlobalTheory.VertCoeffRing
end
end
