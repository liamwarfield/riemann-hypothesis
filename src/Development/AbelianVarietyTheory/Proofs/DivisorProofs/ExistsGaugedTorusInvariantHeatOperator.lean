module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresBasicOpen
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

namespace GlobalTheory.Heat.WtPres

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem isWt_div {α : Q.X} {V : Y.H.left.Opens} {f u u' : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hu : IsWt Y α V u)
    (h : u * u' = 1) : IsWt Y 0 V (f * u') := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have e : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V → valR b V u * valR b V u' = 1 := fun b hb => by
    rw [← WtAlg.valR_mul'' _ _ hb, h, WtAlg.valR_eq' _ _ hb, map_one, map_one]
  have e₁ := e a hV
  have e₂ := e a' hV'
  rw [hu S φ x x' c a a' ha ha' hV hV' hq hc] at e₂
  rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]
  linear_combination valR a V f * valR a V u' * e₂ - c α * valR a V f * valR a' V u' * e₁

end GlobalTheory.Heat.WtPres
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatGaugeCoverOpenLeHeatOperatorOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT pbT)
open GlobalTheory.LogKS (IsField)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m : G.left ⟶ X) {m₁ : G.left ⟶ X} {L : LB X} {dd : Fin n → Fld G.left} {D : R → R} (h₁ : Heat G m₁ L dd D)

def W (p : h₁.J × (Fin 2 → L.ι)) : G.left.Opens := h₁.W p.1 ⊓ LB.wchart L ![m, m₁] p.2

theorem heatGaugeCoverOpen_le_heatOperatorOpen (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ h₁.W p.1 := inf_le_left

theorem W_le_wchart (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ LB.wchart L ![m, m₁] p.2 := inf_le_right

theorem W_le_m (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m ⁻¹ᵁ L.U (p.2 0) :=
  (W_le_wchart m h₁ p).trans (LB.wchart_le L ![m, m₁] p.2 0)

theorem W_le_m₁ (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m₁ ⁻¹ᵁ (L.U (p.2 1) ⊓ L.U (h₁.j p.1)) :=
  fun _ hy => ⟨LB.wchart_le L ![m, m₁] p.2 1 hy.2, h₁.le p.1 hy.1⟩

variable (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

def gU (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p)ˣ :=
  res (W_le_wchart m h₁ p) (e.s p.2) * res (W_le_m₁ m h₁ p) (pullU m₁ _ (L.g (p.2 1) (h₁.j p.1)))

def gL (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  dd a (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gE (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  h₁.d p.1 (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gY (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e b p

def gD (p : h₁.J × (Fin 2 → L.ι)) : Fld G.left :=
  fun O f => h₁.d p.1 O f + ∑ a, rsT (gY m h₁ e a p) O * dd a O f

def gP (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p p.1) (W m h₁ p) - gE m h₁ e p -
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e a p * gL m h₁ e b p

def gP' (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p' p.1) (W m h₁ p) +
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * dd a (W m h₁ p) (gL m h₁ e b p) -
    ∑ a, constFn G.hom (W m h₁ p) (h₁.u a) * gL m h₁ e a p

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : Fld Z} (h : IsField W₀ d) (hle : W₁ ≤ W₀) :
    IsField W₁ d :=
  ⟨fun W hW => h.1 W (hW.trans hle), fun W hW => h.2.1 W (hW.trans hle),
    fun W W' hWW' hW => h.2.2 W W' hWW' (hW.trans hle)⟩


open GlobalTheory.KS in
theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (dd : Fin n → Fld G.left) (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R)
    (d : Fld G.left) {W₀ : G.left.Opens} (p p' : Γ(G.left, W₀)) (k : ℕ) {O O' : G.left.Opens}
    (hd : IsField O d) (hO : O ≤ W₀) (h : O' ≤ O) (f : Γ(G.left, O)) :
    rsT (op G dd Θ u d p p' k O f) O' = op G dd Θ u d p p' k O' (rsT f O') := by
  have hd' : ∀ g, resG G.left h (d O g) = d O' (resG G.left h g) :=
    fun g => (hd.2.2 O O' h le_rfl g).symm
  have hdd' : ∀ a g, resG G.left h (dd a O g) = dd a O' (resG G.left h g) :=
    fun a g => ((hdd a).2.2 O O' h le_top g).symm
  have hc : ∀ r, resG G.left h (constFn G.hom O r) = constFn G.hom O' r :=
    fun r => (rsT_of_le h _).symm.trans (rsT_constFn G.hom h r)
  have hp : ∀ q : Γ(G.left, W₀), resG G.left h (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h, rsT_rsT hO h]
  rw [rsT_of_le h, rsT_of_le h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [op, map_add (f := _), map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem trans_factor {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : GlobalTheory.RayEv.Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) :
    ∃ τ : Q.P.A.left ⟶ Q.P.A.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left = Y.q.left ≫ τ := by
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  refine ⟨(𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)).left, ?_⟩
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc Y.q (toUnit _),
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg (fun f => f.left) e

end GlobalTheory.Heat.Gauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedLocalHeatOperatorPowerMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedLocalHeatOperatorPowerMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

open GlobalTheory.KS (rsT_mul rsT_one rsT_sum rsT_sub rsT_add rsT_constFn rsT_rsT)
open GlobalTheory.HeatGlue (IsDer isDer_of_isField field_rsT ringOp_conj)

theorem op_gauged : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), (∀ a, IsField ⊤ (dd a)) → ∀ (c : R), 2 * c = 1 → ∀ (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p → ∀ (f : Γ(G.left, O)), op G dd h₁.Θ h₁.u (GlobalTheory.Heat.Gauge.gD m h₁ e p) (GlobalTheory.Heat.Gauge.gP m h₁ e c p) (GlobalTheory.Heat.Gauge.gP' m h₁ e c p) k O (rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * f) = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hdd c hc p k O hO f
  have hW1 : W m h₁ p ≤ h₁.W p.1 := heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p
  have hdF : IsField (h₁.W p.1) (h₁.d p.1) := (h₁.lift p.1).1
  have hd : IsDer (h₁.d p.1 O) := isDer_of_isField hdF (hO.trans hW1)
  have hddO : ∀ a, IsDer (dd a O) := fun a => isDer_of_isField (hdd a) le_top
  have hg : rsT (gU m h₁ e p).val O * rsT (gU m h₁ e p)⁻¹.val O = 1 := by
    rw [← rsT_mul, Units.mul_inv, rsT_one hO]
  set g := rsT (gU m h₁ e p).val O with hgdef
  set gi := rsT (gU m h₁ e p)⁻¹.val O with hgidef
  have eL : ∀ a, rsT (gL m h₁ e a p) O = dd a O g * gi := fun a => by
    rw [gL, rsT_mul, field_rsT (hdd a) le_top hO]
  have eE : rsT (gE m h₁ e p) O = h₁.d p.1 O g * gi := by
    rw [gE, rsT_mul, field_rsT hdF hW1 hO]
  have eY : ∀ a, rsT (gY m h₁ e a p) O = ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi) := fun a => by
    simp only [gY, rsT_sum, rsT_mul, rsT_constFn G.hom hO, eL]
  have eP : rsT (gP m h₁ e c p) O = rsT (h₁.p p.1) O - h₁.d p.1 O g * gi -
      constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi) := by
    simp only [gP, rsT_sub, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eE, rsT_rsT hW1 hO]
  have eDL : ∀ a b, rsT (dd a (W m h₁ p) (gL m h₁ e b p)) O = dd a O (dd b O g * gi) := fun a b => by
    rw [← field_rsT (hdd a) le_top hO, eL]
  have eP' : rsT (gP' m h₁ e c p) O = rsT (h₁.p' p.1) O +
      constFn G.hom O c * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi) -
      ∑ a, constFn G.hom O (h₁.u a) * (dd a O g * gi) := by
    simp only [gP', rsT_sub, rsT_add, rsT_mul, rsT_sum, rsT_constFn G.hom hO, eL, eDL, rsT_rsT hW1 hO]
  have hcO : 2 * constFn G.hom O c = 1 := by
    have := congrArg (constFn G.hom O) (show c + c = 1 by linear_combination hc)
    simp only [constFn, map_add (f := _), map_one] at this ⊢
    linear_combination this
  have hs : ∀ a b, (h₁.Θ.map (constFn G.hom O)) a b = (h₁.Θ.map (constFn G.hom O)) b a := fun a b => by
    simp only [Matrix.map_apply]
    rw [show h₁.Θ a b = h₁.Θᵀ b a from rfl, h₁.symm]
  have key := ringOp_conj hd hddO hs (fun a => constFn G.hom O (h₁.u a)) (rsT (h₁.p p.1) O) (rsT (h₁.p' p.1) O) hg k f
  simp only [ringOp, Matrix.map_apply] at key
  have S1 : ∑ a, (∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi)) * dd a O (g ^ k * f) =
      g ^ k * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd b O g * gi) * dd a O f +
      (k : Γ(G.left, O)) * g ^ k * f * ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi) := by
    simp only [(hddO _).pow_mul hg, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [op, gD, eY, eP, eP']
  linear_combination key + 2 * (k : Γ(G.left, O)) * S1 -
    (k : Γ(G.left, O)) * g ^ k * f * ((k : Γ(G.left, O)) *
      (∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * (dd a O g * gi) * (dd b O g * gi)) -
      ∑ a, ∑ b, constFn G.hom O (h₁.Θ a b) * dd a O (dd b O g * gi)) * hcO

end GlobalTheory.Heat.Gauge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedLocalHeatOperatorPowerMulStatement
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
theorem _root_.GlobalTheory.T.gauged_local_heat_operator_power_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), (∀ a, IsField ⊤ (dd a)) → ∀ (c : R), 2 * c = 1 → ∀ (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p → ∀ (f : Γ(G.left, O)), op G dd h₁.Θ h₁.u (GlobalTheory.Heat.Gauge.gD m h₁ e p) (GlobalTheory.Heat.Gauge.gP m h₁ e c p) (GlobalTheory.Heat.Gauge.gP' m h₁ e c p) k O (rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * f) = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f := by
  first | exact @GlobalTheory.Heat.Gauge.op_gauged | exact GlobalTheory.Heat.Gauge.op_gauged | (intros; apply GlobalTheory.Heat.Gauge.op_gauged <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitHasGeneratorWeightOnPreimages
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitHasGeneratorWeightOnPreimages
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

namespace GlobalTheory.Heat.Gauge

theorem isWt_zero_pbT_factor {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {Z : Scheme.{0}} (m₁ : Y.H.left ⟶ Z) (τ : Q.P.A.left ⟶ Z)
    (hm : m₁ = Y.q.left ≫ τ) {U : Z.Opens} (s : Γ(Z, U)) {V : Y.H.left.Opens} (hV : V ≤ m₁ ⁻¹ᵁ U) :
    IsWt Y 0 V (pbT m₁ s V) := by
  intro S _ φ z z' c a a' ha ha' h1 h2 hq hc
  have e : a' ≫ m₁ = a ≫ m₁ := by
    subst ha ha' hm
    have := congrArg CommaMorphism.left hq
    simp only [Over.comp_left] at this
    rw [← Category.assoc, this, Category.assoc]
  rw [GlobalTheory.HeatGlue.valR_pbT a' m₁ hV h2, GlobalTheory.HeatGlue.valR_pbT a m₁ hV h1, e, GlobalTheory.Heat.WtAlg.c_zero z z' c hc,
    Units.val_one, _root_.one_mul]

end GlobalTheory.Heat.Gauge


open GlobalTheory.Heat.Gauge in
theorem GlobalTheory.Heat.Gauge.gU_isWt : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D) (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∀ (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ GlobalTheory.Heat.Gauge.W Y.q.left h₁ p → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (GlobalTheory.Heat.Gauge.gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) := by
  intro R _ _ Q O _ _ _ oa Y n dd D x h₁ e β hwe p V hV
  obtain ⟨τ, hτ⟩ := trans_factor Q oa Y x
  have hW := W_le_wchart Y.q.left h₁ p
  have hm := W_le_m₁ Y.q.left h₁ p
  have key : rsT (gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V) =
      pbT ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) (Q.P.L.g (p.2 1) (h₁.j p.1)).val (Y.q.left ⁻¹ᵁ V) *
        rsT (e.s p.2).val (Y.q.left ⁻¹ᵁ V) := by
    rw [gU, Units.val_mul, GlobalTheory.KS.AdjDlog.val_res_pullU]
    erw [GlobalTheory.KS.AdjDlog.val_res hW]
    rw [GlobalTheory.KS.rsT_mul,
      GlobalTheory.KS.rsT_rsT hW hV, GlobalTheory.KS.rsT_pbT _ hm hV]
    exact mul_comm _ _
  rw [key]
  exact GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul
    (isWt_zero_pbT_factor Y _ τ hτ _ (hV.trans hm))
    (hwe p.2 V (hV.trans hW))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitHasGeneratorWeightOnPreimagesStatement
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
theorem _root_.GlobalTheory.T.gauge_unit_has_generator_weight_on_preimages : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (dd : Fin n → Fld Y.H.left) (D : R → R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D) (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∀ (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ GlobalTheory.Heat.Gauge.W Y.q.left h₁ p → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (GlobalTheory.Heat.Gauge.gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.Heat.Gauge.gU_isWt | exact GlobalTheory.Heat.Gauge.gU_isWt | (intros; apply GlobalTheory.Heat.Gauge.gU_isWt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitsTransitionRelationOnOverlaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitsTransitionRelationOnOverlaps
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

namespace GlobalTheory.Heat.Gauge

theorem gU_transition : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (p p' : h₁.J × (Fin 2 → L.ι)) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p ⊓ GlobalTheory.Heat.Gauge.W m h₁ p' → pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p').val O = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hL he p p' O hO
  have hWp : O ≤ W m h₁ p := hO.trans inf_le_left
  have hWp' : O ≤ W m h₁ p' := hO.trans inf_le_right
  have gv : ∀ q, O ≤ W m h₁ q → rsT (gU m h₁ e q).val O =
      rsT (e.s q.2).val O * pbT m₁ (L.g (q.2 1) (h₁.j q.1)).val O := by
    intro q hq
    rw [gU, Units.val_mul, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.AdjDlog.val_res_pullU m₁ (W_le_m₁ m h₁ q),
      GlobalTheory.KS.rsT_pbT m₁ (W_le_m₁ m h₁ q) hq]
    have a : rsT (res (W_le_wchart m h₁ q) (e.s q.2)).val O = rsT (e.s q.2).val O :=
      (congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res (W_le_wchart m h₁ q) (e.s q.2))).trans
        (GlobalTheory.KS.rsT_rsT (W_le_wchart m h₁ q) hq _)
    exact congrArg (· * _) a
  have hj : O ≤ LB.wchart L ![m, m₁] p.2 ⊓ LB.wchart L ![m, m₁] p'.2 :=
    le_inf (hWp.trans (W_le_wchart m h₁ p)) (hWp'.trans (W_le_wchart m h₁ p'))
  have hj' : O ≤ (LB.LinComb L ![m, m₁] ![1, -1]).U p.2 ⊓ (LB.LinComb L ![m, m₁] ![1, -1]).U p'.2 := hj
  have g1 : rsT (e.s p.2).val O = (res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * rsT (e.s p'.2).val O := by
    have g0 := congrArg (fun u => (res hj' u).val) (he p.2 p'.2)
    simp only [map_mul, Units.val_mul, GlobalTheory.KS.AdjDlog.res_res'] at g0
    rw [GlobalTheory.KS.AdjDlog.val_res hj']
    simpa only [GlobalTheory.KS.AdjDlog.val_res] using g0
  have le : ∀ k : Fin 2, O ≤ (![m, m₁] k) ⁻¹ᵁ (L.U (p.2 k) ⊓ L.U (p'.2 k)) := fun k =>
    le_inf ((hj.trans inf_le_left).trans (LB.wchart_le L _ _ k)) ((hj.trans inf_le_right).trans (LB.wchart_le L _ _ k))
  have ec : res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2) =
      ∏ k, res (le k) (pullU _ _ (L.g (p.2 k) (p'.2 k))) ^ (![(1 : ℤ), -1] k) := by
    refine (map_prod (res hj') _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow (res hj') _ _).trans ?_)
    exact congrArg (fun u => u ^ (![(1 : ℤ), -1] k)) (GlobalTheory.KS.AdjDlog.res_res' _ hj' _)
  have v0 : (res (le 0) (pullU (![m, m₁] 0) _ (L.g (p.2 0) (p'.2 0)))).val = pbT m (L.g (p.2 0) (p'.2 0)).val O :=
    GlobalTheory.KS.AdjDlog.val_res_pullU _ (le 0) _
  have v1 : (res (le 1) (pullU (![m, m₁] 1) _ (L.g (p.2 1) (p'.2 1)))).val = pbT m₁ (L.g (p.2 1) (p'.2 1)).val O :=
    GlobalTheory.KS.AdjDlog.val_res_pullU _ (le 1) _
  have hv : (res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * pbT m₁ (L.g (p.2 1) (p'.2 1)).val O =
      pbT m (L.g (p.2 0) (p'.2 0)).val O := by
    rw [ec, Fin.prod_univ_two, ← v0, ← v1]
    rw [show (![(1 : ℤ), -1] 0) = 1 from rfl, show (![(1 : ℤ), -1] 1) = -1 from rfl, zpow_one, zpow_neg_one,
      ← Units.val_mul, inv_mul_cancel_right]
  have m1p := hWp.trans (W_le_m₁ m h₁ p)
  have m1p' := hWp'.trans (W_le_m₁ m h₁ p')
  have coc1 := GlobalTheory.Heat.Glue.pbT_cocycle hL m₁ (p.2 1) (h₁.j p.1) (h₁.j p'.1)
    (O := O) (fun y hy => ⟨⟨(m1p hy).1, (m1p hy).2⟩, (m1p' hy).2⟩)
  have coc2 := GlobalTheory.Heat.Glue.pbT_cocycle hL m₁ (p.2 1) (p'.2 1) (h₁.j p'.1)
    (O := O) (fun y hy => ⟨⟨(m1p hy).1, (m1p' hy).1⟩, (m1p' hy).2⟩)
  rw [gv p hWp, gv p' hWp']
  linear_combination -(rsT (e.s p'.2).val O * pbT m₁ (L.g (p'.2 1) (h₁.j p'.1)).val O) * hv +
    ((res hj' ((LB.LinComb L ![m, m₁] ![1, -1]).g p.2 p'.2)).val * rsT (e.s p'.2).val O) * coc2 -
    pbT m₁ (L.g (p.2 1) (h₁.j p'.1)).val O * g1 - rsT (e.s p.2).val O * coc1

end GlobalTheory.Heat.Gauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugeUnitsTransitionRelationOnOverlapsStatement
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
theorem _root_.GlobalTheory.T.gauge_units_transition_relation_on_overlaps : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (p p' : h₁.J × (Fin 2 → L.ι)) (O : G.left.Opens), O ≤ GlobalTheory.Heat.Gauge.W m h₁ p ⊓ GlobalTheory.Heat.Gauge.W m h₁ p' → pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p').val O = rsT (GlobalTheory.Heat.Gauge.gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O := by
  first | exact @GlobalTheory.Heat.Gauge.gU_transition | exact GlobalTheory.Heat.Gauge.gU_transition | (intros; apply GlobalTheory.Heat.Gauge.gU_transition <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedChartFunctionEqGaugePowerMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedChartFunctionEqGaugePowerMul
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

theorem chart_fn_mul_gen_pow : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (k : ℕ) (σ : SecM m₁ L k) (ρ : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → ∀ (p : h₁.J × (Fin 2 → L.ι)), rsT (ρ.f fun _ => p.2 0) (GlobalTheory.Heat.Gauge.W m h₁ p) = (GlobalTheory.Heat.Gauge.gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (GlobalTheory.Heat.Gauge.W m h₁ p) := by
  intro R _ G _ _ n X m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have le₀ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m) (fun _ => p.2 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => W_le_m m h₁ p hy
  have le₁ : W m h₁ p ≤ LB.wchart L (K := Fin 1) (fun _ => m₁) (fun _ => h₁.j p.1) :=
    fun y hy => Set.mem_iInter.2 fun _ => (W_le_m₁ m h₁ p hy).2
  refine fn_ext fun y hy => ?_
  choose J hJ using fun χ : G.left ⟶ X => exists_chart hL (χ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 G.left : G.left ⟶ G.left) y ∈ W m h₁ p := hy
  have e₀ : gs (𝟙 G.left) y _ (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => p.2 0) (fun _ => J (𝟙 G.left ≫ m))).val *
        sval ρ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₀ _)).trans ((gs_res (𝟙 G.left) y le₀ hy' _).trans
      (sec_trans ρ (𝟙 G.left) y (le₀ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₁ : gs (𝟙 G.left) y _ (rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p)) =
      (trF (fun _ : Fin 1 => m₁) (fun _ => (k : ℤ)) (𝟙 G.left) y (fun _ => h₁.j p.1) (fun _ => J (𝟙 G.left ≫ m₁))).val *
        sval σ (𝟙 G.left) y J :=
    (congrArg (gs (𝟙 G.left) y _) (GlobalTheory.KS.rsT_of_le le₁ _)).trans ((gs_res (𝟙 G.left) y le₁ hy' _).trans
      (sec_trans σ (𝟙 G.left) y (le₁ hy) (hJ'.mem _ (𝟙 G.left))))
  have e₂ : gm (𝟙 G.left) y _ (gU m h₁ e p) =
      (trF ![m, m₁] ![1, -1] (𝟙 G.left) y p.2 (fun a => J (𝟙 G.left ≫ ![m, m₁] a)) * val e (𝟙 G.left) y J) *
        gm (𝟙 G.left ≫ m₁) y _ (L.g (p.2 1) (h₁.j p.1)) :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 G.left) y (W_le_wchart m h₁ p) hy' _).trans
        (gen_trans he (𝟙 G.left) y (W_le_wchart m h₁ p hy) (hJ'.mem _ (𝟙 G.left))))
      ((gm_res (𝟙 G.left) y (W_le_m₁ m h₁ p) hy' _).trans (gm_pull (𝟙 G.left) m₁ y _ (W_le_m₁ m h₁ p hy) _)))
  have e₃ : gs (𝟙 G.left) y _ ((gU m h₁ e p).val ^ k) = (gm (𝟙 G.left) y _ (gU m h₁ e p) ^ k).val := by
    rw [← Units.val_pow_eq_pow_val, gs_unit _ _ _ hy', map_pow]
  have hc := gm_cocycle hL (𝟙 G.left ≫ m₁) y (W_le_m₁ m h₁ p hy).1 (W_le_m₁ m h₁ p hy).2 (hJ (𝟙 G.left ≫ m₁))
  rw [gs_mul _ _ _ hy', e₀, e₁, e₃, e₂, hρ _ _ y J hJ', ← _root_.mul_assoc, ← _root_.mul_assoc, mul_right_comm, ← Units.val_mul,
    ← Units.val_mul]
  congr 2
  simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_natCast,
    zpow_one, zpow_neg]
  rw [← mul_pow, ← mul_pow]
  congr 1
  rw [_root_.mul_assoc _ (gm _ _ _ (L.g (p.2 1) _)), hc]
  rw [mul_right_comm _ (val e _ y J)]
  exact congrArg (· * val e _ y J) (inv_mul_cancel_right _ _).symm

end GlobalTheory.Heat.Gauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaugedChartFunctionEqGaugePowerMulStatement
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
theorem _root_.GlobalTheory.T.gauged_chart_function_eq_gauge_power_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (X : Scheme.{0}) (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D) (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])), L.IsLB → e.IsGen → ∀ (k : ℕ) (σ : SecM m₁ L k) (ρ : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → ∀ (p : h₁.J × (Fin 2 → L.ι)), rsT (ρ.f fun _ => p.2 0) (GlobalTheory.Heat.Gauge.W m h₁ p) = (GlobalTheory.Heat.Gauge.gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (GlobalTheory.Heat.Gauge.W m h₁ p) := by
  first | exact @GlobalTheory.Heat.Gauge.chart_fn_mul_gen_pow | exact GlobalTheory.Heat.Gauge.chart_fn_mul_gen_pow | (intros; apply GlobalTheory.Heat.Gauge.chart_fn_mul_gen_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperator
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

open GlobalTheory.KS

theorem gauge_op {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hdd : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1)
    (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens) (hO : O ≤ W m h₁ p) (f : Γ(G.left, O)) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O (rsT (gU m h₁ e p).val O ^ k * f) =
      rsT (gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f :=
  GlobalTheory.T.gauged_local_heat_operator_power_mul _ G n X m m₁ L dd D h₁ e hdd c hc p k O hO f

theorem gauge_cocycle {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (p p' : h₁.J × (Fin 2 → L.ι))
    (O : G.left.Opens) (hO : O ≤ W m h₁ p ⊓ W m h₁ p') :
    pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (gU m h₁ e p').val O =
      rsT (gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O :=
  GlobalTheory.T.gauge_units_transition_relation_on_overlaps _ G n X m m₁ L dd D h₁ e hL he p p' O hO

theorem gauge_chart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (k : ℕ) (σ : SecM m₁ L k)
    (ρ : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ.f fun _ => p.2 0) (W m h₁ p) = (gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p) :=
  GlobalTheory.T.gauged_chart_function_eq_gauge_power_mul _ G n X m m₁ L dd D h₁ e hL he k σ ρ hρ p

theorem gauge_wt {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens) (hV : Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p) :
    IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) :=
  GlobalTheory.T.gauge_unit_has_generator_weight_on_preimages _ Q O oa Y n dd D x h₁ e β hwe p V hV

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
  (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

theorem gauge_cover (hL : L.IsLB) : ⨆ p, W m h₁ p = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  have hy : y ∈ ⨆ i, h₁.W i := by rw [h₁.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m y)
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m₁ y)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, ![a, b]), hi, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨ha, hb⟩)⟩

theorem gauge_lift (hF : ∀ a, IsField ⊤ (dd a)) (h0 : ∀ a O r, dd a O (constFn G.hom O r) = 0)
    (p : h₁.J × (Fin 2 → L.ι)) : IsLift G D (W m h₁ p) (gD m h₁ e p) := by
  have hd₁ := h₁.lift p.1
  refine ⟨GlobalTheory.Heat.Adjust.isField_add_comb (h₁.d p.1) dd (fun a => gY m h₁ e a p)
    (isField_mono hd₁.1 (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) hF, fun O' hO r => ?_⟩
  show h₁.d p.1 O' (constFn G.hom O' r) + ∑ a, rsT (gY m h₁ e a p) O' * dd a O' (constFn G.hom O' r) = _
  rw [hd₁.2 O' (hO.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) r]
  simp [h0]

theorem gauge_glue (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1) (k : ℕ)
    (p p' : h₁.J × (Fin 2 → L.ι)) (O' : G.left.Opens) (hO : O' ≤ W m h₁ p ⊓ W m h₁ p') (f : Γ(G.left, O')) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O' (pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f) =
      pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k *
        op G dd h₁.Θ h₁.u (gD m h₁ e p') (gP m h₁ e c p') (gP' m h₁ e c p') k O' f := by
  have hOp : O' ≤ W m h₁ p := hO.trans inf_le_left
  have hOp' : O' ≤ W m h₁ p' := hO.trans inf_le_right
  have hco := gauge_cocycle G m m₁ L dd D h₁ e hL he p p' O' hO
  have hA' : rsT (gU m h₁ e p').val O' * rsT (gU m h₁ e p')⁻¹.val O' = 1 := by
    rw [← GlobalTheory.KS.rsT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.KS.rsT_one hOp']
  have hk := congrArg (· ^ k) hco
  have hk' := congrArg (· ^ k) hA'
  simp only [one_pow, mul_pow] at hk hk'
  have e1 : pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f =
      rsT (gU m h₁ e p).val O' ^ k *
        (pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f)) := by
    linear_combination (-(pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f)) * hk' +
      (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) * hk
  have ef : f = rsT (gU m h₁ e p').val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) := by
    linear_combination (-f) * hk'
  rw [e1, gauge_op G m m₁ L dd D h₁ e hF c hc p k O' hOp,
    h₁.glue k p.1 p'.1 O' (le_inf (hOp.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) (hOp'.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p')))]
  conv_rhs => rw [ef, gauge_op G m m₁ L dd D h₁ e hF c hc p' k O' hOp']
  linear_combination (-(op G dd h₁.Θ h₁.u (h₁.d p'.1) (h₁.p p'.1) (h₁.p' p'.1) k O'
    (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f))) * hk

end General

theorem gauge_acts {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a))
    (c : R) (hc : 2 * c = 1) (k : ℕ) (σ σ' : SecM m₁ L k) (ρ ρ' : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val)
    (hA : h₁.Acts k σ σ') (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ'.f fun _ => p.2 0) (W m h₁ p) = op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k
      (W m h₁ p) (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) := by
  have c1 := gauge_chart G m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have c2 := gauge_chart G m m₁ L dd D h₁ e hL he k σ' ρ' hρ' p
  have hU : rsT (gU m h₁ e p).val (W m h₁ p) = (gU m h₁ e p).val := GlobalTheory.KS.rsT_self _
  rw [c1, c2, ← hU, gauge_op G m m₁ L dd D h₁ e hF c hc p k _ le_rfl, hU]
  congr 1
  have hWc : h₁.W p.1 ≤ (LB.LinComb L (K := Fin 1) (fun _ => m₁) fun _ => (k : ℤ)).U (fun _ => h₁.j p.1) :=
    GlobalTheory.Heat.Glue.le_wchart _ (h₁.le p.1)
  rw [← GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p) (σ'.f fun _ => h₁.j p.1), hA p.1,
    op_rsT G dd hF _ _ _ _ _ k (h₁.lift p.1).1 le_rfl (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p),
    GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)]

theorem gauge_basic {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left)
    (hinv : ∀ a, IsInv Y.H (v a) (dd a)) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (hB₁ : ∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f))
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (c : R) (p : h₁.J × (Fin 2 → Q.P.L.ι)) :
    (∃ V : Q.P.A.left.Opens, W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (gP Y.q.left h₁ e c p) ∧
      IsWt Y 0 _ (gP' Y.q.left h₁ e c p) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (gD Y.q.left h₁ e p _ f) := by
  obtain ⟨τ, hτ⟩ := trans_factor Q oa Y x
  obtain ⟨⟨V₁, hV₁⟩, hp₁, hp₁', hd₁⟩ := hB₁ p.1
  let Vp : Q.P.A.left.Opens := V₁ ⊓ (Q.P.L.U (p.2 0) ⊓ τ ⁻¹ᵁ Q.P.L.U (p.2 1))
  have hm₁ : ∀ y, ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y = τ (Y.q.left y) := fun y => by
    rw [hτ, Scheme.Hom.comp_apply]
  have hWp : W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ Vp := by
    refine TopologicalSpace.Opens.ext (Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
    · have h1 : y ∈ Y.q.left ⁻¹ᵁ V₁ := hV₁ ▸ hy.1
      have h2 := Set.mem_iInter.1 hy.2
      refine ⟨h1, h2 0, ?_⟩
      show τ (Y.q.left y) ∈ Q.P.L.U (p.2 1)
      rw [← hm₁]; exact h2 1
    · have h1 : y ∈ h₁.W p.1 := hV₁ ▸ hy.1
      refine ⟨h1, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨hy.2.1, ?_⟩)⟩
      show ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y ∈ Q.P.L.U (p.2 1)
      rw [hm₁]; exact hy.2.2
  have tr : ∀ (α : Q.X) (W₀ : Y.H.left.Opens), W₀ = Y.q.left ⁻¹ᵁ Vp → ∀ f : Γ(Y.H.left, W₀),
      IsWt Y α (Y.q.left ⁻¹ᵁ Vp) (rsT f (Y.q.left ⁻¹ᵁ Vp)) → IsWt Y α W₀ f := by
    rintro α W₀ rfl f h
    rwa [GlobalTheory.KS.rsT_self] at h
  have hU : IsWt Y β (W Y.q.left h₁ p) (gU Y.q.left h₁ e p).val :=
    tr β _ hWp _ (gauge_wt Q oa Y dd D x h₁ e β hwe p Vp hWp.ge)
  have hdW : ∀ α f, IsWt Y α (W Y.q.left h₁ p) f → IsWt Y α (W Y.q.left h₁ p) (h₁.d p.1 (W Y.q.left h₁ p) f) := by
    have hle : Y.q.left ⁻¹ᵁ Vp ≤ h₁.W p.1 := hWp ▸ heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p
    rw [hWp]
    exact fun α => hd₁ α Vp hle
  have hinvU : (gU Y.q.left h₁ e p).val * (gU Y.q.left h₁ e p)⁻¹.val = 1 := Units.mul_inv _
  have hL0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gL Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtPres.isWt_div (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) β _ _ hU) hU hinvU
  have hE0 : IsWt Y 0 (W Y.q.left h₁ p) (gE Y.q.left h₁ e p) :=
    GlobalTheory.Heat.WtPres.isWt_div (hdW β _ hU) hU hinvU
  have hY0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gY Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 b)
  refine ⟨⟨Vp, hWp⟩, ?_, ?_, fun α V hV f hf => ?_⟩
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_sub
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁) hE0) ?_
    refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
    exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
      GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)) (hL0 b)
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_add
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁') ?_) ?_
    · refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
      exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _)
          (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) 0 _ _ (hL0 b))
    · exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)
  · show IsWt Y α _ (h₁.d p.1 _ f + ∑ a, rsT (gY Y.q.left h₁ e a p) _ * dd a _ f)
    exact GlobalTheory.Heat.WtAlg.isWt_add (hd₁ α V (hV.trans (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p)) f hf)
      (GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul
        (GlobalTheory.Heat.Adjust.isWt_rsT Y hV (hY0 a)) (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) α _ _ hf))

theorem exists_gauge_heat : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D), (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) → ∀ (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h₁.Θ ∧ h'.u = h₁.u ∧ ∀ (k : ℕ) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k) (ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val) → h₁.Acts k σ σ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hinv D x h₁ hB₁ e β he hwe
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hF : ∀ a, IsField ⊤ (dd a) := fun a => (hinv a).1
  have hc : 2 * algebraMap ℚ R (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  refine ⟨⟨h₁.Θ, h₁.symm, h₁.u, h₁.J × (Fin 2 → Q.P.L.ι), W Y.q.left h₁, fun p => p.2 0,
    gD Y.q.left h₁ e, gP Y.q.left h₁ e (algebraMap ℚ R (1 / 2)), gP' Y.q.left h₁ e (algebraMap ℚ R (1 / 2)),
    gauge_cover Y.H _ _ Q.P.L dd _ h₁ hL, fun p => W_le_m Y.q.left h₁ p,
    gauge_lift Y.H _ _ Q.P.L dd _ h₁ e hF (fun a O' r => GlobalTheory.Heat.Adjust.inv_constFn Y.H (v a) (dd a) (hinv a) O' r),
    fun k p p' O' hO f => gauge_glue Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k p p' O' hO f⟩,
    gauge_basic Q oa Y v dd hinv _ x h₁ hB₁ e β hwe _, rfl, rfl, ?_⟩
  intro k σ σ' ρ ρ' hρ hρ' hA p
  exact gauge_acts Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k σ σ' ρ ρ' hρ hρ' hA p

end GlobalTheory.Heat.Gauge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperatorStatement
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
theorem _root_.GlobalTheory.T.exists_gauged_torusInvariant_heatOperator : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D), (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) → ∀ (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h₁.Θ ∧ h'.u = h₁.u ∧ ∀ (k : ℕ) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k) (ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val) → h₁.Acts k σ σ' → h'.Acts k ρ ρ' := by
  first | exact @GlobalTheory.Heat.Gauge.exists_gauge_heat | exact GlobalTheory.Heat.Gauge.exists_gauge_heat | (intros; apply GlobalTheory.Heat.Gauge.exists_gauge_heat <;> assumption)
end
