module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphism

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtRelVIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRos

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def PV (W : Matrix (Fin r) (Fin r) ℤ) (e : N'.X → Fin r → N.X) (χ' : N'.X) (vs : Fin r → N.Gt) : F :=
  ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
        N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F)

theorem gtRelV_iff (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) :
    GtRelV W φ e wv v' vs ↔ (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
      (v'.s χ' : F) * wv (N'.c χ') * wv v'.b = PV W e χ' vs * wv (N'.c χ' * v'.b) * wv 1 := Iff.rfl

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def tensJ (T : Tens D D' W) (ν : NumOf D F N) (y : Sp F ⟶ D'.P.A.left) :
    (LB.LinComb D.P.L (tensφ T.pr) (tensε W)).ι :=
  fun k => ν.J (y ≫ tensφ T.pr k)

def RosVT (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (f g : D'.P.A ⟶ D'.P.A) (ρ : N'.A → N'.A → F) :
    Prop :=
  ∃ u : LB.Gen (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) (rosatiφ D'.P.A f g) rosatiε), u.IsGen ∧
    LB.Gen.Corr (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ _ _
      (LB.pullGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ u (zero2 D'.P.A))
      (LB.oneGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W))) ∧
    ∀ b b', ρ b b' = vF u (lift (ν'.eA b) (ν'.eA b')).left (tensJ T ν)

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] [Module O D'.X] (o : D'.OAct O)
    (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (j : Fin r) :
    GlobalTheory.Mum.TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) j = ∏ k, GlobalTheory.Mum.TensTor.cmp T ν ν' b k ^ ρ x j k := by
  letI := D.P.isAb.comm
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := MonObj.comp_one _
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have e : ν'.eA (GlobalTheory.Relabel.actV ν' o.onB x b) ≫ T.pr j = P (∏ k, T.pr k ^ ρ x j k) := by
    rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x j]; rfl
  rw [GlobalTheory.Mum.TensTor.cmp, e, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  rfl

theorem c_actV {R : Type} [CommRing R] [IsDomain R] {D' : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N' : NumD F} (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O]
    [Module O D'.X] (o : D'.OAct O) (a : O) (χ : N'.X) :
    GlobalTheory.Relabel.actV ν' o.onB a (N'.c χ) = N'.c (ν'.eX.symm (a • ν'.eX χ)) := by
  apply ν'.eA.injective
  rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, ν'.c_eq, ν'.c_eq, AddEquiv.apply_symm_apply]
  show (toUnit _ ≫ D'.c _) ≫ _ = toUnit _ ≫ D'.c _
  rw [o.c_lin, Category.assoc]

end GlobalTheory.Mum.TensRos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.RosComp

section Alg

variable {O : Type} [CommRing O] {N : NumD O} {Γ Γ₀ Q : Type} [CommGroup Γ] [CommGroup Γ₀] [AddCommGroup Q]
  (ev : Γ →* N.A) (e₀ : Γ →* Γ₀) (ℓ : Γ → Γ → Q) (κ : Additive Oˣ →+ Q)

def PVu {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (χ : Fin r → N.X) (vs : Fin r → N.Gt) : Oˣ :=
  ∏ i, ∏ j, ((vs j).s (χ i) * (vs i).s (χ j) /
      (N.θ (N.c (χ j)) (vs j).b (N.c (χ i)) * N.θ (N.c (χ j)) (vs j).b (vs i).b *
        N.θ (N.c (χ i)) (vs i).b (N.c (χ j) * (vs j).b))) ^ W i j

def cHom (N : NumD O) : Multiplicative N.X →* N.A := MonoidHom.mk' (fun χ => N.c χ.toAdd) fun a b => N.c_add a.toAdd b.toAdd

variable (hs : ∀ a b, ℓ a b = ℓ b a)
  (hc : ∀ a a' b, e₀ b = 1 → ℓ (a * a') b = ℓ a b + ℓ a' b - κ (Additive.ofMul (N.θ (ev a) (ev a') (ev b))))

include hc in
theorem left_sum {r : ℕ} (x : Fin r → Γ) (χ : Fin r → N.X) (hx : ∀ k, ev (x k) = N.c (χ k)) (n : Fin r → ℤ)
    (b : Γ) (g : N.Gt) (hb : ev b = g.b) (h₀ : e₀ b = 1) :
    ℓ (∏ k, x k ^ n k) b - κ (Additive.ofMul (g.s (∑ k, n k • χ k))) =
      ∑ k, n k • (ℓ (x k) b - κ (Additive.ofMul (g.s (χ k)))) := by
  let S : Subgroup (Γ × Multiplicative N.X) :=
    MonoidHom.eqLocus (ev.comp (MonoidHom.fst _ _)) ((cHom N).comp (MonoidHom.snd _ _))
  let φ : S →* Multiplicative Q := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd (ℓ p.1.1 b - κ (Additive.ofMul (g.s p.1.2.toAdd)))) fun p p' => by
      have e : ev p.1.1 = N.c p.1.2.toAdd := p.2
      have e' : ev p'.1.1 = N.c p'.1.2.toAdd := p'.2
      have m := congrArg (fun u => κ (Additive.ofMul u)) (g.mult p.1.2.toAdd p'.1.2.toAdd)
      simp only [ofMul_mul, map_add (f := _)] at m
      rw [← ofAdd_add]
      congr 1
      show ℓ (p.1.1 * p'.1.1) b - κ (Additive.ofMul (g.s (p.1.2.toAdd + p'.1.2.toAdd))) = _
      rw [hc _ _ _ h₀, e, e', hb]
      linear_combination (norm := abel) -m
  let s : Fin r → S := fun k => ⟨(x k, Multiplicative.ofAdd (χ k)), hx k⟩
  have h := congrArg Multiplicative.toAdd (map_prod φ (fun k => s k ^ n k) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  have c₁ : (∏ k, s k ^ n k).1.1 = ∏ k, x k ^ n k := by
    simp [s, Prod.fst_prod]
  have c₂ : (∏ k, s k ^ n k).1.2.toAdd = ∑ k, n k • χ k := by
    simp [s, Prod.snd_prod, toAdd_prod]
  rw [← c₁, ← c₂]
  exact h

include hs hc in
theorem right_sum {r : ℕ} (y : Fin r → Γ) (g : Fin r → N.Gt) (hy : ∀ k, ev (y k) = (g k).b) (n : Fin r → ℤ)
    (a : Γ) (χ : N.X) (ha : ev a = N.c χ) (h₀ : e₀ a = 1) :
    ℓ a (∏ k, y k ^ n k) - κ (Additive.ofMul ((∏ k, g k ^ n k).s χ)) =
      ∑ k, n k • (ℓ a (y k) - κ (Additive.ofMul ((g k).s χ))) := by
  let S : Subgroup (Γ × N.Gt) :=
    MonoidHom.eqLocus (ev.comp (MonoidHom.fst _ _)) (N.projB.comp (MonoidHom.snd _ _))
  let φ : S →* Multiplicative Q := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd (ℓ a p.1.1 - κ (Additive.ofMul (p.1.2.s χ)))) fun p p' => by
      have e : ev p.1.1 = p.1.2.b := p.2
      have e' : ev p'.1.1 = p'.1.2.b := p'.2
      rw [← ofAdd_add]
      congr 1
      show ℓ a (p.1.1 * p'.1.1) - κ (Additive.ofMul ((p.1.2 * p'.1.2).s χ)) = _
      rw [hs, hc _ _ _ h₀, e, e', ha, NumD.Gt.mul_s, hs a, hs a, N.cub.s12 p.1.2.b, N.cub.s01 p.1.2.b]
      simp only [ofMul_mul, ofMul_div, map_add (f := _), map_sub]
      abel
  let s : Fin r → S := fun k => ⟨(y k, g k), hy k⟩
  have h := congrArg Multiplicative.toAdd (map_prod φ (fun k => s k ^ n k) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  have c₁ : (∏ k, s k ^ n k).1.1 = ∏ k, y k ^ n k := by
    simp [s, Prod.fst_prod]
  have c₂ : (∏ k, s k ^ n k).1.2 = ∏ k, g k ^ n k := by
    simp [s, Prod.snd_prod]
  rw [← c₁, ← c₂]
  exact h

include hs hc in
theorem quad_mul {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (a y : Fin r → Γ) (χ : Fin r → N.X) (g : Fin r → N.Gt)
    (ha : ∀ k, ev (a k) = N.c (χ k)) (hy : ∀ k, ev (y k) = (g k).b) (a₀ : ∀ k, e₀ (a k) = 1) (y₀ : ∀ k, e₀ (y k) = 1) :
    ∑ i, ∑ j, W i j • ℓ (a i * y i) (a j * y j) = ∑ i, ∑ j, W i j • ℓ (a i) (a j) + ∑ i, ∑ j, W i j • ℓ (y i) (y j) +
      ∑ i, ∑ j, W i j • ((ℓ (a i) (y j) - κ (Additive.ofMul ((g j).s (χ i)))) +
        (ℓ (a j) (y i) - κ (Additive.ofMul ((g i).s (χ j))))) + κ (Additive.ofMul (PVu W χ g)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PVu, ofMul_prod, map_sum, ofMul_zpow, map_zsmul, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [hc _ _ _ (by rw [map_mul, a₀, y₀, _root_.mul_one]), hs (a i), hs (y i), hc _ _ _ (a₀ i), hc _ _ _ (y₀ i), map_mul,
    ha, ha, hy, hy, hs (a j) (a i), hs (y j) (a i), hs (y j) (y i)]
  simp only [ofMul_mul, ofMul_div, map_add (f := _), map_sub]
  abel

include hs hc in
theorem total {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') (x y a b : Fin r → Γ) (χ χ₁ : Fin r → N.X)
    (g : Fin r → N.Gt) (hx : ∀ k, ev (x k) = N.c (χ k)) (hy : ∀ k, ev (y k) = (g k).b) (x₀ : ∀ k, e₀ (x k) = 1)
    (y₀ : ∀ k, e₀ (y k) = 1) (ha : ∀ i, a i = ∏ k, x k ^ A i k) (hb : ∀ i, b i = ∏ k, y k ^ A' i k)
    (h₁ : ∀ i, χ₁ i = ∑ k, A i k • χ k) :
    ∑ i, ∑ j, W i j • ℓ (a i * y i) (a j * y j) - ∑ i, ∑ j, W i j • ℓ (a i) (a j) - ∑ i, ∑ j, W i j • ℓ (y i) (y j) -
      ∑ i, ∑ j, W i j • ℓ (x i * b i) (x j * b j) + ∑ i, ∑ j, W i j • ℓ (x i) (x j) + ∑ i, ∑ j, W i j • ℓ (b i) (b j) =
      κ (Additive.ofMul (PVu W χ₁ g)) - κ (Additive.ofMul (PVu W χ (fun i => ∏ k, g k ^ A' i k))) := by
  have ea : ∀ i, ev (a i) = N.c (χ₁ i) := fun i => by
    have : N.c (χ₁ i) = cHom N (∏ k, Multiplicative.ofAdd (χ k) ^ A i k) := by
      rw [h₁]; show _ = N.c _; simp [toAdd_prod]
    rw [this, ha, map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hx]; rfl
  have eb : ∀ i, ev (b i) = (∏ k, g k ^ A' i k).b := fun i => by
    rw [← N.projB_apply, hb, map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hy]; rfl
  have a₀ : ∀ i, e₀ (a i) = 1 := fun i => by simp [ha, map_prod, x₀]
  have b₀ : ∀ i, e₀ (b i) = 1 := fun i => by simp [hb, map_prod, y₀]
  rw [quad_mul ev e₀ ℓ κ hs hc W a y χ₁ g ea hy a₀ y₀, quad_mul ev e₀ ℓ κ hs hc W x b χ _ hx eb x₀ b₀]
  have e₁ : ∀ i j, ℓ (a i) (y j) - κ (Additive.ofMul ((g j).s (χ₁ i))) =
      ∑ k, A i k • (ℓ (x k) (y j) - κ (Additive.ofMul ((g j).s (χ k)))) := fun i j => by
    rw [ha, h₁, left_sum ev e₀ ℓ κ hc x χ hx _ _ _ (hy j) (y₀ j)]
  have e₂ : ∀ i j, ℓ (x i) (b j) - κ (Additive.ofMul ((∏ k, g k ^ A' j k).s (χ i))) =
      ∑ k, A' j k • (ℓ (x i) (y k) - κ (Additive.ofMul ((g k).s (χ i)))) := fun i j => by
    rw [hb, right_sum ev e₀ ℓ κ hs hc y g hy _ _ _ (hx i) (x₀ i)]
  have hC := GlobalTheory.TensRosati.key_sum (fun k m => ℓ (x k) (y m) - κ (Additive.ofMul ((g m).s (χ k)))) W A A' h
  simp only [e₁, e₂]
  rw [hC]
  abel

end Alg

end GlobalTheory.Mum.RosComp

namespace GlobalTheory.Mum.RosComp

open GlobalTheory.TensRosati

section Flat

variable {X X' Y Z : Scheme.{0}} {M : LB X} {K₁ : Type} [Fintype K₁] {pr : K₁ → (X' ⟶ X)} {e : K₁ → ℤ}
  {K : Type} [Fintype K]

theorem le_flat (φ' : K → (Y ⟶ X')) (j : K × K₁ → M.ι) :
    LB.wchart M (fun p : K × K₁ => φ' p.1 ≫ pr p.2) j ≤ LB.wchart (LB.LinComb M pr e) φ' (fun a k => j (a, k)) :=
  fun _ hy => Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (a, k)

def flat (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb (LB.LinComb M pr e) φ' ε)) :
    LB.Gen (LB.LinComb M (fun p : K × K₁ => φ' p.1 ≫ pr p.2) (fun p => ε p.1 * e p.2)) :=
  ⟨fun j : K × K₁ → M.ι => res (le_flat φ' j) (t.s (fun a k => j (a, k)))⟩

theorem flat_isGen (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb (LB.LinComb M pr e) φ' ε))
    (ht : t.IsGen) : (flat φ' ε t).IsGen := by
  refine isGen_of_gm _ fun y j j' h h' => ?_
  refine (gm_res (𝟙 Y) y _ h _).trans ((gen_trans ht (𝟙 Y) y (le_flat φ' j h) (le_flat φ' j' h')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y _ h' _).symm))
  unfold trF
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  refine (congrArg (· ^ ε a) (gm_linComb M pr e (𝟙 Y ≫ φ' a) y (fun k => j (a, k)) (fun k => j' (a, k))
    (Set.mem_iInter.1 (le_flat (e := e) φ' j h) a) (Set.mem_iInter.1 (le_flat (e := e) φ' j' h') a))).trans ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [← zpow_mul, mul_comm (e i), Category.assoc]

theorem good_comb {z : Z} {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    Good (LB.LinComb M pr e) z (fun ψ k => J (ψ ≫ pr k)) := fun ψ => hJ.mem pr ψ

theorem val_flat (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb (LB.LinComb M pr e) φ' ε)) (r : Z ⟶ Y)
    {z : Z} {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    val (flat φ' ε t) r z J = val t r z (fun ψ k => J (ψ ≫ pr k)) := by
  refine Eq.trans ?_ (val_of t r z (fun ψ k => J (ψ ≫ pr k)) (fun a k => J (r ≫ φ' a ≫ pr k))
    (fun a => funext fun k => congrArg J (Category.assoc _ _ _))).symm
  exact gm_res r z _ (hJ.mem (fun p : K × K₁ => φ' p.1 ≫ pr p.2) r) _

end Flat

section Gens

variable {X Y Z S₀ : Scheme.{0}}

def normGens (L : LB X) (e : S₀ ⟶ Y) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    AddSubgroup (FreeAbelianGroup (Y ⟶ X) × Additive (Z.presheaf.stalk z)ˣ) where
  carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ s.1 = ∑ k, ε k • FreeAbelianGroup.of (φ k) ∧ (∀ y I, Good L y I → val t e y I = 1) ∧
      val t r z J = s.2.toMul}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    (Fintype.sum_empty _).symm, fun _ _ _ => val_one _, val_one _⟩
  add_mem' := by
    rintro s s' ⟨K, _, φ, ε, t, ht, hs, h₀, hv⟩ ⟨K', _, φ', ε', t', ht', hs', h₀', hv'⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', ?_,
      fun y I hI => by rw [val_mul hI, h₀ y I hI, h₀' y I hI, _root_.mul_one], by rw [val_mul hJ, hv, hv']; rfl⟩
    rw [Fintype.sum_sum_type, Prod.fst_add, hs, hs']
    rfl
  neg_mem' := by
    rintro s ⟨K, _, φ, ε, t, ht, hs, h₀, hv⟩
    refine ⟨K, inferInstance, φ, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, ?_,
      fun y I hI => by rw [val_inv, h₀ y I hI, inv_one], by rw [val_inv, hv]; rfl⟩
    simp only [neg_smul, Finset.sum_neg_distrib, Prod.fst_neg, hs]

end Gens

section Cube

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem cube_mem_norm (L : RigLB G) (c : CubicalStr G L) {T T₀ T' : Over S} (e : T₀ ⟶ T) (r : T' ⟶ T) {z : T'.left}
    {J} (hJ : Good L.L z J) (a a' b : T ⟶ G) (hb : e ≫ b = 1) :
    (lam (a * a') b - lam a b - lam a' b, Additive.ofMul (cubV c z J (r ≫ a) (r ≫ a') (r ≫ b))) ∈
      normGens L.L e.left r.left hJ := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift a' b)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, ?_, fun y I hI => ?_, val_cub c r hJ a a' b⟩
  · have := prod_cub a a' b (U := Multiplicative (FreeAbelianGroup (T.left ⟶ G.left)))
      (fun m => Multiplicative.ofAdd (FreeAbelianGroup.of m))
    have e := congrArg Multiplicative.toAdd this
    simp only [toAdd_prod, toAdd_zpow, toAdd_mul, toAdd_inv, toAdd_ofAdd] at e
    rw [e, lam, lam, lam]
    abel
  · refine (val_cub c e hI a a' b).trans ?_
    rw [hb]
    exact (isCub_cubV c hI).face₃ _ _

end Cube

section Total

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
  {r : ℕ} (pr : Fin r → (A' ⟶ A))

theorem ros_flat (W : Matrix (Fin r) (Fin r) ℤ) (f g : A' ⟶ A') :
    ∑ p : Fin 6 × ((Fin r × Fin r) × Fin 4), (rosatiε p.1 * tensε W p.2) •
      FreeAbelianGroup.of (rosatiφ A' f g p.1 ≫ tensφ pr p.2) =
      qf pr W ((fst A' A' ≫ f) * snd A' A') - qf pr W (fst A' A' ≫ f) - qf pr W (snd A' A') -
        qf pr W (fst A' A' * (snd A' A' ≫ g)) + qf pr W (fst A' A') + qf pr W (snd A' A' ≫ g) := by
  rw [Fintype.sum_prod_type]
  simp only [mul_smul, ← Finset.smul_sum, Fin.sum_univ_six]
  rw [← flat_eq, ← flat_eq, ← flat_eq, ← flat_eq, ← flat_eq, ← flat_eq]
  rw [show rosatiε 0 = 1 from rfl, show rosatiε 1 = -1 from rfl,
    show rosatiε 2 = -1 from rfl, show rosatiε 3 = -1 from rfl, show rosatiε 4 = 1 from rfl,
    show rosatiε 5 = 1 from rfl]
  simp only [one_smul, neg_smul, sub_eq_add_neg]
  rfl

end Total

end GlobalTheory.Mum.RosComp

namespace GlobalTheory.Mum.RosComp

open GlobalTheory.TensRosati

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem ros_value (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') (f g : D'.P.A ⟶ D'.P.A)
    (hf : letI := D.P.isAb.comm; ∀ i, f ≫ T.pr i = ∏ j, T.pr j ^ A i j)
    (hg : letI := D.P.isAb.comm; ∀ i, g ≫ T.pr i = ∏ j, T.pr j ^ A' i j)
    (ρ : N'.A → N'.A → F) (hρ : TensRos.RosVT T ν ν' f g ρ) (a b : N'.A) (χ χ₁ : Fin r → N.X) (gs : Fin r → N.Gt)
    (ha : ∀ j, TensTor.cmp T ν ν' a j = N.c (χ j)) (hb : ∀ j, TensTor.cmp T ν ν' b j = (gs j).b)
    (h₁ : ∀ i, χ₁ i = ∑ k, A i k • χ k) :
    ρ a b * (PVu W χ₁ gs : Fˣ) = (PVu W χ (fun i => ∏ k, gs k ^ A' i k) : Fˣ) := by
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  obtain ⟨u, hu, u₀, hv⟩ := hρ
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  let τ : Fˣ →* ((Sp F).presheaf.stalk z)ˣ := Units.map (toStk z).toMonoidHom
  have tθ : ∀ a b c, τ (N.θ a b c) = cubV D.cub (T := TF (R := R) F) z ν.J (ν.eA a) (ν.eA b) (ν.eA c) := fun a b c =>
    Units.ext ((Units.coe_map _ _).trans ((congrArg (toStk z) (ν.θ_eq a b c)).trans (toStk_valF _ _ z (hJ.mem _ _) _)))
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A ⊗ D'.P.A := lift η[D'.P.A] η[D'.P.A]
  let p : TF (R := R) F ⟶ D'.P.A ⊗ D'.P.A := lift (ν'.eA a) (ν'.eA b)
  let H := normGens D.P.L (Z := Sp F) e.left p.left hJ
  let ev : (D'.P.A ⊗ D'.P.A ⟶ D.P.A) →* N.A := ν.eA.symm.toMonoidHom.comp (preHom p)
  let ℓ : (D'.P.A ⊗ D'.P.A ⟶ D.P.A) → (D'.P.A ⊗ D'.P.A ⟶ D.P.A) → _ ⧸ H := fun x y =>
    (QuotientAddGroup.mk' H).comp (AddMonoidHom.inl _ _) (lam x y)
  let κ : Additive Fˣ →+ _ ⧸ H := ((QuotientAddGroup.mk' H).comp (AddMonoidHom.inr _ _)).comp τ.toAdditive
  have hs : ∀ x y, ℓ x y = ℓ y x := fun x y => by simp only [ℓ, lam_comm x y]
  have hc : ∀ x x' y, preHom e y = 1 →
      ℓ (x * x') y = ℓ x y + ℓ x' y - κ (Additive.ofMul (N.θ (ev x) (ev x') (ev y))) := fun x x' y hy => by
    have m := (QuotientAddGroup.eq_zero_iff _).2
      (cube_mem_norm ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub e p hJ x x' y hy)
    have t : τ (N.θ (ev x) (ev x') (ev y)) = cubV D.cub (T := TF (R := R) F) z ν.J (p ≫ x) (p ≫ x') (p ≫ y) := by
      rw [tθ]
      simp only [ev, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      rfl
    have m' : ℓ (x * x') y - ℓ x y - ℓ x' y + κ (Additive.ofMul (N.θ (ev x) (ev x') (ev y))) = 0 := by
      refine Eq.trans ?_ m
      simp only [ℓ, ← map_sub]
      refine (map_add (QuotientAddGroup.mk' H) _ _).symm.trans (congrArg _ (Prod.ext (add_zero _) ?_))
      exact (zero_add _).trans (congrArg Additive.ofMul t)
    linear_combination (norm := abel) m'
  have one : ∀ k, η[D'.P.A] ≫ T.pr k = 1 := fun k => by
    have := T.pr_hom k
    simp [Hom.one_def]
  have tot := total ev (preHom e) ℓ κ hs hc W A A' h (fun k => fst _ _ ≫ T.pr k) (fun k => snd _ _ ≫ T.pr k)
    (fun k => (fst _ _ ≫ f) ≫ T.pr k) (fun k => (snd _ _ ≫ g) ≫ T.pr k) χ χ₁ gs
    (fun k => (congrArg ν.eA.symm (lift_fst_assoc _ _ _)).trans (ha k))
    (fun k => (congrArg ν.eA.symm (lift_snd_assoc _ _ _)).trans (hb k))
    (fun k => (lift_fst_assoc _ _ _).trans (one k)) (fun k => (lift_snd_assoc _ _ _).trans (one k))
    (fun i => by
      rw [Category.assoc, hf, GlobalTheory.MatrixAction.comp_finsetProd]
      exact Finset.prod_congr rfl fun k _ => by rw [GrpObj.comp_zpow])
    (fun i => by
      rw [Category.assoc, hg, GlobalTheory.MatrixAction.comp_finsetProd]
      exact Finset.prod_congr rfl fun k _ => by rw [GrpObj.comp_zpow]) h₁
  have hm : ∀ (x y : D'.P.A ⊗ D'.P.A ⟶ D'.P.A) (i : Fin r), (x * y) ≫ T.pr i = (x ≫ T.pr i) * (y ≫ T.pr i) :=
    fun x y i => by
      have := T.pr_hom i
      exact MonObj.mul_comp x y (T.pr i)
  have mq : ∀ x : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, (QuotientAddGroup.mk' H).comp (AddMonoidHom.inl _ _) (qf T.pr W x) =
      ∑ i, ∑ j, W i j • ℓ (x ≫ T.pr i) (x ≫ T.pr j) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [qf, map_sum, map_zsmul, ℓ]
  have mem : (∑ q : Fin 6 × ((Fin r × Fin r) × Fin 4), (rosatiε q.1 * tensε W q.2) •
      FreeAbelianGroup.of (rosatiφ D'.P.A f g q.1 ≫ tensφ T.pr q.2),
      Additive.ofMul (τ (PVu W χ (fun i => ∏ k, gs k ^ A' i k) / PVu W χ₁ gs))) ∈ H := by
    refine (QuotientAddGroup.eq_zero_iff _).1 ?_
    have s : ∀ (x) (v : Fˣ), (QuotientAddGroup.mk (x, Additive.ofMul (τ v)) : _ ⧸ H) =
        (QuotientAddGroup.mk' H).comp (AddMonoidHom.inl _ _) x + κ (Additive.ofMul v) := fun x v =>
      (congrArg _ (Prod.ext (add_zero _).symm (zero_add _).symm)).trans (map_add (QuotientAddGroup.mk' H) _ _)
    rw [s, ros_flat]
    simp only [map_add (f := _), map_sub, mq, hm, ofMul_div]
    rw [tot]
    abel
  obtain ⟨K, _, φ, ε, t, ht, hF, t₀, tv⟩ := mem
  have he : e.left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (formEq_of_eq hF.symm) _ e.left he
    (surj_comp (surj_snd GlobalTheory.globalFns_holds D'.P.isAb _) (GlobalTheory.globalFns_holds _ _ D'.P.isAb).2)
    (flat_isGen _ _ u hu) ht (fun y I hI => by
      have c := val_corr (good_comb (pr := tensφ T.pr) (e := tensε W) hI) u₀ (𝟙 _)
      have c' := (val_pull (good_comb (pr := tensφ T.pr) (e := tensε W) hI) u (zero2 D'.P.A) (𝟙 _)).symm.trans
        (c.trans (val_one _))
      rw [Category.id_comp] at c'
      exact ((val_flat _ _ u _ hI).trans c').trans (t₀ y I hI).symm) (Sp F) p.left z ν.J hJ
  have k2 : toStk z (ρ a b) = (τ (PVu W χ (fun i => ∏ k, gs k ^ A' i k) / PVu W χ₁ gs)).val := by
    rw [hv]
    refine (toStk_valF _ _ z ((good_comb (pr := tensφ T.pr) (e := tensε W) hJ).mem _ _) _).trans ?_
    exact congrArg Units.val ((val_flat _ _ u p.left hJ).symm.trans (key.trans tv))
  have k3 : ρ a b = (PVu W χ (fun i => ∏ k, gs k ^ A' i k) / PVu W χ₁ gs : Fˣ) :=
    (toStk z).injective (k2.trans (Units.coe_map _ _))
  rw [k3, ← Units.val_mul, div_mul_cancel]

end GlobalTheory.Mum.RosComp


open GlobalTheory.Mum.RosComp in
theorem GlobalTheory.Mum.TensRos.rosVT_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ'' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Mum.TensRos.RosVT T ν ν' (o.onB.act (star x)) (o.onB.act x) ρ'') → ∀ (χ : N'.X) (b : N'.A) (gs : Fin r → N.Gt), (∀ j, GlobalTheory.Mum.TensTor.cmp T ν ν' b j = (gs j).b) → (letI := H.starRing; ρ'' (N'.c χ) b * GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') (ν'.eX.symm (star x • ν'.eX χ)) gs = GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') χ (fun i => ∏ j, gs j ^ ρ x i j)) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact x ρ'' hros χ b gs hb
  letI := H.starRing
  have h := hρ (star x)
  rw [show H.bar (star x) = x from star_star x] at h
  refine ros_value T ν ν' (ρ (star x)) (ρ x) h _ _ (hact.2 _) (hact.2 _) ρ'' hros (N'.c χ) b (TensTor.chi T ν ν' χ) _ gs
    (fun j => ?_) hb (fun i => ?_)
  · simp only [TensTor.cmp, TensTor.chi]
    rw [ν.eA.symm_apply_eq, ν.c_eq, ν'.c_eq, ν.eX.apply_symm_apply]
    simp only [DegPre.cF, Category.assoc, T.c_pr]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [TensTor.chi, AddEquiv.apply_symm_apply, hact.1, map_sum, map_zsmul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_components_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ'' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Mum.TensRos.RosVT T ν ν' (o.onB.act (star x)) (o.onB.act x) ρ'') → ∀ (χ : N'.X) (b : N'.A) (gs : Fin r → N.Gt), (∀ j, GlobalTheory.Mum.TensTor.cmp T ν ν' b j = (gs j).b) → (letI := H.starRing; ρ'' (N'.c χ) b * GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') (ν'.eX.symm (star x • ν'.eX χ)) gs = GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') χ (fun i => ∏ j, gs j ^ ρ x i j)) := by
  first | exact @GlobalTheory.Mum.TensRos.rosVT_components | exact GlobalTheory.Mum.TensRos.rosVT_components | (intros; apply GlobalTheory.Mum.TensRos.rosVT_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValueTensorDataTransportLambdaBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValueTensorDataTransportLambdaBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRosMove

theorem rosati_alg {U : Type} [CommGroup U] (g : Fin 6 → U) (u : U) :
    (∏ k, g k ^ rosatiε k) * u * (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5) := by
  rw [Fin.prod_univ_six]
  show g 0 ^ (1 : ℤ) * g 1 ^ (-1 : ℤ) * g 2 ^ (-1 : ℤ) * g 3 ^ (-1 : ℤ) * g 4 ^ (1 : ℤ) * g 5 ^ (1 : ℤ) * u *
    (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem rosVT_move : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  intro R _ _ _ _ D D' n W T F _ _ _ N N' ν ν' O _ _ oa x ρ' hR
  obtain ⟨u, hu, u₀, hρ⟩ := hR
  have := oa.hom x
  have := oa.hom (star x)
  have hL₁ : (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).IsLB := LB.isLB_linComb D.toPre.P.isLB _ _
  obtain ⟨u'', hu'', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb D'.toPre.P.isLB _ rosatiε)
    (LB.isLB_linComb hL₁ (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε)
    (LB.linCombIso T.w _ rosatiε) (DVR.linCombIso_isGen T.w T.w_gen _ _) u hu
  refine ⟨fun a b => vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν), ⟨u'', hu'', ?_, fun _ _ => rfl⟩, ?_⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    rw [val_pull hJ, val_one]
    have h1 : (η[D'.toPre.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have hz : ∀ k, (𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A).left := fun k => by
      rw [Category.id_comp, zero2, h1, ← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [MonObj.one_comp]
    choose I hI using fun χ : _ ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ y)
    have hI' : Good D'.toPre.P.L y I := hI
    have e₀ : val u (𝟙 _ ≫ zero2 D'.toPre.P.A) y I = 1 := by
      have := val_corr hI' u₀ (𝟙 _)
      rwa [val_pull hI', val_one] at this
    have m₁ := hJ.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have m₂ := hI'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have H := hv _ (𝟙 _ ≫ zero2 D'.toPre.P.A) y _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (𝟙 _ ≫ zero2 D'.toPre.P.A) y ⟨m₁, m₂⟩
    refine H.trans (Eq.trans (congrArg₂ (· * ·) G e₀) ?_)
    rw [_root_.mul_one]
    have key : ∀ Fn : (_ ⟶ D'.toPre.P.A.left) → ((𝟙_ (Over (Spec (CommRingCat.of R)))).left.presheaf.stalk y)ˣ,
        ∏ a, Fn ((𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) a) ^ rosatiε a = 1 := by
      intro Fn
      simp only [hz]
      simp [Fin.prod_univ_succ, rosatiε]
    exact key (fun ψ => gm ψ y (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (J ψ, I ψ))
      (T.w.s (J ψ, I ψ)))
  · intro a b
    let z : Sp F := IsLocalRing.closedPoint F
    have hN : Good D.toPre.P.L z ν.J := fun q => ν.good q trivial
    have hJ' : Good D'.toPre.P.L z ν'.J := fun q => ν'.good q trivial
    have mT : ∀ y : Sp F ⟶ D'.toPre.P.A.left,
        y z ∈ (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).U (GlobalTheory.Mum.TensRos.tensJ T ν y) :=
      fun y => Set.mem_iInter.2 fun k => hN (y ≫ tensφ T.pr k)
    have m₁ : (lift (ν'.eA a) (ν'.eA b)).left z ∈ LB.wchart (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W))
        (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x))
        (fun k => GlobalTheory.Mum.TensRos.tensJ T ν ((lift (ν'.eA a) (ν'.eA b)).left ≫
          rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k)) := Set.mem_iInter.2 fun k => mT _
    have m₂ := hJ'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (lift (ν'.eA a) (ν'.eA b)).left
    have H := hv _ (lift (ν'.eA a) (ν'.eA b)).left z _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (lift (ν'.eA a) (ν'.eA b)).left z ⟨m₁, m₂⟩
    let Gp : N'.A → ((Sp F).presheaf.stalk z)ˣ := fun p => gm (ν'.eA p).left z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
        (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
    have hW : ∀ p, toStk z (wv T ν ν' p) = (Gp p).val := fun p => by
      have hm : (ν'.eA p).left z ∈ (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
          (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left)) := ⟨mT _, hJ' _⟩
      exact toStk_valF _ _ z hm _
    have ea : ∀ y c, ν'.eA (GlobalTheory.Relabel.actV ν' oa y c) = ν'.eA c ≫ oa.act y := fun y c => ν'.eA.apply_symm_apply _
    let pts : Fin 6 → N'.A := ![GlobalTheory.Relabel.actV ν' oa (star x) a * b, GlobalTheory.Relabel.actV ν' oa (star x) a, b,
      a * GlobalTheory.Relabel.actV ν' oa x b, a, GlobalTheory.Relabel.actV ν' oa x b]
    have hp : ∀ k, (lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (ν'.eA (pts k)).left := fun k => by
      rw [← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [pts, ea]
    have key : ∀ Fn : (Sp F ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ,
        ∏ k, Fn ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k) ^ rosatiε k =
          ∏ k, Fn (ν'.eA (pts k)).left ^ rosatiε k := fun Fn => by simp only [hp]
    have G' := G.trans (key (fun ψ => gm ψ z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))))
    have v'' := toStk_valF _ _ z m₁ (u''.s _)
    have v' : toStk z (ρ' a b) = (gm (lift (ν'.eA a) (ν'.eA b)).left z _ (u.s fun k => ν'.J
        ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k))).val := by
      rw [hρ]; exact toStk_valF _ _ z m₂ _
    have HH := H.trans (congrArg₂ (· * ·) G' rfl)
    apply (toStk z).injective
    show toStk z (vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν) * _) = _
    simp only [map_mul, hW, v']
    erw [v'', HH]
    simp only [← Units.val_mul]
    congr 1
    exact rosati_alg (fun k => Gp (pts k)) _

end GlobalTheory.Mum.TensRosMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValueTensorDataTransportLambdaBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiValue_tensorData_transport_lambdaBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  first | exact @GlobalTheory.Mum.TensRosMove.rosVT_move | exact GlobalTheory.Mum.TensRosMove.rosVT_move | (intros; apply GlobalTheory.Mum.TensRosMove.rosVT_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section
namespace GlobalTheory.Mum.TensRos

theorem main_alg {F : Type} [Field F] (a1 a2 P1 P2 s1 s2 A Bv C Dd E' G one : F) (hA : A ≠ 0) (hB : Bv ≠ 0)
    (hE : E' ≠ 0) (hG : G ≠ 0) (hD : Dd ≠ 0)
    (h1 : a2 * (A * Bv * C) = a1 * (Dd * E' * G)) (h2 : a2 * P1 = P2) (h3 : s1 * A * Bv = P1 * Dd * one)
    (h4 : s2 * E' * G = P2 * C * one) : s2 = s1 * a1 := by
  have hK : A * Bv * E' * G * Dd ≠ 0 := by positivity
  apply mul_right_cancel₀ hK
  linear_combination (A*Bv*Dd)*h4 - (a1*E'*G*Dd)*h3 - (A*Bv*Dd*C*one)*h2 + (P1*one*Dd)*h1

theorem rosGt_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Relabel.RosV ν' o.onB x ρ') → ∀ (v' w' : N'.Gt) (vs : Fin r → N.Gt), GtRel T ν ν' v' vs → GtRel T ν ν' w' (fun i => ∏ j, vs j ^ ρ x i j) → (letI := H.starRing; ∀ χ, (w'.s χ : F) = v'.s (ν'.eX.symm (star x • ν'.eX χ)) * ρ' (N'.c χ) v'.b) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact x ρ' hρ' v' w' vs hv hw
  letI := H.starRing
  obtain ⟨ρ'', hT, hmove⟩ := GlobalTheory.T.rosatiValue_tensorData_transport_lambdaBundle R hB D D' W T F N N' ν ν' (𝓞 E) o.onB x ρ' hρ'
  obtain ⟨-, hbij, -, -, -, hwv0, -, -⟩ := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  rw [GtRel, gtRelV_iff] at hv hw
  intro χ
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x v'.b := by
    apply hbij.1
    funext j
    rw [hw.1 j, cmp_actV T ν ν' o ρ hact x v'.b j, ← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, NumD.projB_apply, hv.1 k]
  have h1 := hmove (N'.c χ) v'.b
  rw [c_actV ν' o] at h1
  have h2 := GlobalTheory.T.rosatiGenerator_components_torusExtension R hB D D' W T F N N' ν ν' E H ρ hρ o hact x ρ'' hT χ v'.b vs hv.1
  have h3 := hv.2 (ν'.eX.symm (star x • ν'.eX χ))
  have h4 := hw.2 χ
  rw [hb] at h4
  exact main_alg _ _ _ _ _ _ _ _ _ _ _ _ _ (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) h1 h2 h3 h4

end GlobalTheory.Mum.TensRos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_values_tensor_data_matrix_action : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Relabel.RosV ν' o.onB x ρ') → ∀ (v' w' : N'.Gt) (vs : Fin r → N.Gt), GtRel T ν ν' v' vs → GtRel T ν ν' w' (fun i => ∏ j, vs j ^ ρ x i j) → (letI := H.starRing; ∀ χ, (w'.s χ : F) = v'.s (ν'.eX.symm (star x • ν'.eX χ)) * ρ' (N'.c χ) v'.b) := by
  first | exact @GlobalTheory.Mum.TensRos.rosGt_values | exact GlobalTheory.Mum.TensRos.rosGt_values | (intros; apply GlobalTheory.Mum.TensRos.rosGt_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensAct

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) [Module O D'.X]
    (o : D'.OAct O) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (i : Fin r) :
    TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) i = ∏ j, TensTor.cmp T ν ν' b j ^ ρ x i j := by
  letI := D.P.isAb.comm
  simp only [TensTor.cmp, GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x i]
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := by simp [Hom.one_def]
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have := map_prod (ν.eA.symm.toMonoidHom.comp P) (fun j => T.pr j ^ ρ x i j) Finset.univ
  simp only [map_zpow] at this
  exact this

end GlobalTheory.Mum.TensAct
namespace GlobalTheory.Mum.TensAct

section V
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem rel_one (hF : TensFacts W φ e wv) : GtRelV W φ e wv 1 1 := by
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W φ e wv hF 1
  have h2 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hF u u 1 1 hu hu
  rw [_root_.mul_one] at h2
  have h3 : u * u = u := GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv hF _ _ _ h2 hu
  rw [_root_.mul_eq_left] at h3
  exact h3 ▸ hu

theorem rel_pow (hF : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) :
    ∀ m : ℕ, GtRelV W φ e wv (v' ^ m) (vs ^ m)
  | 0 => by simpa using rel_one hF
  | m + 1 => by
    rw [_root_.pow_succ, _root_.pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hF _ _ _ _ (rel_pow hF h m) h

end V

theorem io_sum {O : Type} [CommRing O] (N : NumD O) {κ : Type} (s : Finset κ) (m : κ → ℤ) (y : κ → N.X) :
    N.io (∑ j ∈ s, m j • y j) = ∏ j ∈ s, N.io (y j) ^ m j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, N.io_add, ih]
    congr 1
    have := N.ioHom.map_zpow (Multiplicative.ofAdd (y k)) (m k)
    simpa [NumD.ioHom, ← ofAdd_zsmul] using this

def qTH {O : Type} [CommRing O] (N : NumD O) (k : ℕ) : Multiplicative N.X →* N.QT k :=
  MonoidHom.mk' (fun z => N.qTriv k z.toAdd) fun a b => Subtype.ext (Prod.ext
    (by simp [NumD.qTriv, smul_add, ofAdd_add]) (by simp [NumD.qTriv, N.io_add]))

theorem qEq_iff_mk {O : Type} [CommRing O] (N : NumD O) {k : ℕ} (p p' : N.QT k) :
    N.QEq p p' ↔ (p : N.QT k ⧸ (qTH N k).range) = p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [qTH]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    have : N.qTriv k z.toAdd = p⁻¹ * p' := hz
    rw [this, mul_inv_cancel_left]

end GlobalTheory.Mum.TensAct

open GlobalTheory.Mum.TensAct in
theorem GlobalTheory.Mum.TensAct.qkAct_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact g ev hadd hker n hn x a p' q' hp hq
  letI := H.starRing
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  have hB := GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have hB' := GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  beta_reduce at hB hB'
  obtain ⟨q0, qs, hq0, hqs, hrel0⟩ := hp
  obtain ⟨q1, qs1, hq1, hqs1, hrel1⟩ := hq
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).1 o.onB x
  let us : Fin r → N.QT n := fun i => ∏ j, qs j ^ ρ x i j
  let ts : Fin r → N.Gt := fun i => ∏ j, (qs j).1.2 ^ ρ x i j
  have hts : ∀ i, (us i).1.2 = ts i := fun i => by
    show ((MonoidHom.snd _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j) = ∏ j, (qs j).1.2 ^ ρ x i j
    rw [map_prod]
    simp only [map_zpow]
    rfl
  have husy : ∀ i, (us i).1.1.toAdd = ∑ j, ρ x i j • (qs j).1.1.toAdd := fun i => by
    show Multiplicative.toAdd (((MonoidHom.fst _ _).comp (N.QT n).subtype) (∏ j, qs j ^ ρ x i j)) = _
    rw [map_prod, toAdd_prod]
    simp only [map_zpow, toAdd_zpow]
    rfl
  obtain ⟨w', hw'⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W _ _ _ hF ts
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x q0.1.2.b := by
    apply hF.2.1.1
    funext i
    rw [cmp_actV T ν ν' ρ o hact x _ i, hw'.1 i]
    simp only [ts]
    rw [← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, NumD.projB_apply, hrel0.2.1 j]
  have hros := GlobalTheory.T.rosati_values_tensor_data_matrix_action R hR D D' W T F N N' ν ν' E H ρ hρ o hact x ρ' hρ' q0.1.2 w' (fun j => (qs j).1.2) hrel0.2 hw'

  set y'' : N'.X := ν'.eX.symm (x • p'.y) with hy''
  have hey : ∀ i, TensTor.chi T ν ν' y'' i = (us i).1.1.toAdd := fun i => by
    rw [husy i]
    have h1 : ν'.eX y'' = x • p'.y := by rw [hy'', AddEquiv.apply_symm_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [TensTor.chi, h1, hact.1 x p'.y i, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hrel0.1 j, ← hq0.1]
    rfl
  have hwn : w' ^ n = N'.io y'' := by
    have hpow := rel_pow hF hw' n
    have hio := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W _ _ _ hF y''
    have e1 : ts ^ n = fun j => N.io (TensTor.chi T ν ν' y'' j) := funext fun i => by
      rw [hey i, husy i, io_sum]
      simp only [Pi.pow_apply, ts, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← (qs j).2]
      rw [← zpow_natCast, ← zpow_natCast ((qs j).1.2), ← zpow_mul, ← zpow_mul, mul_comm]
    rw [e1] at hpow
    exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W _ _ _ hF _ _ _ hpow hio
  let tv : N'.QT n := ⟨(Multiplicative.ofAdd y'', w'), by rw [NumD.mem_QT]; exact hwn⟩
  obtain ⟨t', ht'⟩ := (hB'.2.2.2.2 n).2.1 tv

  have hex : ∀ b, ∃ c, ν.QPt (ev n b) c := fun b => ((hB.2.2.2.2 n).1 (ev n b)).exists
  choose qv hqv using hex
  have huniq : ∀ b c, ν.QPt (ev n b) c → c = qv b := fun b c h =>
    ((hB.2.2.2.2 n).1 (ev n b)).unique h (hqv b)
  have haddv : ∀ b c, N.QEq (qv b * qv c) (qv (b + c)) := fun b c => by
    obtain ⟨q, hqy, hqadd, hqeq⟩ := hadd n hn b c
    obtain ⟨cq, hcq⟩ := ((hB.2.2.2.2 n).1 q).exists
    have e1 : cq = qv b * qv c := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        change ν.eX cq.1.1.toAdd = ν.eX ((qv b).1.1.toAdd + (qv c).1.1.toAdd)
        rw [map_add (f := _), (hqv b).1, (hqv c).1, hcq.1, hqy]
      · exact (hB.2.2.1 _ _ _ _ _ _ (hqv b).2 (hqv c).2 hcq.2).1 hqadd
    rw [← e1]
    exact ((hB.2.2.2.2 n).2.2 q (ev n (b + c)) cq (qv (b + c)) hcq (hqv _)).1 hqeq
  let f : Multiplicative ((Fin g → ℤ) × (Fin g → ℤ)) →* N.QT n ⧸ (qTH N n).range :=
    MonoidHom.mk' (fun b => ((qv b.toAdd : N.QT n) : N.QT n ⧸ (qTH N n).range)) fun b c => by
      rw [toAdd_mul, ← (qEq_iff_mk N _ _).1 (haddv _ _), QuotientGroup.mk_mul]
  have hQi : ∀ i, N.QEq (us i) (qs1 i) := fun i => by
    rw [qEq_iff_mk, huniq _ _ (hqs1 i)]
    have h1 : ((qv (∑ j, ρ x i j • a j) : N.QT n) : N.QT n ⧸ (qTH N n).range) =
        f (Multiplicative.ofAdd (∑ j, ρ x i j • a j)) := rfl
    rw [h1, ofAdd_sum, map_prod]
    simp only [us, QuotientGroup.mk_prod, QuotientGroup.mk_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ofAdd_zsmul, map_zpow, huniq _ _ (hqs j)]
    rfl
  choose z hz1 hz2 using hQi
  obtain ⟨z', hz'⟩ := hF.2.2.2.1.2 z
  let eH : N'.X →+ (Fin r → N.X) := AddMonoidHom.mk' (TensTor.chi T ν ν') fun a b => funext (hF.2.2.1 a b)
  have hQ : N'.QEq tv q1 := by
    refine ⟨z', ?_, ?_⟩
    · apply hF.2.2.2.1.1
      have hs : TensTor.chi T ν ν' (y'' + n • z') = TensTor.chi T ν ν' y'' + n • TensTor.chi T ν ν' z' :=
        (map_add eH _ _).trans (congrArg _ (map_nsmul eH n z'))
      change TensTor.chi T ν ν' q1.1.1.toAdd = TensTor.chi T ν ν' (y'' + n • z')
      rw [hs]
      funext i
      rw [Pi.add_apply, Pi.smul_apply]
      rw [hrel1.1 i, hz1 i, hey i, hz']
    · have hm := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W _ _ _ hF _ _ _ _ hw' (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W _ _ _ hF z')
      have e2 : ts * (fun j => N.io (TensTor.chi T ν ν' z' j)) = fun j => (qs1 j).1.2 := funext fun i => by
        rw [Pi.mul_apply, hz2 i, hts i, hz']
      rw [e2] at hm
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W _ _ _ hF _ _ _ hrel1.2 hm
  refine ⟨t', ?_, ?_, ((hB'.2.2.2.2 n).2.2 t' q' tv q1 ht' hq1).2 hQ⟩
  · rw [← ht'.1]
    exact AddEquiv.apply_symm_apply _ _
  · exact ((GlobalTheory.Relabel.gtAct_values GlobalTheory.globalFns_holds R D'.toPre F N' ν' (𝓞 E)).2 o x ρ' hρ' p'.g t'.g q0.1.2 w'
      hq0.2 ht'.2).2 ⟨hb, hros⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrixStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (g : ℕ) (ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n), (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → ∀ n, 0 < n → ∀ (x : 𝓞 E) (a : Fin r → (Fin g → ℤ) × (Fin g → ℤ)) (p' q' : QkPt D'.toPre F n), PtRel T ν ν' p' (fun j => ev n (a j)) → PtRel T ν ν' q' (fun i => ev n (∑ j, ρ x i j • a j)) → (letI := H.starRing; QkAct o x p' q') := by
  first | exact @GlobalTheory.Mum.TensAct.qkAct_tens | exact GlobalTheory.Mum.TensAct.qkAct_tens | (intros; apply GlobalTheory.Mum.TensAct.qkAct_tens <;> assumption)
end
