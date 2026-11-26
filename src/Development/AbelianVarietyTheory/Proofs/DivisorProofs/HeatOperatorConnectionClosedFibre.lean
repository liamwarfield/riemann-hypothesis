module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivCoordinateSubPotentialsConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCoordinateConstantAdditiveInCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateLogDerivMinusPotentialsChartIndependen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateLogDerivMinusPotentialsChartIndependen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem cancel_unit {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (δ : A → B) (u : Aˣ) (L Δ : B)
    (h₁ : δ u.val = π u.val * L) (h₂ : δ u.val = π u.val * Δ) : L = Δ :=
  ((Units.isUnit u).map π).mul_left_cancel (h₁.symm.trans h₂)

section ChartFreeProof

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} {h : Heat Y.H Y.q.left Q.P.L dd D}
  {K : Type} [Field K] {ν : R} {A₀ : Over (Sp K)} {m₀ : A₀.left ⟶ Q.P.A.left} {V : h.J → Q.P.A.left.Opens}
  {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}

theorem dE_trans_unit {D' : R → K} (hC : IsConnK Q.P.A Q.P.L A₀ m₀ D' V h.j ed pb) (hD : IsDesc Y h ν m₀ V ed pb)
    (hCo : Commutes Q m₀ ed) (α : Q.X) (j : Fin 4) (T : A₀.left ⟶ A₀.left) (h₁ : T ≫ m₀ = m₀ ≫ Q.famφB α j)
    (h₂ : T ≫ A₀.hom = A₀.hom) {Z : Scheme.{0}} {a : Z ⟶ Y.H.left} {b : Z ⟶ A₀.left} (w : a ≫ Y.q.left = b ≫ m₀)
    (z : Z) (i₀ : h.J) (hi₀ : (b ≫ m₀) z ∈ V i₀)
    (δ : Y.H.left.presheaf.stalk (a z) → Z.presheaf.stalk z)
    (hδ : ∀ W, W ≤ h.W i₀ → a z ∈ W → ∀ f, δ (gs (𝟙 _) (a z) W f) = gs a z W (dE h ν i₀ W f))
    (c c' : h.J) (hc : (b ≫ T ≫ m₀) z ∈ V c) (hc' : (b ≫ T ≫ m₀) z ∈ V c') :
    δ (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) (Q.P.L.g (h.j c) (h.j c')).val) =
      (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c'))
        (Q.P.L.g (h.j c) (h.j c')).val) *
        (gs (b ≫ T) z (m₀ ⁻¹ᵁ V c') (pb c') - gs (b ≫ T) z (m₀ ⁻¹ᵁ V c) (pb c)) := by
  have e : a ≫ Y.q.left ≫ Q.famφB α j = b ≫ T ≫ m₀ := by rw [h₁, reassoc_of% w]
  have hVL : V c ⊓ V c' ≤ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := inf_le_inf (hC.2.2.1 c) (hC.2.2.1 c')
  have hpV : (Q.famφB α j) (Y.q.left (a z)) ∈ V c ⊓ V c' := by
    show (a ≫ Y.q.left ≫ Q.famφB α j) z ∈ V c ⊓ V c'
    rw [e]; exact ⟨hc, hc'⟩
  have hq0 : Y.q.left (a z) ∈ V i₀ := by
    show (a ≫ Y.q.left) z ∈ V i₀
    rw [w]; exact hi₀
  have hqU : Y.q.left (a z) ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := ⟨hq0, hpV⟩
  have hbU : (b ≫ m₀) z ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := by
    show (b ≫ m₀) z ∈ _
    rw [← w]; exact hqU
  set g := (Q.P.L.g (h.j c) (h.j c')).val
  set F := ((Q.famφB α j).app (V c ⊓ V c')).hom (rsT g (V c ⊓ V c'))
  set f := resG Q.P.A.left (inf_le_right : V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') ≤ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) F
  have s₁ : gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) g =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c'))) ((Y.q.left.app _).hom f) := by
    rw [gs_pull (𝟙 _) Y.q.left (a z) _ hqU f, Category.id_comp, gs_res Y.q.left (a z) inf_le_right hqU F,
      gs_pull Y.q.left (Q.famφB α j) (a z) _ hpV _, gs_rsT (Y.q.left ≫ Q.famφB α j) (a z) hVL hpV]
  have hle : Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ h.W i₀ := by
    rw [hD.1 i₀]; exact fun _ hx ↦ hx.1
  have hbT : (b ≫ T) z ∈ m₀ ⁻¹ᵁ (V c ⊓ V c') := ⟨hc, hc'⟩
  have m : (Y.q.left ≫ Q.famφB α j) (a z) ∈ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := hVL hpV
  have hπ : (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) _ g) = gs (b ≫ T ≫ m₀) z _ g := by
    rw [← e, ← gs_pull a (Y.q.left ≫ Q.famφB α j) z _ m g, gs_stalkMap a z _ m, gs_pull (𝟙 _) _ (a z) _ m g,
      Category.id_comp]
  rw [hπ, s₁, hδ _ hle hqU, ← hD.2.1 Z a b w z i₀ _ inf_le_left hbU f,
    hC.1.res _ _ inf_le_right le_top F, gs_rsT b z (show m₀ ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ m₀ ⁻¹ᵁ (Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) from fun _ hx ↦ hx.2) hbU,
    hCo α j T h₁ h₂ (V c ⊓ V c') (rsT g (V c ⊓ V c')) Z b z ⟨hc, hc'⟩, hC.2.2.2 c c',
    gs_mul _ z _ hbT, gs_sub _ z _ hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c' from fun _ hx ↦ hx.2) hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c from fun _ hx ↦ hx.1) hbT,
    gs_pbT (b ≫ T) m₀ z (fun _ hx ↦ hVL hx) hbT, Category.assoc]

end ChartFreeProof

theorem chartFree : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCo α T h₁ h₂ Z a b hw z i i' hi hi' w H
  unfold CoordAt at H ⊢
  have hV : ∀ c, V c ≤ Q.P.L.U (h.j c) := hC.2.2.1
  have hm := hF.mem_chart hD hV h₁ hw hi
  have hm' := hF.mem_chart hD hV h₁ hw hi'
  have hT0 := hF.T_zero (h₁ 0) (h₂ 0)
  have hi₀ : (b ≫ m₀) z ∈ V (i 0) := by
    have := hi 0
    rwa [hT0, Category.id_comp] at this
  obtain ⟨δ, -, hδm, hδ⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z hm.1
  obtain ⟨l, hl⟩ := exists_dlog (a.stalkMap z).hom δ hδm
  have hx : gs a z (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j))
      (dE h ν (i 0) _ (rsT (xc Y α fun j ↦ h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i j)) (xc Y α fun j ↦ h.j (i j))).val := by
    rw [← hδ _ inf_le_left hm, gs_rsT (𝟙 _) (a z) inf_le_right hm, gs_unit (𝟙 _) (a z) _ hm.2]
  have hx' : gs a z (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j))
      (dE h ν (i' 0) _ (rsT (xc Y α fun j ↦ h.j (i' j)).val (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i' j)) (xc Y α fun j ↦ h.j (i' j))).val := by
    have hU : a z ∈ h.W (i 0) ⊓ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) := ⟨⟨hm.1, hm'.1⟩, hm'.2⟩
    have hle : h.W (i 0) ⊓ h.W (i' 0) ⊓ (xU Y α fun j ↦ h.j (i' j)) ≤ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) :=
      fun _ hy ↦ ⟨hy.1.2, hy.2⟩
    rw [← gs_res a z hle hU, ← (isField_dE h ν hF.field (i' 0)).2.2 _ _ hle inf_le_left,
      ← hF.dE_agree hw z (i 0) (i' 0) _ inf_le_left hU, ← hδ _ (inf_le_left.trans inf_le_left) hU, gs_res (𝟙 _) (a z) hle hU,
      gs_rsT (𝟙 _) (a z) inf_le_right hm', gs_unit (𝟙 _) (a z) _ hm'.2]
  have ht := gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 Y.H.left) (a z) hm.2 hm'.2
  have hu : ∀ k, (l (gm (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z)
      (Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))))
      (Q.P.L.g (h.j (i (![1, 2, 0, 3] k))) (h.j (i' (![1, 2, 0, 3] k)))))).toAdd =
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i' (![1, 2, 0, 3] k))) (pb (i' (![1, 2, 0, 3] k))) -
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i (![1, 2, 0, 3] k))) (pb (i (![1, 2, 0, 3] k))) := by
    intro k
    have mem : (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z) ∈
        Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))) :=
      ⟨Set.mem_iInter.1 hm.2 k, Set.mem_iInter.1 hm'.2 k⟩
    refine cancel_unit _ δ _ _ _ (hl _) ?_
    rw [← gs_unit _ _ _ mem, Category.id_comp, gtφT_eq]
    exact dE_trans_unit hC hD hCo α _ (T _) (h₁ _) (h₂ _) hw z (i 0) hi₀ δ hδ _ _ (hi _) (hi' _)
  have e2 := congrArg (fun u ↦ (l u).toAdd) ht
  simp only [map_mul, toAdd_mul, trF, map_prod, map_zpow, toAdd_prod, toAdd_zpow, Fin.sum_univ_four] at e2
  rw [hu 0, hu 1, hu 2, hu 3] at e2
  simp only [DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at e2
  rw [hx, gs_stalkMap a z _ hm.2, gs_unit (𝟙 _) (a z) _ hm.2] at H
  have eH := cancel_unit _ δ _ _ _ (hl _) H
  rw [hx', hl, gs_stalkMap a z _ hm'.2, gs_unit (𝟙 _) (a z) _ hm'.2]
  congr 1
  linear_combination eH - e2

end GlobalTheory.HeatConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateLogDerivMinusPotentialsChartIndependenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_logDeriv_minus_potentials_chart_independent : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  first | exact @GlobalTheory.HeatConn.chartFree | exact GlobalTheory.HeatConn.chartFree | (intros; apply GlobalTheory.HeatConn.chartFree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIdentificationDerivationCommutesTrans
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIdentificationDerivationCommutesTrans
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section

open GlobalTheory.KS.DlogPol (gs_pbT gs_sub)

namespace GlobalTheory.HeatConn.Comm

theorem gs_stalkMap' {X X' Z : Scheme.{0}} (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U)
    (a : Γ(X, U)) : (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem cst_spMap {V V' : Type} [CommRing V] [CommRing V'] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (ψ : V' →+* V) (z : Z)
    (a : V') : cst (q ≫ spMap ψ) z a = cst q z (ψ a) := by
  rw [cst, cst, ← gs_pull _ (spMap ψ) z ⊤ trivial]
  exact congrArg (gs q z ⊤) (congrArg (fun ψ' => ψ'.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm

theorem stalkMap_eq_zero {k : Type} [Field k] {A₀ B' : Scheme.{0}} (q : B' ⟶ Sp (DualNumber k)) [Flat q]
    (sc : A₀ ⟶ B') (q₀ : A₀ ⟶ Sp k) (hsc : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (y : A₀)
    {t : B'.presheaf.stalk (sc y)} (ht : cst q (sc y) DualNumber.eps * t = 0) : (sc.stalkMap y).hom t = 0 := by
  obtain ⟨u, rfl⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero q (sc y) (a := DualNumber.eps) (b := DualNumber.eps)
    (fun c hc => by
      have h1 : c.fst = 0 := by simpa using congrArg TrivSqZeroExt.snd hc
      exact ⟨TrivSqZeroExt.inl c.snd, by ext <;> simp [h1]⟩) ht
  rw [map_mul, cst, gs_stalkMap' sc q y ⊤ trivial, ← cst, hsc, cst_spMap]
  have e0 : (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 := by simp
  rw [e0, cst, map_zero, gs_eq _ y ⊤ trivial, map_zero, map_zero, zero_mul]

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem spMap_fst_alg (k : Type) [Field k] :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
  rw [← spMap_comp]
  have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext; simp
  rw [this, spMap]
  exact Spec.map_id _

theorem exists_sec {k : Type} [Field k] {S A A₀ B' : Scheme.{0}} (p : A ⟶ S) (s : Sp k ⟶ S) (q₀ : A₀ ⟶ Sp k)
    (q : B' ⟶ Sp (DualNumber k)) (m₀ : A₀ ⟶ A) (π₁ π₂ : B' ⟶ A) (pr : B' ⟶ A₀)
    (h₀ : IsPullback m₀ q₀ p s) (h₂ : IsPullback π₂ q p (spMap (algebraMap k (DualNumber k)) ≫ s))
    (h₃ : ∀ (Z : Scheme.{0}) (x : Z ⟶ B') (y : Z ⟶ Sp k),
      x ≫ q = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂)
    (hpr₁ : pr ≫ m₀ = π₂) (hpr₂ : pr ≫ q₀ = q ≫ spMap (algebraMap k (DualNumber k))) :
    ∃ sc : A₀ ⟶ B', sc ≫ pr = 𝟙 _ ∧ sc ≫ π₂ = m₀ ∧
      sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ∧ ∀ x : B', π₁ x = π₂ x := by
  have e1 := spMap_fst_alg k
  have w : m₀ ≫ p = (q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap (algebraMap k (DualNumber k)) ≫ s := by
    rw [Category.assoc, reassoc_of% e1, h₀.w]
  let sc := h₂.lift m₀ _ w
  have hs₂ : sc ≫ π₂ = m₀ := h₂.lift_fst _ _ _
  have hsq : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := h₂.lift_snd _ _ _
  have hspr : sc ≫ pr = 𝟙 _ := h₀.hom_ext (by rw [Category.assoc, hpr₁, hs₂, Category.id_comp])
    (by rw [Category.assoc, hpr₂, reassoc_of% hsq, e1, Category.comp_id, Category.id_comp])
  have hR : IsPullback pr q q₀ (spMap (algebraMap k (DualNumber k))) :=
    IsPullback.of_right (h₁₂ := m₀) (v₁₃ := p) (h₂₂ := s) (by rw [hpr₁]; exact h₂) hpr₂ h₀
  have hL : IsPullback sc q₀ q (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) :=
    IsPullback.of_right (h₁₂ := pr) (v₁₃ := q₀) (h₂₂ := spMap (algebraMap k (DualNumber k)))
      (by rw [hspr, e1]; exact IsPullback.id_horiz q₀) hsq hR
  have surj := (GlobalTheory.EpsIso.isHomeomorph_of_isPullback hL).2.surjective
  refine ⟨sc, hspr, hs₂, hsq, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := surj x
  have := congrArg (fun g : A₀ ⟶ A => g y) (h₃ _ sc q₀ hsq)
  simpa using this

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf in
theorem const_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) : (toUnit B ≫ c').left ≫ π = π ≫ (toUnit A ≫ c).left := by
  rw [Over.comp_left, Over.comp_left, toUnit_left', toUnit_left', Category.assoc, hc, ← Category.assoc,
    ← h.1.w, Category.assoc]

theorem trans_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) :
    (padd B (𝟙 B) (toUnit B ≫ c')).left ≫ π = π ≫ (padd A (𝟙 A) (toUnit A ≫ c)).left := by
  let x₀ : Over.mk (B.hom ≫ f) ⟶ A := Over.homMk π h.1.w
  have e := h.2 B (𝟙 B) (toUnit B ≫ c') x₀ (toUnit _ ≫ c) (by simp [x₀]) (by
    rw [Over.comp_left, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left',
      ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left', Category.assoc, hc]
    rfl)
  have e2 : x₀ * (toUnit _ ≫ c) = x₀ ≫ (𝟙 A * (toUnit A ≫ c)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  change (𝟙 B * (toUnit B ≫ c')).left ≫ π = π ≫ (𝟙 A * (toUnit A ≫ c)).left
  rw [← e, e2]
  rfl

theorem exists_lift {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k]
    (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left)
    (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) (h₁ : IsGrpPullback B' Q.P.A (spMap ρ) π₁)
    (h₂ : IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂)
    (hc : ∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) (α : Q.X) (j : Fin 4) :
    ∃ φ' : B'.left ⟶ B'.left, φ' ≫ B'.hom = B'.hom ∧ φ' ≫ π₁ = π₁ ≫ Q.famφB α j ∧ φ' ≫ π₂ = π₂ ≫ Q.famφB α j := by
  have hcB : ∀ y, c' y ≫ B'.hom = (𝟙_ (Over (Sp (DualNumber k)))).hom := fun y => (hc y).1
  let cB : Q.X → (𝟙_ (Over (Sp (DualNumber k))) ⟶ B') := fun y => Over.homMk (c' y) (hcB y)
  have h1 : ∀ y, (cB y).left ≫ π₁ = spMap ρ ≫ (Q.c y).left := fun y => (hc y).2.1
  have h2 : ∀ y, (cB y).left ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left := fun y => (hc y).2.2
  fin_cases j
  · exact ⟨𝟙 _, Category.id_comp _, (Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩
  · exact ⟨(padd B' (𝟙 B') (toUnit B' ≫ cB α)).left, Over.w _, trans_comm h₁ _ _ (h1 α),
      trans_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ cB α).left, Over.w _, const_comm h₁ _ _ (h1 α), const_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ η[B']).left, Over.w _,
      const_comm h₁ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₁),
      const_comm h₂ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₂)⟩

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem commutes : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsGrpPullback A₀ Q.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → Commutes Q m₀ ed := by
  intro R _ _ Q k _ ρ A₀ _ m₀ hA₀ ed B' _ π₁ π₂ c' h₁ h₂ h₃ hc pr hpr₁ hpr₂ hD α j T hT₁ hT₂ W f Z b z hz
  have hfA : Flat Q.P.A.hom := by
    have := Q.P.smoothDim
    have : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
    infer_instance
  have hfB : Flat B'.hom := MorphismProperty.of_isPullback h₁.1 hfA
  obtain ⟨φ', hφ'0, hφ'1, hφ'2⟩ := exists_lift Q ρ B' π₁ π₂ c' h₁ h₂ hc α j
  have e2 : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := spMap_comp _ _
  obtain ⟨sc, hspr, hs₂, hsq, hpts⟩ := exists_sec Q.P.A.hom _ A₀.hom B'.hom m₀ π₁ π₂ pr hA₀.1
    (e2 ▸ h₂.1) h₃ hpr₁ hpr₂
  have hpre : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ π₁ ⁻¹ᵁ U := fun U x hx => by
    change π₁ x ∈ U
    rw [hpts x]
    exact hx
  have hprle : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U x hx => by
    change m₀ (pr x) ∈ U
    have : (pr ≫ m₀) x ∈ U := by rw [hpr₁]; exact hx
    simpa using this
  have hφpr : φ' ≫ pr = pr ≫ T := hA₀.1.hom_ext
    (by rw [Category.assoc, Category.assoc, hpr₁, hφ'2, hT₁, ← Category.assoc, hpr₁])
    (by rw [Category.assoc, Category.assoc, hpr₂, ← Category.assoc, hφ'0, hT₂, hpr₂])
  set φ := Q.famφB α j with hφdef
  have key : ∀ y : A₀.left, (T ≫ m₀) y ∈ W →
      gs (𝟙 _) y (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) = gs T y (m₀ ⁻¹ᵁ W) (ed W f) := by
    intro y hy
    have hy' : φ (m₀ y) ∈ W := by
      have h := hy
      rw [hT₁] at h
      all_goals simpa using h
    have m₂ : sc y ∈ π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (π₂ (sc y)) ∈ W
      have : (sc ≫ π₂) y = m₀ y := by rw [hs₂]
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact hy'
    have m₃ : φ' (sc y) ∈ π₂ ⁻¹ᵁ W := by
      change π₂ (φ' (sc y)) ∈ W
      have : (φ' ≫ π₂) (sc y) = φ (π₂ (sc y)) := by rw [hφ'2]; simp
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact m₂
    have eA := congrArg (gs (𝟙 B'.left) (sc y) (π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W))) (hD (φ ⁻¹ᵁ W) ((φ.app W).hom f))
    rw [gs_add (𝟙 _) (sc y) _ m₂, gs_mul (𝟙 _) (sc y) _ m₂, gs_pbT (𝟙 _) π₁ (sc y) (hpre _) m₂,
      gs_pbT (𝟙 _) π₂ (sc y) le_rfl m₂, gs_pbT (𝟙 _) pr (sc y) (hprle _) m₂, gs_constFn B'.hom _ (𝟙 _) (sc y) m₂] at eA
    have eB := congrArg (gs φ' (sc y) (π₂ ⁻¹ᵁ W)) (hD W f)
    rw [gs_add φ' (sc y) _ m₃, gs_mul φ' (sc y) _ m₃, gs_pbT φ' π₁ (sc y) (hpre _) m₃,
      gs_pbT φ' π₂ (sc y) le_rfl m₃, gs_pbT φ' pr (sc y) (hprle _) m₃, gs_constFn B'.hom _ φ' (sc y) m₃, hφ'1, hφ'2, hφ'0, hφpr] at eB
    simp only [Category.id_comp] at eA
    have m₁' : φ (π₁ (sc y)) ∈ W := by rw [hpts]; exact m₂
    rw [← gs_pull π₁ φ (sc y) W m₁', ← gs_pull π₂ φ (sc y) W m₂] at eB
    have hk : cst B'.hom (sc y) DualNumber.eps * (gs pr (sc y) (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) -
        gs (pr ≫ T) (sc y) (m₀ ⁻¹ᵁ W) (ed W f)) = 0 := by
      linear_combination eB - eA
    have h0 := stalkMap_eq_zero B'.hom sc A₀.hom hsq y hk
    have hy0 : pr (sc y) = y := by
      have := congrArg (fun g : A₀.left ⟶ A₀.left => g y) hspr
      simpa using this
    have ma : pr (sc y) ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (m₀ (pr (sc y))) ∈ W
      rw [hy0]; exact hy'
    have mb : (pr ≫ T) (sc y) ∈ m₀ ⁻¹ᵁ W := by
      change m₀ ((pr ≫ T) (sc y)) ∈ W
      simp only [Scheme.Hom.comp_apply]
      rw [hy0]; simpa using hy
    rw [map_sub, gs_stalkMap' sc pr y _ ma, gs_stalkMap' sc (pr ≫ T) y _ mb, hspr, reassoc_of% hspr] at h0
    exact sub_eq_zero.1 h0
  have hyz : (T ≫ m₀) (b z) ∈ W := by simpa using hz
  have mz1 : b z ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
    change φ (m₀ (b z)) ∈ W
    have h := hyz
    rw [hT₁] at h
    all_goals simpa using h
  have mz2 : T (b z) ∈ m₀ ⁻¹ᵁ W := by
    change m₀ (T (b z)) ∈ W
    simpa using hyz
  rw [gs_stalkMap b z _ mz1, key (b z) hyz, gs_stalkMap' b T z _ mz2]

end GlobalTheory.HeatConn.Comm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIdentificationDerivationCommutesTransStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_pullback_identification_derivation_commutes_translations : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsGrpPullback A₀ Q.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → Commutes Q m₀ ed := by
  first | exact @GlobalTheory.HeatConn.Comm.commutes | exact GlobalTheory.HeatConn.Comm.commutes | (intros; apply GlobalTheory.HeatConn.Comm.commutes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermAlongFibreConnection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermAlongFibreConnection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

section T
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem trF_term (e : ℕ) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι) (y : Y.H.left) :
    trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t *
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
          (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) := by
  let G : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι → (Y.H.left.presheaf.stalk y)ˣ := fun ψ i =>
    gm ψ y (Q.P.L.U (J ψ) ⊓ Q.P.L.U i) (Q.P.L.g (J ψ) i)
  have e1 : trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t =
      ∏ k, G (Y.q.left ≫ Q.famφB α k) (t k) ^ DegPre.famε e k := rfl
  have e2 : trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
      (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) =
      ∏ k, G (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) (t (![1, 2, 0, 3] k)) ^ DegPre.gtε k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.id_comp, gtφT_eq]
  have e3 : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      G Y.q.left (t 0) ^ (e : ℤ) := by
    rw [trF, Fin.prod_univ_one, Category.id_comp]
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  rw [e1, e2, e3]
  simp only [Fin.prod_univ_four, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, f0, Category.comp_id]
  rw [zpow_sub_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv, zpow_one, zpow_neg]
  abel

theorem term_germ {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) (y : Y.H.left) (h₁ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : y ∈ xU Y α t) :
    gs (𝟙 _) y _ (τ.f fun _ => t 0) = gs Y.q.left y _ (σ.f t) * gs (𝟙 _) y _ (xc Y α t).val := by
  have hL : Q.P.L.IsLB := Q.P.isLB
  choose J hJ using fun χ : Y.H.left ⟶ Q.P.A.left => exists_chart hL (χ y)
  have hJ' : Good Q.P.L y J := hJ
  have e₀ := hτ Y.H (𝟙 _) y J hJ'
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  have h₀ : y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => t 0 := Set.mem_iInter.2 fun _ => by
    have := Set.mem_iInter.1 h₁ 0
    rw [f0] at this
    exact this
  rw [sval_of τ _ y J (fun _ => J Y.q.left) (fun _ => by simp),
    sval_of σ _ y J (fun j => J (Y.q.left ≫ Q.famφB α j)) (fun _ => by simp),
    val_of _ _ y J (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => by rw [Category.id_comp, gtφT_eq])] at e₀
  simp only [Over.id_left, Over.comp_left, Category.id_comp] at e₀
  have m₁ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => J Y.q.left :=
    Set.mem_iInter.2 fun _ => hJ _
  have m₂ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) fun j => J (Y.q.left ≫ Q.famφB α j) :=
    Set.mem_iInter.2 fun j => hJ _
  have m₃ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α)
      fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) :=
    Set.mem_iInter.2 fun k => by
      show y ∈ (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) ⁻¹ᵁ _
      rw [gtφT_eq]; exact hJ _
  rw [sec_trans τ _ y m₁ h₀, sec_trans σ Y.q.left y m₂ h₁, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 _) y m₃ h₂,
    Units.val_mul] at e₀
  rw [gs_unit (𝟙 _) y _ h₂]
  rw [trF_term Y e α t J y, Units.val_mul] at e₀
  exact ((Units.isUnit _).mul (Units.isUnit _)).mul_left_cancel (e₀.trans (mul_mul_mul_comm _ _ _ _))
end T

section T2
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem term_germ_at {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) {Z : Scheme.{0}} (r : Z ⟶ Y.H.left) (z : Z)
    (h₁ : Y.q.left (r z) ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : r z ∈ xU Y α t) :
    gs r z _ (τ.f fun _ => t 0) = gs (r ≫ Y.q.left) z _ (σ.f t) * gs r z _ (xc Y α t).val := by
  have h₀ : r z ∈ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => t 0 :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h₁ 0
  have h₁' : Y.q.left (r z) ∈ (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U t := h₁
  have e₁ : gs Y.q.left (r z) _ (σ.f t) = gs (𝟙 _) (r z) (Y.q.left ⁻¹ᵁ _) ((Y.q.left.app _).hom (σ.f t)) := by
    rw [gs_pull (𝟙 _) Y.q.left (r z) _ h₁', Category.id_comp]
  rw [gs_stalkMap r z _ h₀, term_germ Y hτ t (r z) h₁ h₂, map_mul, ← gs_stalkMap r z _ h₂, e₁,
    ← gs_stalkMap r z _ h₁', gs_pull r Y.q.left z _ h₁']
end T2

theorem heat_term_fibre : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ (α : Q.X) (c : K), CoordEq Y h ν m₀ V pb α c → ∀ (σ σ' : Q.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ U : A₀.left.Opens, U ≤ m₀ ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j)) → (∀ j, U ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) U = 2 * (e : Γ(A₀.left, U)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) U + pbT m₀ (σ.f (fun j => h.j (i j))) U * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, U)) * pbT (T j) (pb (i j)) U + constFn A₀.hom U c)) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hK hD α c hC σ σ' hA i T hT₁ hT₂ U hU hUT
  obtain ⟨τ, τ', hτ, hτ', hAc⟩ := hA
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hK.2.2.1
  have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => hUT j hz
  have ha := hF.mem_chart hD hV hT₁ w hi
  have T0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have wz : Y.q.left (a z) = m₀ (b z) := by
    have := congrArg (fun f => f z) w
    simpa using this
  set W := (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U fun j => h.j (i j) with hWdef
  have hU' : U ≤ m₀ ⁻¹ᵁ W := hU
  have hbW : m₀ (b z) ∈ W := hU hz
  have hqa : Y.q.left (a z) ∈ W := wz ▸ hbW
  have hb0 : (b ≫ m₀) z ∈ V (i 0) := by simpa [T0] using hi 0

  have P : ∀ j, gs b z U (pbT (T j) (pb (i j)) U) = gs (b ≫ T j) z _ (pb (i j)) := fun j =>
    gs_pbT b (T j) z (hUT j) hz _
  have Ed : gs b z U (rsT (ed W (σ.f fun j => h.j (i j))) U) = gs b z (m₀ ⁻¹ᵁ W) (ed W (σ.f fun j => h.j (i j))) :=
    gs_rsT b z hU' hz _
  have Sb : ∀ s : Q.SecB e α, gs b z U (pbT m₀ (s.f fun j => h.j (i j)) U) = gs (a ≫ Y.q.left) z W (s.f fun j => h.j (i j)) :=
    fun s => by rw [gs_pbT b m₀ z hU' hz, w]
  have Cc : gs b z U (constFn A₀.hom U c) = cst (b ≫ A₀.hom) z c := gs_constFn _ _ _ _ hz _

  have hΘ : ∀ a' b', gsH a z (h.W (i 0)) ha.1 (constFn Y.H.hom (h.W (i 0)) (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z (h.W (i 0)) ha.1, hF.symb, cst_eq_cstH, map_zero]
  have hop := congrArg (gsH a z (h.W (i 0)) ha.1) (hAc (i 0))
  rw [map_op h ν e hF.inv (i 0) (h.W (i 0)) le_rfl _ hΘ] at hop
  simp only [← gs_eq_gsH] at hop
  have hWc : h.W (i 0) ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => h.j (i 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => h.le (i 0) hy
  rw [gs_rsT a z hWc ha.1, gs_rsT a z le_rfl ha.1,
    term_germ_at Y hτ' (fun j => h.j (i j)) a z hqa ha.2, ← hD.2.2 Z a b w z (i 0) hb0] at hop

  obtain ⟨δ, -, hδm, hδv⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z ha.1
  set U' : Q.P.A.left.Opens := V (i 0) ⊓ W with hU'def
  have hqU : Y.q.left ⁻¹ᵁ U' ≤ h.W (i 0) := by
    rw [hD.1 (i 0)]; exact fun y (hy : Y.q.left y ∈ U') => hy.1
  have haV : Y.q.left (a z) ∈ V (i 0) := by
    have := ha.1; rw [hD.1 (i 0)] at this; exact this
  have haU : a z ∈ Y.q.left ⁻¹ᵁ U' := ⟨haV, hqa⟩
  have hbU : (b ≫ m₀) z ∈ U' := ⟨hb0, by simpa using hbW⟩
  have haU' : (a ≫ Y.q.left) z ∈ U' := by simpa using haU
  set f' : Γ(Q.P.A.left, U') := resG Q.P.A.left (inf_le_right : U' ≤ W) (σ.f fun j => h.j (i j)) with hf'
  have hAB : gs (𝟙 _) (a z) (h.W (i 0)) (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0))) =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ U') ((Y.q.left.app U').hom f') *
        gs (𝟙 _) (a z) (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
          (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
    rw [gs_rsT (𝟙 _) (a z) hWc ha.1, term_germ Y hτ (fun j => h.j (i j)) (a z) hqa ha.2,
      gs_rsT (𝟙 _) (a z) inf_le_right ha, gs_pull (𝟙 _) Y.q.left (a z) U' haU, Category.id_comp, hf',
      gs_res Y.q.left (a z) inf_le_right haU]
  have hδ := hδv (h.W (i 0)) le_rfl ha.1 (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0)))
  rw [hAB, hδm, hδv _ hqU haU, hδv _ inf_le_left ha, ← hD.2.1 Z a b w z (i 0) U' inf_le_left hbU,
    hf', hK.1.res W U' inf_le_right le_top, gs_rsT b z (fun y (hy : m₀ y ∈ U') => hy.2) hbU,
    hC T hT₁ hT₂ Z a b w z i hi, ← gs_stalkMap a z _ haU, ← gs_stalkMap a z _ ha, gs_pull a Y.q.left z U' haU,
    gs_res _ z inf_le_right haU', gs_rsT a z inf_le_right ha] at hδ
  rw [gs_rsT a z hWc ha.1 (τ.f fun _ => h.j (i 0)), term_germ_at Y hτ (fun j => h.j (i j)) a z hqa ha.2, ← hδ] at hop
  have hX : IsUnit (gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val) := by
    rw [gs_unit a z _ ha.2]; exact Units.isUnit _
  rw [Sb σ', gs_eq_gsH b z U hz]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_add (f := _), map_sum, map_natCast, map_ofNat, map_intCast]
  simp only [← gs_eq_gsH b z U hz]
  rw [Ed, Sb σ, Cc, Fin.sum_univ_four, P 0, P 1, P 2, P 3]
  rw [T0, Category.comp_id] at hop ⊢
  simp only [W] at hop ⊢
  have f0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
  have f1 : DegPre.famε e 1 = 1 := rfl
  have f2 : DegPre.famε e 2 = -1 := rfl
  have f3 : DegPre.famε e 3 = 1 := rfl
  rw [f0, f1, f2, f3]
  push_cast
  apply hX.mul_left_cancel
  linear_combination hop
end GlobalTheory.HeatConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermAlongFibreConnectionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_operator_fourier_term_along_fibre_connection : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ (α : Q.X) (c : K), CoordEq Y h ν m₀ V pb α c → ∀ (σ σ' : Q.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ U : A₀.left.Opens, U ≤ m₀ ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j)) → (∀ j, U ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) U = 2 * (e : Γ(A₀.left, U)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) U + pbT m₀ (σ.f (fun j => h.j (i j))) U * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, U)) * pbT (T j) (pb (i j)) U + constFn A₀.hom U c)) := by
  first | exact @GlobalTheory.HeatConn.heat_term_fibre | exact GlobalTheory.HeatConn.heat_term_fibre | (intros; apply GlobalTheory.HeatConn.heat_term_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedHeatConnectionOnAbelianFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedHeatConnectionOnAbelianFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.KS.GlueDer (rsT_eq res_app pre_mono)
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_sub)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem exists_descData : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a, IsField ⊤ (dd a)) → (∀ a V r, dd a V (constFn Y.H.hom V r) = 0) → (∀ a α V f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∃ (V : h.J → Q.P.A.left.Opens) (E : h.J → Fld Q.P.A.left) (P : ∀ i, Γ(Q.P.A.left, V i)), (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ (∀ i, IsLift Q.P.A D (V i) (E i)) ∧ (∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (E i V' f) = GlobalTheory.HeatConn.dE h ν i _ ((Y.q.left.app V').hom f)) ∧ ∀ i, (Y.q.left.app (V i)).hom (P i) = rsT (GlobalTheory.HeatConn.pE h ν i) (Y.q.left ⁻¹ᵁ V i) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hfield hconst hwt hB
  choose V hV using fun i => (hB i).1
  have hlift : ∀ i, IsLift Y.H D (Y.q.left ⁻¹ᵁ V i) (dE h ν i) := fun i => by
    rw [← hV i]
    refine ⟨isField_dE h ν hfield i, fun O hO r => ?_⟩
    show h.d i O _ + constFn Y.H.hom O ν * ∑ a, constFn Y.H.hom O (h.u a) * dd a O (constFn Y.H.hom O r) = _
    simp only [hconst, mul_zero, Finset.sum_const_zero, add_zero]
    exact (h.lift i).2 O hO r
  have hwt0 : ∀ i (V' : Q.P.A.left.Opens), V' ≤ V i → ∀ f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V') f →
      IsWt Y 0 (Y.q.left ⁻¹ᵁ V') (dE h ν i _ f) := by
    intro i V' hV' f hf
    exact WtAlg.isWt_add ((hB i).2.2.2 0 V' ((GlobalTheory.KS.GlueDer.pre_mono _ hV').trans (hV i).ge) f hf)
      (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν)
        (WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hwt a 0 _ f hf)))
  choose E hE hq using fun i => AbConst.exists_desc Y (V i) (dE h ν i) D (hlift i) (hwt0 i)
  have hP : ∀ i, ∃ a, (Y.q.left.app (V i)).hom a = rsT (pE h ν i) (Y.q.left ⁻¹ᵁ V i) := fun i => by
    refine AbConst.exists_app_eq Y ?_
    have hw : IsWt Y 0 (h.W i) (pE h ν i) :=
      WtAlg.isWt_add (hB i).2.1 (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν) (hB i).2.2.1)
    have tr : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)), W = Y.q.left ⁻¹ᵁ V i → IsWt Y 0 W s →
        IsWt Y 0 _ (rsT s (Y.q.left ⁻¹ᵁ V i)) := by
      rintro W s rfl hs
      rwa [WtAlg.rsT_self]
    exact tr _ _ (hV i) hw
  choose P hP using hP
  exact ⟨V, E, P, hV, hE, hq, hP⟩

theorem exists_glue_desc : ∀ {R K : Type} [CommRing R] [Field K] (G : Over (Sp R)) (A₀ : Over (Sp K)) (m₀ : A₀.left ⟶ G.left) (φ : R →+* K), m₀ ≫ G.hom = A₀.hom ≫ spMap φ → ∀ (D : R → R) {I : Type} (V : I → G.left.Opens), ⨆ i, V i = ⊤ → ∀ (E : I → Fld G.left), (∀ i, IsLift G D (V i) (E i)) → (∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f)) → ∃ ed : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) ⊤ ed ∧ ∀ i U, U ≤ V i → ∀ f, ed U f = (m₀.app U).hom (E i U f) := by
  intro R K _ _ G A₀ m₀ φ hm D I V hV E hE hc
  have hW : ∀ y, ∃ i, m₀ y ∈ V i := fun y => by
    have hy : m₀ y ∈ ⨆ i, V i := by rw [hV]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have he : ∀ i, GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) (V i) (fun W f => (m₀.app W).hom (E i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(hE i).1.1 W hW, map_add (f := _)]
    · rw [(hE i).1.2.1 W hW, map_add (f := _), map_mul, map_mul]
    · rw [(hE i).1.2.2 W W' h' hW, GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ h'), GlobalTheory.KS.GlueDer.res_app m₀ h']
    · rw [(hE i).2 W hW, GlobalTheory.KS.GlueDer.app_const φ _ _ m₀ hm]
  obtain ⟨ed, hed, hchar⟩ := GlobalTheory.InteriorKS.glue_along A₀.hom G.hom m₀ (fun r => φ (D r)) V hW
    (fun i W f => (m₀.app W).hom (E i W f)) he fun i i' O hO f => hc i i' O hO f
  refine ⟨ed, hed, fun i U hU f => hchar U f _ fun i' => ?_⟩
  have h1 := (he i).res U (U ⊓ V i') inf_le_left hU f
  rw [GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ inf_le_left)] at h1
  rw [← h1]
  exact hc i i' _ (le_inf (inf_le_left.trans hU) inf_le_right) _

theorem connK_transition : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] {φ : R →+* K} {e : ℕ} {ν : R} {A₀ : Over (Sp K)} [GrpObj A₀] {m₀ : A₀.left ⟶ Q.P.A.left}, GlobalTheory.HeatConn.IsFibre Y h φ e ν A₀ m₀ → ∀ {V : h.J → Q.P.A.left.Opens} {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}, GlobalTheory.HeatConn.IsDesc Y h ν m₀ V ed pb → (∀ i, V i ≤ Q.P.L.U (h.j i)) → ∀ (i i' : h.J), ed (V i ⊓ V i') (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) = pbT m₀ (Q.P.L.g (h.j i) (h.j i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) * (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hD hV i i'
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hF.inv
    rw [Nat.cast_zero, mul_zero] at this
    exact zero_ne_one this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0
  have hUL : V i ⊓ V i' ≤ Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i') := inf_le_inf (hV i) (hV i')
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hz' : (a ≫ Y.q.left) z ∈ V i ⊓ V i' := by rw [w]; exact hz
  have haΩ : a z ∈ Y.q.left ⁻¹ᵁ (V i ⊓ V i') := hz'
  have hΩW : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ h.W i ⊓ h.W i' := by
    rw [hD.1 i, hD.1 i']; exact le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right)
  have hΩL : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := pre_mono _ hUL
  have hG : (Y.q.left.app (V i ⊓ V i')).hom (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) =
      pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [rsT_eq hUL, ← res_app Y.q.left hUL (pre_mono _ hUL), pbT, dif_pos hΩL]; rfl
  have hz1 : (b ≫ m₀) z ∈ V i := hz.1
  have hz2 : (b ≫ m₀) z ∈ V i' := hz.2
  rw [hD.2.1 Z a b w z i _ inf_le_left hz, hG, gs_mul b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (pre_mono _ hUL) hz,
    gs_rsT b z (pre_mono m₀ inf_le_right) hz, gs_rsT b z (pre_mono m₀ inf_le_left) hz, hD.2.2 Z a b w z i' hz2,
    hD.2.2 Z a b w z i hz1, ← w, ← gs_pbT a Y.q.left z hΩL haΩ, ← gs_rsT a z (hΩW.trans inf_le_right) haΩ,
    ← gs_rsT a z (hΩW.trans inf_le_left) haΩ]
  simp only [gs_eq_gsH a z _ haΩ]
  set π := gsH a z _ haΩ
  set G := pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i'))
  have hΘ : ∀ a' b', π (constFn Y.H.hom _ (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z _ haΩ, hF.symb, cst_eq_cstH, map_zero]
  have hpow : ∀ (m : ℕ) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))),
      dE h ν i _ (f ^ (m + 1)) = ((m + 1 : ℕ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))) * f ^ m * dE h ν i _ f := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, (isField_dE h ν hF.field i).2.1 _ (hΩW.trans inf_le_left), ih]
      push_cast; ring
  have e1 := congrArg π (h.glue (k + 1) i i' _ hΩW 1)
  rw [_root_.mul_one, map_op h ν (k + 1) hF.inv i _ (hΩW.trans inf_le_left) π hΘ, map_mul,
    map_op h ν (k + 1) hF.inv i' _ (hΩW.trans inf_le_right) π hΘ, hpow,
    AbConst.isField_one (isField_dE h ν hF.field i') (hΩW.trans inf_le_right)] at e1
  simp only [map_mul, map_pow, map_natCast, map_one, map_zero, zero_add, _root_.mul_one] at e1
  have h2 : IsUnit (2 : Z.presheaf.stalk z) := by
    simpa only [map_ofNat] using (two_ne_zero (α := K)).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hk : IsUnit (((k + 1 : ℕ)) : Z.presheaf.stalk z) := by
    simpa only [map_natCast] using
      (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k) : ((k + 1 : ℕ) : K) ≠ 0).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hGu : IsUnit G := by
    simp only [G, pbT, dif_pos hΩL]; exact (Units.isUnit _).map _
  have hc : IsUnit (2 * ((k + 1 : ℕ) : Z.presheaf.stalk z) ^ 2 * π G ^ k) := (h2.mul (hk.pow 2)).mul ((hGu.map π).pow k)
  refine hc.mul_left_cancel ?_
  push_cast at e1 ⊢
  linear_combination e1

theorem exists_connK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF
  have := (AbConst.surjective_q Y).1
  obtain ⟨V, E, P, hW, hE, hq, hP⟩ := exists_descData Y h ν hF.field hF.const hF.wt hF.basic
  have hm : m₀ ≫ Q.P.A.hom = A₀.hom ≫ spMap φ := hF.pull.1.w
  have hcov : ⨆ i, V i = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hW] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hVL : ∀ i, V i ≤ Q.P.L.U (h.j i) := fun i x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ h.W i := by rw [hW]; exact hx
    exact h.le i hy
  have hc : ∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f) := by
    intro i i' O hO f
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    have hz' : (a ≫ Y.q.left) z ∈ O := by rw [w]; exact hz
    rw [gs_pull b m₀ z O hz, gs_pull b m₀ z O hz, ← w, ← gs_pull a Y.q.left z O hz', ← gs_pull a Y.q.left z O hz',
      hq i O (hO.trans inf_le_left), hq i' O (hO.trans inf_le_right)]
    refine hF.dE_agree w z i i' _ ?_ hz' _
    rw [hW i, hW i']
    exact le_inf (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_left)) (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_right))
  obtain ⟨ed, hed, hedE⟩ := exists_glue_desc Q.P.A A₀ m₀ φ hm D V hcov E hE hc
  let pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i) := fun i => (m₀.app (V i)).hom (P i)
  have hD : IsDesc Y h ν m₀ V ed pb := by
    refine ⟨hW, fun Z a b w z i U hU hz f => ?_, fun Z a b w z i hz => ?_⟩
    · have hz' : (a ≫ Y.q.left) z ∈ U := by rw [w]; exact hz
      rw [hedE i U hU f, gs_pull b m₀ z U hz, ← w, ← gs_pull a Y.q.left z U hz', hq i U hU f]
    · have hz' : (a ≫ Y.q.left) z ∈ V i := by rw [w]; exact hz
      show gs b z _ ((m₀.app (V i)).hom (P i)) = _
      rw [gs_pull b m₀ z (V i) hz, ← w, ← gs_pull a Y.q.left z (V i) hz', hP i]
      exact GlobalTheory.KS.DlogPol.gs_rsT a z (hW i).ge hz' _
  exact ⟨V, ed, pb, ⟨hed, hcov, hVL, fun i i' => connK_transition Y h hF hD hVL i i'⟩, hD⟩

end GlobalTheory.HeatConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedHeatConnectionOnAbelianFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_heat_connection_on_abelian_fibre : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  first | exact @GlobalTheory.HeatConn.exists_connK_desc | exact GlobalTheory.HeatConn.exists_connK_desc | (intros; apply GlobalTheory.HeatConn.exists_connK_desc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConnectionClosedFibre
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

theorem heat_connection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (e : ℕ), 1 ≤ e → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ (V : h.J → P.D.toPre.P.A.left.Opens) (ed : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.D.toPre.P.A P.D.toPre.P.L A₀ m₀ (fun r => (ρ r).snd) V h.j ed pb ∧ (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∃ c : P.D.toPre.X →+ k, ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ P.D.toPre.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ O : A₀.left.Opens, O ≤ m₀ ⁻¹ᵁ LB.wchart P.D.toPre.P.L (P.D.toPre.famφB α) (fun j => h.j (i j)) → (∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) O = 2 * (e : Γ(A₀.left, O)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) O + pbT m₀ (σ.f (fun j => h.j (i j))) O * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O + constFn A₀.hom O (c α))) := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _
  letI := H.starRing
  intro Y n' v' dd hv D q _ h hB _ hΘ ρ hρ e he A₀ _ m₀ hpull
  have hfst : ∀ r, (ρ r).fst = MvPowerSeries.constantCoeff r := fun r => by
    rw [hρ r]; simp
  have hsnd : ∀ r, (ρ r).snd = MvPowerSeries.constantCoeff (D r) := fun r => by
    rw [hρ r]; simp
  have he0 : (e : k) ≠ 0 := by
    have : (0 : ℕ) < e := he
    exact_mod_cast this.ne'
  have hF : IsFibre Y h ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) e
      (algebraMap k (ChartRing k m d) ((e : k)⁻¹)) A₀ m₀ :=
    { field := fun a => (hv a).1
      const := fun a V r => GlobalTheory.Heat.Adjust.inv_constFn Y.H (v' a) (dd a) (hv a) V r
      wt := fun a α V f hf => GlobalTheory.Heat.IsInv.isWt Y (v' a) (dd a) (hv a) α V f hf
      basic := hB
      symb := fun a b => by
        show (ρ (h.Θ a b)).fst = 0
        rw [hfst]
        by_contra hne
        have hu : IsUnit (h.Θ a b) :=
          MvPowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hne)
        exact (IsLocalRing.mem_maximalIdeal _).mp (hΘ a b) hu
      inv := by
        rw [← map_natCast (algebraMap k (ChartRing k m d)) e, ← map_mul, inv_mul_cancel₀ he0, map_one]
      pull := hpull }
  obtain ⟨V, ed, pb, hC, hDs⟩ := GlobalTheory.T.exists_descended_heat_connection_on_abelian_fibre Y h _ e _ A₀ m₀ hF
  have hD' : (fun r => ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) (D r)) = fun r => (ρ r).snd := by
    funext r
    show (ρ (D r)).fst = (ρ r).snd
    rw [hfst, hsnd]
  rw [hD'] at hC
  refine ⟨V, ed, pb, hC, hDs.1, ?_⟩
  intro B' _ π₁ π₂ c' h1 h2 h3 h4 pr hpr1 hpr2 hed
  have hCom := GlobalTheory.T.two_pullback_identification_derivation_commutes_translations P.D.toPre ρ A₀ m₀ hpull ed B' π₁ π₂ c' h1 h2 h3 h4 pr hpr1 hpr2 hed
  rw [← hD'] at hC
  have hCF := GlobalTheory.T.coordinate_logDeriv_minus_potentials_chart_independent Y h _ e _ A₀ m₀ hF V ed pb hC hDs hCom
  choose cf hcf using fun α => GlobalTheory.T.logDeriv_coordinate_sub_potentials_const Y h _ e _ A₀ m₀ hF V ed pb hC hDs α (hCF α)
  have hadd : ∀ α β, cf (α + β) = cf α + cf β := fun α β =>
    GlobalTheory.T.raynaud_coordinate_constant_additive_in_character Y h _ e _ A₀ m₀ hF V ed pb hC hDs hCom α β (cf α) (cf β) (cf (α + β))
      (hcf α) (hcf β) (hcf (α + β))
  refine ⟨AddMonoidHom.mk' cf hadd, ?_⟩
  intro α σ σ' hT i T hT1 hT2 O' hO1 hO2
  exact GlobalTheory.T.heat_operator_fourier_term_along_fibre_connection Y h _ e _ A₀ m₀ hF V ed pb hC hDs α (cf α) (hcf α) σ σ' hT i T hT1 hT2 O' hO1 hO2

end GlobalTheory.HeatConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConnectionClosedFibreStatement
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
theorem _root_.GlobalTheory.T.heatOperator_connection_closedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (e : ℕ), 1 ≤ e → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∃ (V : h.J → P.D.toPre.P.A.left.Opens) (ed : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.D.toPre.P.A P.D.toPre.P.L A₀ m₀ (fun r => (ρ r).snd) V h.j ed pb ∧ (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∃ c : P.D.toPre.X →+ k, ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ P.D.toPre.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ O : A₀.left.Opens, O ≤ m₀ ⁻¹ᵁ LB.wchart P.D.toPre.P.L (P.D.toPre.famφB α) (fun j => h.j (i j)) → (∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) O = 2 * (e : Γ(A₀.left, O)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) O + pbT m₀ (σ.f (fun j => h.j (i j))) O * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O + constFn A₀.hom O (c α))) := by
  first | exact @GlobalTheory.HeatConn.heat_connection | exact GlobalTheory.HeatConn.heat_connection | (intros; apply GlobalTheory.HeatConn.heat_connection <;> assumption)
end
