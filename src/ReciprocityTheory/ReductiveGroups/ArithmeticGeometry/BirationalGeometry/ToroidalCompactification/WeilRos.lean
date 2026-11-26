module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_local_gen {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (y : Y) : ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (LB.LinComb M (fun k => V.ι ≫ φ k) ε), t.IsGen := by
  choose j₀ hj using fun k => exists_chart hM (φ k y)
  refine ⟨LB.wchart M φ j₀, Set.mem_iInter.2 hj, ?_⟩
  have all : ∀ w : (LB.wchart M φ j₀).toScheme, w ∈ LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j₀ := fun w =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 w.2 k
  have le : ∀ j, LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j ≤ LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j ⊓
      LB.wchart M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) j₀ := fun j w hw => ⟨hw, all w⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb M (fun k => (LB.wchart M φ j₀).ι ≫ φ k) ε).g j j₀)⟩,
    isGen_of_gm _ fun w j j' h h' => ?_⟩
  exact ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j j₀ h (all w))).trans
    ((trF_trans hM _ ε (𝟙 _) w h h' (all w)).symm.trans (congrArg _
      ((gm_res _ w (le j') h' _).trans (gm_linComb M _ ε (𝟙 _) w j' j₀ h' (all w))).symm))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

include c in
theorem exists_theta {k : ℕ} {T : Over S} {x : T ⟶ A} (hx : x ^ k = 1) {K : Type} [Fintype K] {φ : K → (T.left ⟶ A.left)}
    {ε : K → ℤ} (v : LB.Gen (LB.LinComb L.L φ ε)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (1 : T ⟶ A).left ^ (k : ℤ) * h x.left ^ (-(k : ℤ))) : ∃ θ : ThetaGrp A L.L k T, θ.pt = x := by
  obtain ⟨t, ht, -⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ x) (snd T A) k
  obtain ⟨u, hu, -⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (translPt A x).left]) (ε' := ![(k : ℤ), -(k : ℤ)])
    (fun U _ h => by
      have p := hF U fun q => h ((fst T A).left ≫ q)
      rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one] at p
      refine (prod_sum₂ (K := K) (K' := Fin 8) (U := U) _ p (Fin.prod_univ_eight _)).trans ?_
      rw [Fin.prod_univ_two, translPt_eq]
      simp only [Sum.elim_inr, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← MonObj.comp_pow, hx, MonObj.comp_one, _root_.one_mul (1 : T ⊗ A ⟶ A), _root_.one_mul (snd T A)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ v (fst T A).left) t)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hv _) ht)
  exact ⟨⟨x, u, hu⟩, rfl⟩

theorem exists_weil {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) : ∃ w : Γ(T.left, ⊤)ˣ,
    ∀ (T' : Over S) (σ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → gm σ.left z ⊤ w =
      cubN (cubV c z J) k 1 (σ ≫ y) (σ ≫ x) * (cubN (cubV c z J) k 1 (σ ≫ x) (σ ≫ y))⁻¹ := by
  obtain ⟨t, ht, vt⟩ := exists_cubN c (1 : T ⟶ A) y x k
  obtain ⟨t', ht', vt'⟩ := exists_cubN c (1 : T ⟶ A) x y k
  obtain ⟨u, -, vu⟩ := exists_gen L.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 8) (K' := Fin 8) (U := U) _ (Fin.prod_univ_eight _)
        (prod_neg _ _ (Fin.prod_univ_eight _))).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inr, Sum.elim_inl, Matrix.cons_val]
      rw [hx, hy, _root_.one_mul (1 : T ⟶ A), mul_comm y x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (LB.mulGen L.L _ _ _ _ t (LB.invGen L.L _ _ t')) (mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht'))
  have le : (⊤ : T.left.Opens) ≤ LB.wchart L.L (PEmpty.elim : PEmpty → (T.left ⟶ A.left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (u.s PEmpty.elim), fun T' σ z J hJ => (gm_res σ.left z le trivial _).trans
    ((val_of u σ.left z J PEmpty.elim fun k => k.elim).symm.trans ?_)⟩
  rw [vu _ _ z J hJ, val_mul hJ, val_inv, vt _ σ z J hJ, vt' _ σ z J hJ, MonObj.comp_one]

def thG {k : ℕ} {T : Over S} (W : ThetaGrp A L.L k T) :
    LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (translPt A W.pt).left] ![(k : ℤ), -(k : ℤ)]) := W.φ

theorem thG_mul (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (W W' : ThetaGrp A L.L k T)
    (hW : W.pt ^ k = 1) (hW' : W'.pt ^ k = 1) {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J} (hJ : Good L.L z J) :
    val (LB.mulGen L.L _ _ _ _ (thG W) (LB.pullGen L.L _ _ (thG W') (translT A W.pt).left)) (lift σ y).left z J =
      val (thG W) (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W.pt) y *
        (val (thG W') (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W'.pt) ((σ ≫ W.pt) * y)) := by
  have v : ∀ (W : ThetaGrp A L.L k T), W.pt ^ k = 1 → ∀ y : T' ⟶ A, val (thG W) (lift σ y).left z J =
      val (thG W) (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ W.pt) y := fun W hW y =>
    val_theta c hG hA hW (thG W) W.isGen (fun V _ h => by
      rw [Fin.prod_univ_two]
      show h _ ^ (k : ℤ) * h _ ^ (-(k : ℤ)) = _
      rw [zpow_neg, zpow_natCast, zpow_natCast]; rfl) σ y hJ
  rw [val_mul hJ, val_pull hJ, ← Over.comp_left, lift_transl, v W hW y, v W' hW' (_ * y)]

theorem comm_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (θ θ' : ThetaGrp A L.L k T)
    (hx : θ.pt ^ k = 1) (hy : θ'.pt ^ k = 1) (e : Γ(T.left, ⊤)ˣ) {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J}
    (hJ : Good L.L z J) :
    val (LB.mulGen L.L _ _ _ _ (thG θ) (LB.pullGen L.L _ _ (thG θ') (translT A θ.pt).left)) (lift σ y).left z J =
      val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (thG θ') (LB.pullGen L.L _ _ (thG θ) (translT A θ'.pt).left))
        (constGen A L.L e)) (lift σ y).left z J ↔ gm σ.left z ⊤ e =
      cubN (cubV c z J) k 1 (σ ≫ θ'.pt) (σ ≫ θ.pt) * (cubN (cubV c z J) k 1 (σ ≫ θ.pt) (σ ≫ θ'.pt))⁻¹ := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have pk : ∀ {x : T ⟶ A}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, h, MonObj.comp_one]
  have hm : (lift σ y).left z ∈ LB.wchart L.L (PEmpty.elim : PEmpty → ((T ⊗ A).left ⟶ A.left)) PEmpty.elim :=
    Set.mem_iInter.2 fun k => k.elim
  have vc : val (constGen A L.L e) (lift σ y).left z J = gm σ.left z ⊤ e := by
    rw [val_of _ _ z J PEmpty.elim fun k => k.elim]
    refine (gm_res (lift σ y).left z le_top hm _).trans ((gm_pull (lift σ y).left (fst T A).left z ⊤ trivial e).trans ?_)
    rw [← Over.comp_left, lift_fst]
  rw [thG_mul c hG hA θ θ' hx hy σ y hJ, val_mul hJ, thG_mul c hG hA θ' θ hy hx σ y hJ, vc]
  have a₁ := cubN_right C (pk hx) (σ ≫ θ'.pt) y
  have a₂ := cubN_right C (pk hy) (σ ≫ θ.pt) y
  rw [C.s01] at a₂
  have E := fun {p q : (T'.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have b₁ := E a₁
  have b₂ := E a₂
  simp only [ofMul_mul] at b₁ b₂
  refine ⟨fun h => Additive.ofMul.injective ?_, fun h => Additive.ofMul.injective ?_⟩
  · have h' := E h
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    linear_combination (norm := abel) b₂ - b₁ - h'
  · have h' := E h
    simp only [ofMul_mul, ofMul_inv] at h' ⊢
    linear_combination (norm := abel) b₂ - b₁ - h'

theorem weilIs_iff (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} {x y : T ⟶ A} (hx : x ^ k = 1)
    (hy : y ^ k = 1) {w : Γ(T.left, ⊤)ˣ} (hw : ∀ (T' : Over S) (σ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → gm σ.left z ⊤ w =
      cubN (cubV c z J) k 1 (σ ≫ y) (σ ≫ x) * (cubN (cubV c z J) k 1 (σ ≫ x) (σ ≫ y))⁻¹) (e : Γ(T.left, ⊤)ˣ) :
    WeilIs A L.L k x y e ↔ e = w := by
  have pk : ∀ {T' : Over S} (σ : T' ⟶ T) {x : T ⟶ A}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun σ _ h => by
    rw [← MonObj.comp_pow, h, MonObj.comp_one]
  constructor
  · refine fun h => unit_ext fun p _ => ?_
    obtain ⟨V, hV, ⟨θ, θ', h₁, h₂⟩, hc⟩ := h p
    let z : (overRes V).left := ⟨p, hV⟩
    choose J hJ using fun ψ : (overRes V).left ⟶ A.left => exists_chart L.isLB (ψ z)
    have e₁ := (comm_val c hG hA θ θ' (h₁ ▸ pk _ hx) (h₂ ▸ pk _ hy) (unitRes V e) (𝟙 _) 1 hJ).1
      (val_corr hJ (hc θ θ' h₁ h₂) _)
    rw [Category.id_comp, Category.id_comp, h₁, h₂, ← hw _ (overResι V) z J hJ] at e₁
    exact gm_inj V.ι z (U := ⊤) (U' := ⊤) trivial trivial (((gm_pull (𝟙 _) V.ι z ⊤ trivial e).trans (by rw [Category.id_comp])).symm.trans e₁)
  · rintro rfl p
    obtain ⟨V₁, hV₁, v₁, hv₁⟩ := exists_local_gen L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, x.left] ![(k : ℤ), -(k : ℤ)] p
    obtain ⟨V₂, hV₂, v₂, hv₂⟩ := exists_local_gen L.isLB (K := Fin 2) ![(1 : T ⟶ A).left, y.left] ![(k : ℤ), -(k : ℤ)] p
    have ex : ∀ (W : T.left.Opens) (le : V₁ ⊓ V₂ ≤ W) (q : T ⟶ A), q ^ k = 1 → ∀ v : LB.Gen (LB.LinComb L.L
        (fun i => W.ι ≫ (![(1 : T ⟶ A).left, q.left] : Fin 2 → _) i) ![(k : ℤ), -(k : ℤ)]), v.IsGen →
        ∃ θ : ThetaGrp A L.L k (overRes (V₁ ⊓ V₂)), θ.pt = overResι (V₁ ⊓ V₂) ≫ q := fun W le q hq v hv =>
      exists_theta c (pk _ hq) (LB.pullGen L.L _ _ v (T.left.homOfLE le)) (pullGen_isGen _ _ _ _ hv _) fun U _ h => by
        rw [Fin.prod_univ_two, ← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, ← MonObj.comp_one (overResι (V₁ ⊓ V₂))]
        rfl
    obtain ⟨θ₁, e₁⟩ := ex V₁ inf_le_left x hx v₁ hv₁
    obtain ⟨θ₂, e₂⟩ := ex V₂ inf_le_right y hy v₂ hv₂
    refine ⟨V₁ ⊓ V₂, ⟨hV₁, hV₂⟩, ⟨θ₁, θ₂, e₁, e₂⟩, fun θ θ' h₁ h₂ => corr_of_val L.isLB fun z J hJ => ?_⟩
    have i₁ : (lift (fst (overRes (V₁ ⊓ V₂)) A) (snd _ A)).left = 𝟙 _ := by
      rw [lift_fst_snd]; rfl
    have key := (comm_val c hG hA θ θ' (h₁ ▸ pk _ hx) (h₂ ▸ pk _ hy) (unitRes (V₁ ⊓ V₂) e) (fst _ A) (snd _ A) hJ).2 (by
      rw [h₁, h₂, ← Category.assoc, ← Category.assoc, ← hw _ (fst _ A ≫ overResι (V₁ ⊓ V₂)) z J hJ]
      exact gm_pull _ (V₁ ⊓ V₂).ι z ⊤ trivial e)
    rw [i₁] at key
    exact key

theorem ros_pair (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (n : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ u (zero2 A)) (LB.oneGen L.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L.L z J) {k : ℕ} {x y : T ⟶ A} (hx : x ^ k = 1) (hy : y ^ k = 1) :
    cubN (cubV c z J) k 1 y (x ≫ f) * (cubN (cubV c z J) k 1 (x ≫ f) y)⁻¹ =
      cubN (cubV c z J) k 1 (y ≫ g) x * (cubN (cubV c z J) k 1 x (y ≫ g))⁻¹ := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have ra := fun x x' y => ros_add c hG hA f g u hu n hJ x x' y
  have u₁ : val₂ u z J (1 : T ⟶ A) y = 1 := by
    have e := (ra 1 1 y).1
    rw [_root_.mul_one, MonObj.one_comp f, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : val₂ u z J x (1 : T ⟶ A) = 1 := by
    have e := (ra 1 1 x).2
    rw [_root_.mul_one, MonObj.one_comp g, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have E := fun {p q : (T.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a : ∀ j, val₂ u z J (x ^ j) y * cubN (cubV c z J) j 1 x (y ≫ g) =
      cubN (cubV c z J) j 1 (x ≫ f) y * val₂ u z J x y ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₁]
    | succ j ih =>
      have e := (ra (x ^ j) x y).1
      rw [MonObj.pow_comp] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ] at ih ⊢
      apply Additive.ofMul.injective
      have b₁ := E ih; have b₂ := E e
      simp only [ofMul_mul] at b₁ b₂ ⊢
      linear_combination (norm := abel) b₁ + b₂
  have b : ∀ j, val₂ u z J x (y ^ j) * cubN (cubV c z J) j 1 (y ≫ g) x =
      cubN (cubV c z J) j 1 y (x ≫ f) * val₂ u z J x y ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₂]
    | succ j ih =>
      have e := (ra (y ^ j) y x).2
      rw [MonObj.pow_comp, C.s01 x, C.s12 _ x, C.s01 (x ≫ f), C.s12 _ (x ≫ f)] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ] at ih ⊢
      apply Additive.ofMul.injective
      have b₁ := E ih; have b₂ := E e
      simp only [ofMul_mul] at b₁ b₂ ⊢
      linear_combination (norm := abel) b₁ + b₂
  have a' := a k
  have b' := b k
  rw [hx, u₁, _root_.one_mul] at a'
  rw [hy, u₂, _root_.one_mul] at b'
  rw [a', b', mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one]

theorem weilRosati (hG : GlobalFnsSt) (hC : CubeSt) : WeilRosatiSt := by
  intro S _ P O _ _ o k T x y a e hx hy
  have := P.isAb.comm
  have := o.hom a
  have := o.hom (star a)
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hC S P ⟨P.L, r, P.isLB, hr⟩ rfl
  obtain ⟨u, hu, n⟩ := exists_ros hG P.isAb P.isLB _ _ (o.rosati a)
  have hx' : (x ≫ o.act a) ^ k = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have hy' : (y ≫ o.act (star a)) ^ k = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨w, hw⟩ := exists_weil c hx' hy
  refine (weilIs_iff c hG P.isAb hx' hy hw e).trans (weilIs_iff c hG P.isAb hx hy' (fun T' σ z J hJ => ?_) e).symm
  rw [hw T' σ z J hJ, ← Category.assoc, ← Category.assoc]
  exact ros_pair c hG P.isAb _ _ u hu n hJ (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubicalLawRight
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

def tup {T : Over S} (x x' y : T ⟶ A) : T ⟶ powObj A 3 := lift x (lift x' (lift y (toUnit T)))

omit [GrpObj A] in
theorem tup_0 {T : Over S} (x x' y : T ⟶ A) : tup x x' y ≫ powPr A (0 : Fin 3) = x := lift_fst _ _

omit [GrpObj A] in
theorem tup_1 {T : Over S} (x x' y : T ⟶ A) : tup x x' y ≫ powPr A (1 : Fin 3) = x' :=
  (lift_snd_assoc _ _ _).trans (lift_fst _ _)

omit [GrpObj A] in
theorem tup_2 {T : Over S} (x x' y : T ⟶ A) : tup x x' y ≫ powPr A (2 : Fin 3) = y :=
  (lift_snd_assoc _ _ _).trans ((lift_snd_assoc _ _ _).trans (lift_fst _ _))

theorem ratio_pow (hp : Function.Surjective (powObj A 3).hom.appTop.hom) {M : LB A.left} (hM : M.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → ((powObj A 3).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((powObj A 3).left ⟶ A.left)}
    {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen)
    (hu' : u'.IsGen) {T : Over S} (x x' y : T ⟶ A) {z : T.left} {J} (hJ : Good M z J) :
    val u (tup x x' y).left z J * val u' (tup (1 : T ⟶ A) 1 1).left z J =
      val u' (tup x x' y).left z J * val u (tup (1 : T ⟶ A) 1 1).left z J := by
  let n : powObj A 3 ⟶ powObj A 3 := tup 1 1 1
  have hn : ∀ {T : Over S} (ρ : T ⟶ powObj A 3), ρ.left ≫ n.left = (tup (1 : T ⟶ A) 1 1).left := fun {T} ρ =>
    congrArg (fun q : T ⟶ powObj A 3 => q.left) ((comp_lift _ _ _).trans (congrArg₂ lift (MonObj.comp_one _)
      ((comp_lift _ _ _).trans (congrArg₂ lift (MonObj.comp_one _) ((comp_lift _ _ _).trans
        (congrArg₂ lift (MonObj.comp_one _) (toUnit_unique _ _)))))))
  have key := gen_unique' hM (fun U _ h => (prod_sum₂ (K := K') (K' := K) (U := U) _ (hF U h)
      (c' := ∏ k, h (n.left ≫ φ k) ^ ε k) rfl).trans (prod_sum₂ (K := K) (K' := K') (U := U) _ rfl
      (hF U fun q => h (n.left ≫ q))).symm) (powObj A 3).hom (tup (1 : 𝟙_ (Over S) ⟶ A) 1 1).left (Over.w _) hp
    (mulGen_isGen _ _ _ _ _ _ _ hu (pullGen_isGen _ _ _ _ hu' n.left))
    (mulGen_isGen _ _ _ _ _ _ _ hu' (pullGen_isGen _ _ _ _ hu n.left)) (fun w I hI => by
      have e := hn (tup (1 : 𝟙_ (Over S) ⟶ A) 1 1)
      exact ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hI _ _ _).trans (congrArg (val u' · w I) e)))).trans
        ((mul_comm _ _).trans ((val_mul hI _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hI _ _ _).trans
          (congrArg (val u · w I) e)))).symm)) _ (tup x x' y).left z J hJ
  rwa [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hn] at key

section

variable [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) {T T' : Over S}

def cubε : thK.{0} → ℤ := thε

def cubφ (x x' y : T ⟶ A) : thK.{0} → (T.left ⟶ A.left) := fun I => (lift x (lift x' y)).left ≫ thφ A (x3 A) I

def cubG (x x' y : T ⟶ A) : LB.Gen (LB.LinComb L.L (cubφ x x' y) cubε) :=
  LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x (lift x' y)).left

theorem prod_cubφ (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I, h (cubφ x x' y I) ^ cubε I = h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ *
      h x.left * h x'.left * h y.left * (h (1 : T ⟶ A).left)⁻¹ := prod_cub x x' y h

theorem cubG_isGen (x x' y : T ⟶ A) : (cubG c x x' y).IsGen := pullGen_isGen _ _ _ _ c.isGen _

theorem val_cubG (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good L.L z J) (x x' y : T ⟶ A) :
    val (cubG c x x' y) ρ.left z J = cubV c z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := val_cub c ρ hJ x x' y

attribute [irreducible] cubG cubφ cubε

end

variable [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (hp : Function.Surjective (powObj A 3).hom.appTop.hom)
  {O : Type} [CommRing O] [StarRing O] (o : OAct O A) {K : Type} [Fintype K] {φ : O → K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
  (w : ∀ a, LB.Gen (LB.LinComb L.L (φ a) ε)) (hw : ∀ a, (w a).IsGen)
  (hW : ∀ a {T : Over S} (x y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U),
    ∏ i, h ((lift x y).left ≫ φ a i) ^ ε i = h (x * (y ≫ o.act (star a))).left * (h x.left)⁻¹ *
      (h (y ≫ o.act (star a)).left)⁻¹ * ((h ((x ≫ o.act a) * y).left)⁻¹ * h (x ≫ o.act a).left * h y.left))
  {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → L.L.ι} (hJ : Good L.L z J)
  (h1 : ∀ a, val₂ (w a) z J (1 : T ⟶ A) 1 = 1)
include c hp hw hW hJ h1

theorem cubical_law_left (a : O) (x x' y : T ⟶ A) :
    val₂ (w a) z J (x * x') y * cubV c z J (x ≫ o.act a) (x' ≫ o.act a) y =
      val₂ (w a) z J x y * val₂ (w a) z J x' y * cubV c z J x x' (y ≫ o.act (star a)) := by
  have := fun a => o.hom a
  have face (x y : T ⟶ A) : cubV c z J 1 x y = 1 := by
    have e := val_corr hJ (c.face 0) (lift x y).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c (lift x y) hJ (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := (K ⊕ K)) (K' := thK.{0}) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (hW a (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3)) U h)) (prod_cubφ (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) h)).trans (Eq.trans (by
      simp only [MonObj.mul_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := K) (K' := thK.{0}) (U := U) _ (hW a ((powPr A (0 : Fin 3)) * (powPr A (1 : Fin 3))) (powPr A (2 : Fin 3)) U h) (prod_cubφ ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (1 : Fin 3)) ≫ o.act a) (powPr A (2 : Fin 3)) h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift ((powPr A (0 : Fin 3)) * (powPr A (1 : Fin 3))) (powPr A (2 : Fin 3))).left) (cubG_isGen c ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (1 : Fin 3)) ≫ o.act a) (powPr A (2 : Fin 3))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3))).left)) (cubG_isGen c (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)))) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, face] at key
  exact key

theorem cubical_law_right (a : O) (x x' y : T ⟶ A) :
    val₂ (w a) z J x (x' * y) * cubV c z J (x ≫ o.act a) x' y =
      val₂ (w a) z J x x' * val₂ (w a) z J x y * cubV c z J x (x' ≫ o.act (star a)) (y ≫ o.act (star a)) := by
  have := fun a => o.hom a
  have face (x y : T ⟶ A) : cubV c z J 1 x y = 1 := by
    have e := val_corr hJ (c.face 0) (lift x y).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c (lift x y) hJ (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := (K ⊕ K)) (K' := thK.{0}) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3)) U h) (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h)) (prod_cubφ (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) h)).trans (Eq.trans (by
      simp only [MonObj.mul_comp, _root_.mul_assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := K) (K' := thK.{0}) (U := U) _ (hW a (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) * (powPr A (2 : Fin 3))) U h) (prod_cubφ ((powPr A (0 : Fin 3)) ≫ o.act a) (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3)) h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) * (powPr A (2 : Fin 3)))).left) (cubG_isGen c ((powPr A (0 : Fin 3)) ≫ o.act a) (powPr A (1 : Fin 3)) (powPr A (2 : Fin 3))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (1 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left)) (cubG_isGen c (powPr A (0 : Fin 3)) ((powPr A (1 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)))) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, face] at key
  exact key

theorem adv_mul (a b : O) (x x' y : T ⟶ A) :
    val₂ (w (a * b)) z J x y = val₂ (w a) z J (x ≫ o.act b) y * val₂ (w b) z J x (y ≫ o.act (star a)) := by
  have := fun a => o.hom a
  have face (x y : T ⟶ A) : cubV c z J 1 x y = 1 := by
    have e := val_corr hJ (c.face 0) (lift x y).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c (lift x y) hJ (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3)) U h) (hW b (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) U h)).trans (Eq.trans (by
      simp only [star_mul, mul_comm (star b), mul_comm a b, o.mul, Category.assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (hW (a * b) (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h).symm))
    (pullGen_isGen _ _ _ _ (hw (a * b)) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw b) (lift (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a))).left)) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, face] at key
  exact key

theorem adv_add (a b : O) (x x' y : T ⟶ A) :
    val₂ (w (a + b)) z J x y * cubV c z J (x ≫ o.act a) (x ≫ o.act b) y =
      val₂ (w a) z J x y * val₂ (w b) z J x y * cubV c z J x (y ≫ o.act (star a)) (y ≫ o.act (star b)) := by
  have := fun a => o.hom a
  have face (x y : T ⟶ A) : cubV c z J 1 x y = 1 := by
    have e := val_corr hJ (c.face 0) (lift x y).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c (lift x y) hJ (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have key := ratio_pow hp L.isLB (fun U _ h => (prod_sum₂ (K := (K ⊕ K)) (K' := thK.{0}) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (hW b (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h)) (prod_cubφ (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star b)) h)).trans (Eq.trans (by
      simp only [star_add, o.add, MonObj.comp_mul, _root_.mul_assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := K) (K' := thK.{0}) (U := U) _ (hW (a + b) (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (prod_cubφ ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3)) h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw (a + b)) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (cubG_isGen c ((powPr A (0 : Fin 3)) ≫ o.act a) ((powPr A (0 : Fin 3)) ≫ o.act b) (powPr A (2 : Fin 3))))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw b) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left)) (cubG_isGen c (powPr A (0 : Fin 3)) ((powPr A (2 : Fin 3)) ≫ o.act (star a)) ((powPr A (2 : Fin 3)) ≫ o.act (star b)))) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, face] at key
  exact key

theorem adv_sy (a : O) (x x' y : T ⟶ A) :
    val₂ (w a) z J x y * val₂ (w (star a)) z J y x * val₂ (w 1) z J x y = val₂ (w 1) z J x y := by
  have := fun a => o.hom a
  have face (x y : T ⟶ A) : cubV c z J 1 x y = 1 := by
    have e := val_corr hJ (c.face 0) (lift x y).left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub c (lift x y) hJ (pzero A _) (x2 A 0) (x2 A 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have key := ratio_pow hp L.isLB (fun U _ h => (hW 1 (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h).trans (Eq.trans (by
      simp only [star_star, mul_comm (powPr A (2 : Fin 3)), mul_comm ((powPr A (2 : Fin 3)) ≫ o.act (star a))]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (prod_sum₂ (K := (K ⊕ K)) (K' := K) (U := U) _ (prod_sum₂ (K := K) (K' := K) (U := U) _ (hW a (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h) (hW (star a) (powPr A (2 : Fin 3)) (powPr A (0 : Fin 3)) U h)) (hW 1 (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3)) U h)).symm))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ (hw a) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) (pullGen_isGen _ _ _ _ (hw (star a)) (lift (powPr A (2 : Fin 3)) (powPr A (0 : Fin 3))).left)) (pullGen_isGen _ _ _ _ (hw 1) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left))
    (pullGen_isGen _ _ _ _ (hw 1) (lift (powPr A (0 : Fin 3)) (powPr A (2 : Fin 3))).left) x x' y hJ
  simp only [val_mul hJ, val_ros _ _ hJ, val_cubG c _ hJ, MonObj.comp_mul, ← Category.assoc, tup_0, tup_1, tup_2,
    MonObj.one_comp, _root_.mul_one, h1, face] at key
  exact key

theorem adv_one (x y : T ⟶ A) : val₂ (w 1) z J x y = 1 := by
  have := adv_mul c hp o w hw hW hJ h1 1 1 x x y
  rw [_root_.mul_one, star_one, o.one, Category.comp_id, Category.comp_id] at this
  exact mul_eq_left.1 this.symm

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

section Germ

variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem mem_wchart_pull {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {h : Y' ⟶ Y} (e : ∀ k, φ' k = h ≫ φ k)
    {j : K → L.ι} {y : Y'} (hy : y ∈ LB.wchart L φ' j) : h y ∈ LB.wchart L φ j := by
  unfold LB.wchart at hy ⊢
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hy ⊢
  intro k
  first
    | simpa [e k] using hy k
    | (have hk := hy k; rw [e k] at hk; exact hk)

theorem exists_gen_pull (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (e : ∀ k, φ' k = h ≫ φ k) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), (t.IsGen → t'.IsGen) ∧ ∀ {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j → gm r z (LB.wchart L φ' j) (t'.s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  refine ⟨LB.pullGen L φ ε t h, fun ht => pullGen_isGen L φ ε t ht h, fun r z j hz => ?_⟩
  exact (gm_res r z _ hz _).trans (gm_pull r h z (LB.wchart L φ j) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k) _)

theorem exists_sec_pull (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (e : ∀ k, φ' k = h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j → gs r z (LB.wchart L φ' j) (s'.f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  refine ⟨pullSec L φ ε s h, fun r z j hz => ?_⟩
  exact (gs_res r z _ hz _).trans (gs_pull r h z (LB.wchart L φ j) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k) _)

theorem val_of_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} {h : Y' ⟶ Y} (e : ∀ k, φ' k = h ≫ φ k)
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε)}
    (H : ∀ {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j → gm r z (LB.wchart L φ' j) (t'.s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j))
    {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t' r z J = val t (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  unfold val
  simp only [Category.assoc]
  rw [H]
  all_goals first
    | rfl
    | (unfold LB.wchart
       simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
       intro k
       simpa using hJ (r ≫ h ≫ φ k))
    | (simp only [LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
       intro k
       simpa using hJ (r ≫ h ≫ φ k))
    | (simp [Category.assoc])
    | (congr 1)

end Germ

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

section Nat

variable {T T' : Over S} (σ : T' ⟶ T)

theorem whisk_snd : (σ ▷ A) ≫ snd T A = snd T' A := by
  first
    | exact whiskerRight_snd σ A
    | (simp; done)

theorem translPt_whisk (x : T ⟶ A) : (σ ▷ A) ≫ translPt A x = translPt A (σ ≫ x) := by
  first
    | (simp only [translPt, comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]; done)
    | (simp [translPt]; done)
    | (unfold translPt; rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd])

theorem transl_whisk (x : T ⟶ A) : translT A (σ ≫ x) ≫ (σ ▷ A) = (σ ▷ A) ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp [translT, translPt_whisk]

theorem neg_whisk : negT A T' ≫ (σ ▷ A) = (σ ▷ A) ≫ negT A T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [negT]
  · simp [negT]

theorem mul_whisk (N : ℕ) : mulT A T' N ≫ (σ ▷ A) = (σ ▷ A) ≫ mulT A T N := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [mulT]
  · first
      | (simp [mulT, comp_pow]; done)
      | (simp [mulT]; done)
      | (simp only [mulT, Category.assoc, whiskerRight_snd, lift_snd]
         induction N with
         | zero => simp
         | succ n ih => simp [pow_succ, comp_mul, ih])

end Nat

def PullRel (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (s : LB.Sec (LPow A L a T))
    (s' : LB.Sec (LPow A L a T')) : Prop :=
  ∀ {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι), r z ∈ (LPow A L a T').U j →
    gs r z ((LPow A L a T').U j) (s'.f j) = gs (r ≫ h.left) z ((LPow A L a T).U j) (s.f j)

theorem exists_pullRel (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) : ∃ s' : LB.Sec (LPow A L a T'), PullRel L a h s s' :=
  exists_sec_pull _ _ s h.left _ fun _ => by rw [← Over.comp_left, hh]

theorem twist_pull {L : LB A.left} {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {ψ' : T' ⊗ A ⟶ T' ⊗ A} {m' : T' ⊗ A ⟶ A}
    {hm' : ψ' ≫ snd T' A = m'} (hψ : ψ' ≫ h = h ≫ ψ) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b])}
    (hα : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 2 → L.ι),
      r z ∈ LB.wchart L ![(snd T' A).left, m'.left] j →
        gm r z (LB.wchart L ![(snd T' A).left, m'.left] j) (α'.s j) =
          gm (r ≫ h.left) z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j))
    {s : LB.Sec (LPow A L b T)} {s₁ : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L b T')}
    {s₁' : LB.Sec (LPow A L a T')} (hs : PullRel L b h s s') (hs₁ : PullRel L a h s₁ s₁')
    (tw : IsTwistPull A L ψ m hm a b α s s₁) : IsTwistPull A L ψ' m' hm' a b α' s' s₁' := by
  have e1 : h.left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, hh]
  have e2 : h.left ≫ m.left = m'.left := by
    rw [← Over.comp_left, ← hm, ← hm', ← Category.assoc, ← hψ, Category.assoc, hh]
  have e : ∀ k, (![(snd T' A).left, m'.left] : Fin 2 → _) k = h.left ≫ (![(snd T A).left, m.left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · exact e1.symm
    · exact e2.symm
  have eψ : ψ'.left ≫ h.left = h.left ≫ ψ.left := by rw [← Over.comp_left, hψ, Over.comp_left]
  intro j
  refine fn_ext fun y hy => ?_
  have hy' := mem_wchart_pull e hy
  have t1 := congrArg (gs h.left y (LB.wchart L ![(snd T A).left, m.left] j)) (tw j)
  erw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_unit _ y _ hy', gs_res _ y _ hy',
    gs_pull h.left ψ.left y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
      (chart_le_pull A L ψ m hm j hy')] at t1
  erw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_unit _ y _ hy, gs_res _ y _ hy,
    gs_pull (𝟙 _) ψ'.left y (LB.wchart L (fun _ : Fin 1 => (snd T' A).left) (fun _ => j 1))
      (chart_le_pull A L ψ' m' hm' j hy), hs₁ _ y _ (chart_le_zero A L m' j hy), hα _ y j hy,
    hs _ y _ (chart_le_pull A L ψ' m' hm' j hy)]
  erw [eψ]
  exact t1

section Theta

variable {L : LB A.left} {k : ℤ}

theorem val_powGenT {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ j₀ : Fin n, val θ.φ (r ≫ (translT A (θ.pt ^ (j₀ : ℕ))).left) z J := by
  have e : ∀ j₀ : Fin n, val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j₀ : ℕ))).left) r z J =
      val θ.φ (r ≫ (translT A (θ.pt ^ (j₀ : ℕ))).left) z J := fun j₀ => val_pull hJ _ _ _
  simp only [← e]
  simp only [val, powGen]
  exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun j₀ _ => gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _)

theorem val_symGen {T : Over S} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (symGen A L k θ nu) r z J = val θ.φ (r ≫ (translT A θ.pt⁻¹).left) z J * val nu r z J *
      (val θ.φ (r ≫ (negT A T).left) z J * (val nu (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  unfold symGen
  exact (val_mul hJ _ _ r).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r) rfl))
    ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r) ((val_inv _ r).trans (congrArg (·⁻¹) (val_pull hJ _ _ r))))))

theorem eθ {T T' : Over S} (σ : T' ⟶ T) (x : T ⟶ A) :
    ∀ kk, (![(snd T' A).left, (translPt A (σ ≫ x)).left] : Fin 2 → _) kk =
      (σ ▷ A).left ≫ (![(snd T A).left, (translPt A x).left] : Fin 2 → _) kk := by
  intro kk
  fin_cases kk
  · simp [← Over.comp_left]
  · simp [← Over.comp_left, translPt_whisk]

theorem symLift_pull (hL : L.IsLB) {T T' : Over S} (σ : T' ⟶ T) {n : ℕ} {x : T ⟶ A} {θ : ThetaGrp A L k T}
    (hθ : SymLift A L k n x θ) (φ' : LB.Gen (thetaLB A L k (σ ≫ θ.pt))) (gφ' : φ'.IsGen)
    (hv : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι}, Good L z J →
      val φ' r z J = val θ.φ (r ≫ (σ ▷ A).left) z J) :
    SymLift A L k n (σ ≫ x) ⟨σ ≫ θ.pt, φ', gφ'⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · show σ ≫ θ.pt = σ ≫ x
    rw [hθ.pt_eq]
  · refine corr_of_val hL fun y J hJ => ?_
    have c := val_corr hJ hθ.pow_eq (σ ▷ A).left
    rw [val_powGenT θ n _ y hJ, val_one] at c
    rw [val_powGenT _ n _ y hJ, val_one, ← c]
    refine Finset.prod_congr rfl fun j₀ _ => ?_
    have m : (𝟙 _ ≫ (translT A ((σ ≫ θ.pt) ^ (j₀ : ℕ))).left) ≫ (σ ▷ A).left =
        (σ ▷ A).left ≫ (translT A (θ.pt ^ (j₀ : ℕ))).left := by
      rw [Category.id_comp, ← MonObj.comp_pow, ← Over.comp_left, ← Over.comp_left, transl_whisk]
    exact (hv _ y hJ).trans (by rw [m])
  · obtain ⟨nu, gnu, cnu⟩ := hθ.sym
    have e1 : (σ ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whisk_snd]
    have e2 : (σ ▷ A).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left := by
      rw [← Over.comp_left, ← Category.assoc, whisk_snd]
    have eN : ∀ kk, (![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) kk =
        (σ ▷ A).left ≫ (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) kk := by
      intro kk; fin_cases kk
      · exact e1.symm
      · exact e2.symm
    obtain ⟨nu', gnu', Hnu⟩ := exists_gen_pull (L := L) _ ![k, -k] nu (σ ▷ A).left _ eN
    refine ⟨nu', gnu' gnu, corr_of_val hL fun y J hJ => ?_⟩
    have c := val_corr hJ cnu (σ ▷ A).left
    rw [val_symGen θ nu _ y hJ, val_one] at c
    rw [val_symGen _ nu' _ y hJ, val_one, ← c]
    have m1 : (𝟙 _ ≫ (translT A (σ ≫ θ.pt)⁻¹).left) ≫ (σ ▷ A).left = (σ ▷ A).left ≫ (translT A θ.pt⁻¹).left := by
      rw [Category.id_comp, ← GrpObj.comp_inv, ← Over.comp_left, ← Over.comp_left, transl_whisk]
    have m3 : (𝟙 _ ≫ (negT A T').left) ≫ (σ ▷ A).left = (σ ▷ A).left ≫ (negT A T).left := by
      rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, neg_whisk]
    have v1 := hv (𝟙 _ ≫ (translT A (σ ≫ θ.pt)⁻¹).left) y hJ
    have v2 := hv (𝟙 _ ≫ (negT A T').left) y hJ
    have v3 := val_of_pull eN Hnu (𝟙 _) y hJ
    have v4 := val_of_pull eN Hnu (𝟙 _ ≫ (translT A (σ ≫ θ.pt)⁻¹).left) y hJ
    rw [m1] at v1 v4
    rw [m3] at v2
    rw [Category.id_comp] at v3
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) v1 v3) (congrArg₂ (· * ·) v2 (congrArg (·⁻¹) v4))

end Theta

variable [IsCommMonObj A]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
