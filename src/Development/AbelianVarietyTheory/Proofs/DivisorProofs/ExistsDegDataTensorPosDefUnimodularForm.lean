module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipallyPolarisedPowerUnimodularForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiPosTendstoZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTauBimultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Interchange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.PolTensBimult

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TensCub

theorem interchange {U X : Type} [CommGroup U] [AddCommGroup X] (t : X → X → U) (hs : ∀ u v, t u v = t v u)
    (hc : ∀ u u' v, t u' v * (t (u + u') v)⁻¹ * t u v = t v u' * (t (u + v) u')⁻¹ * t u u') (x x' y y' : X) :
    t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹ := by
  have h₁ := hc y y' (x + x')
  have h₂ := hc x' y' (x + y)
  have h₃ := hc x x' y
  rw [hs (y + y'), hs y' (x + x'), hs y (x + x')] at h₁
  rw [hs (x' + y'), hs y' (x + y), hs x' (x + y), show x' + (x + y) = y + (x + x') by abel] at h₂
  rw [hs y x'] at h₃
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  have k₃ := congrArg Additive.ofMul h₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at k₁ k₂ k₃ ⊢
  rw [← sub_eq_zero] at k₁ k₂ k₃ ⊢
  have k := congrArg₂ (· - ·) (congrArg₂ (· - ·) k₂ k₁) k₃
  simp only [sub_zero] at k
  rw [← k]
  abel

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (h0 : t 0 0 = 1)
    (ht : ∀ x x' y y', t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  have hτ' : ∀ u v, τ' u v = O (u + v) * (O u)⁻¹ * (O v)⁻¹ * O 0 *
      ∏ i, ∏ j, (t (e u i + e u j) (e v i + e v j) * (t (e u i) (e v i))⁻¹ * (t (e u j) (e v j))⁻¹) ^ W i j := by
    intro u v
    rw [hτ, hr']
    simp only [hψ, map_add (f := _), Pi.add_apply, map_zero, Pi.zero_apply, h0, one_zpow, Finset.prod_const_one, ← ht (e u _) (e v _)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, ofMul_one]
    abel
  rw [eq_mul_inv_of_mul_eq hc, hτ', hτ', hτ']
  simp only [Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply,
    add_zero, h0]
  have e1 : ∀ i j, e a i + e a j + (e a' i + e a' j) = e a i + e a' i + (e a j + e a' j) := fun i j => by abel
  simp only [e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul, ofMul_one, smul_zero, Finset.sum_const_zero]
  abel

theorem cubV_prod (hG : GlobalFnsSt) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {M' : RigLB A} {M : RigLB B} (c' : CubicalStr A M') (c : CubicalStr B M) {N : Type} [Fintype N]
    (P : N → (A ⟶ B)) (hP : ∀ k, IsMonHom (P k)) (φ : N → (A.left ⟶ B.left)) (hφ : ∀ k, (P k).left = φ k) (n : N → ℤ)
    (w : LB.Iso M'.L (LB.LinComb M.L φ n)) (hw : w.IsGen) {T : Over S} (z : T.left) (J J') (hJ : Good M.L z J)
    (hJ' : Good M'.L z J') (x x' y : T ⟶ A) (om : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ)
    (hom : om = fun p => bwg w p.left z (fun k => J (p.left ≫ φ k)) (J' p.left)) :
    cubV c' z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y *
      (om 1)⁻¹) = ∏ k, cubV c z J (x ≫ P k) (x' ≫ P k) (y ≫ P k) ^ n k := by
  subst hom
  let ρ : N → ((G3 A).left ⟶ (G3 B).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ A (x3 A) a ≫ φ k = ρ k ≫ thφ B (x3 B) a := fun k a => by
    rw [← hφ k]
    letI := hP k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over S} (a b c : T ⟶ A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := φ) (εp := n) M.isLB M'.isLB w hw (ε := thε) hψ
    c'.isGen c.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV c' (T := 𝟙_ (Over S)) s I') := isCub_cubV c' hI'
      have C : IsCub (cubV c (T := 𝟙_ (Over S)) s I) := isCub_cubV c hI
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A) 1 1
        (fun q => bwg w q s (fun i => I (q ≫ φ i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := hP k
      have o : (1 : 𝟙_ (Over S) ⟶ A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ n k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bwg w q z (fun i => J (q ≫ φ i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ Q D' r W pr xe T hn a a' b
  obtain ⟨hpr, -, hcp, w, hw, hpsi⟩ := T
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.M.L y J :=
    ⟨fun ψ => (exists_chart Q.M.isLB (ψ y)).choose, fun ψ => (exists_chart Q.M.isLB (ψ y)).choose_spec⟩
  let P : (Fin r × Fin r) × Fin 4 → (D'.P.A ⟶ Q.B) := fun k => ![pr k.1.1 * pr k.1.2, pr k.1.1, pr k.1.2, 1] k.2
  have hPh : ∀ k, IsMonHom (P k) := by
    rintro ⟨⟨i, j⟩, m⟩
    have := hpr i
    have := hpr j
    fin_cases m
    · exact GlobalTheory.Serre.isMonHom_mul _ _
    · exact hpr i
    · exact hpr j
    · exact GlobalTheory.Serre.isMonHom_one
  have hPl : ∀ k, (P k).left = tensφ pr k := by
    rintro ⟨⟨i, j⟩, m⟩
    fin_cases m <;> rfl
  have key := cubV_prod hG D'.P.isAb D'.cub Q.cub P hPh (tensφ pr) hPl (tensε W) w hw (T := TK R) y J J' hJ hJ'
    (cP D' _ a) (cP D' _ a') (cP D' _ b) _ rfl
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left) * ∏ i, ∏ j, val (Q.tau (xe u i) (xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => hpsi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have c0 : cP D' (TK R) 0 = 1 := by
    have := cPoint_add D' (TK R) 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hP : ∀ u k, cP D' (TK R) u ≫ P k = toUnit (TK R) ≫ Q.c (![xe u k.1.1 + xe u k.1.2, xe u k.1.1, xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ pr i = toUnit (TK R) ≫ Q.c (xe u i) := fun i => by
      rw [cP, Category.assoc, hcp]
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · show cP D' (TK R) u ≫ (pr i * pr j) = toUnit (TK R) ≫ Q.c (xe u i + xe u j)
      rw [MonObj.comp_mul, e, e, Q.c_add, MonObj.comp_mul]
    · exact e i
    · exact e j
    · show cP D' (TK R) u ≫ 1 = toUnit (TK R) ≫ Q.c 0
      rw [q0, MonObj.comp_one, MonObj.comp_one]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV Q.cub y J (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v) = val (Q.tau u v) (𝟙 _) y J * val (Q.tau u' v) (𝟙 _) y J * (val (Q.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← Q.tau_add u u' v y J hJ, mul_comm, inv_mul_cancel_left]
  have hI := interchange (fun u v => val (Q.tau u v) (𝟙 _) y J) (fun u v => Q.tau_symm u v y J hJ) (fun u u' v => by
    have := (isCub_cubV Q.cub hJ).s12 (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v)
    rw [hC, hC, _root_.mul_assoc, _root_.mul_assoc, mul_comm, mul_comm (val (Q.tau u _) (𝟙 _) y J)] at this
    first | exact this | exact this.symm)
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0] at key
  refine alg W xe
    (fun u => bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (Q.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b
    (Q.val_tau_zero 0 y J hJ) hI hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.PolTensBimult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTauBimultiplicative
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPolBimult

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hpsi hn
  exact GlobalTheory.PolTensBimult.main R (base_of_isCN hR) Q D' W pr xe ⟨hpr, ⟨hlim⟩, hc, w, hw, hpsi⟩ hn

end GlobalTheory.TensPolBimult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTauBimultiplicativeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_tau_bimultiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  first | exact @GlobalTheory.TensPolBimult.main | exact GlobalTheory.TensPolBimult.main | (intros; apply GlobalTheory.TensPolBimult.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiEven
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiEven
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolTensEven

open TopologicalSpace GlobalTheory.TensEven

section Gen

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {P : Type} [Fintype P] {pr : P → (X' ⟶ X)} {εp : P → ℤ}
  {K : Type} [Fintype K] {Q : Type} [Fintype Q] {P₂ : Type} [Fintype P₂]

def wG (φ' : K → (Y ⟶ X')) {φ : Q → (Y₀ ⟶ X)} (ρ : P₂ → (Y ⟶ Y₀)) (I : (Y ⟶ X) → M.ι) (jM : K → M'.ι) : Y.Opens :=
  LB.wchart (LB.LinComb M pr εp) φ' (fun a i => I (φ' a ≫ pr i)) ⊓ LB.wchart M' φ' jM ⊓
    LB.wchart M (fun q : P₂ × Q => ρ q.1 ≫ φ q.2) (fun q => I (ρ q.1 ≫ φ q.2))

theorem chart_leG {φ : Q → (Y₀ ⟶ X)} (ρ : P₂ → (Y ⟶ Y₀)) (I : (Y ⟶ X) → M.ι) (p : P₂) :
    LB.wchart M (fun q : P₂ × Q => ρ q.1 ≫ φ q.2) (fun q => I (ρ q.1 ≫ φ q.2)) ≤
      ρ p ⁻¹ᵁ LB.wchart M φ (fun k => I (ρ p ≫ φ k)) := fun _ hy =>
  Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (p, k)

def ratioG (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : Q → (Y₀ ⟶ X)} {δ : Q → ℤ}
    (ρ : P₂ → (Y ⟶ Y₀)) (ν : P₂ → ℤ) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ δ))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (I : (Y ⟶ X) → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bwE w (r ≫ φ' a) z (fun i => I (φ' a ≫ pr i)) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ p, gm (r ≫ ρ p) z (LB.wchart M φ (fun k => I (ρ p ≫ φ k))) (t.s (fun k => I (ρ p ≫ φ k))) ^ ν p)⁻¹

theorem exists_ratioG (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : Q → (Y₀ ⟶ X)}
    {δ : Q → ℤ} (ρ : P₂ → (Y ⟶ Y₀)) (ν : P₂ → ℤ) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ δ))
    (I : (Y ⟶ X) → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM → gm r z _ u = ratioG w ρ ν t' t r z I jM := by
  refine ⟨@id (Γ(Y, wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM)ˣ)
      (res inf_le_left ((LB.linCombIso w φ' ε).s ((fun a i => I (φ' a ≫ pr i)), jM)) *
        res (inf_le_left.trans inf_le_right) (t'.s jM) *
      (∏ p, res (inf_le_right.trans (chart_leG ρ I p)) (pullU (ρ p) _ (t.s (fun k => I (ρ p ≫ φ k)))) ^ ν p)⁻¹),
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_res r z _ hz _).trans (gm_linCombIsoE w φ' ε r z _ jM hz.1)) (gm_res r z _ hz _))) ((map_inv _ _).trans
      (congrArg (·⁻¹) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun p _ => ?_)))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ ν p)
    ((gm_res r z _ hz _).trans (gm_pull r (ρ p) z _ (chart_leG ρ I p hz.2) _)))

end Gen

section Gen2

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {P : Type} [Fintype P] {pr : P → (X' ⟶ X)} {εp : P → ℤ}
  {K : Type} [Fintype K] {Q : Type} [Fintype Q] {P₂ : Type} [Fintype P₂]

theorem ratioG_trans (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    {φ : Q → (Y₀ ⟶ X)} {δ : Q → ℤ} {ρ : P₂ → (Y ⟶ Y₀)} {ν : P₂ → ℤ}
    (hF : FormEq (fun q : K × P => φ' q.1 ≫ pr q.2) (fun q => ε q.1 * εp q.2) (fun q : P₂ × Q => ρ q.1 ≫ φ q.2)
      (fun q => ν q.1 * δ q.2))
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ δ)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {I I' : (Y ⟶ X) → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I jM) (h' : r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ I' jM') :
    ratioG w ρ ν t' t r z I jM = ratioG w ρ ν t' t r z I' jM' := by
  have e₁ : ∀ a, bwE w (r ≫ φ' a) z (fun i => I (φ' a ≫ pr i)) (jM a) = _ := fun a =>
    bwE_trans w hw (r ≫ φ' a) z (jN' := fun i => I' (φ' a ≫ pr i)) (k' := jM' a)
      (Set.mem_iInter.1 h.1.1 a) (Set.mem_iInter.1 h'.1.1 a) (Set.mem_iInter.1 h.1.2 a) (Set.mem_iInter.1 h'.1.2 a)
  have e₂ := gen_trans ht' r z h.1.2 h'.1.2
  have e₃ : ∀ p, gm (r ≫ ρ p) z (LB.wchart M φ (fun k => I (ρ p ≫ φ k))) (t.s (fun k => I (ρ p ≫ φ k))) = _ :=
    fun p => gen_trans ht (r ≫ ρ p) z (j' := fun k => I' (ρ p ≫ φ k)) (chart_leG ρ I p h.2) (chart_leG ρ I' p h'.2)
  have e₄ : ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (I (φ' a ≫ pr i)) ⊓ M.U (I' (φ' a ≫ pr i)))
        (M.g (I (φ' a ≫ pr i)) (I' (φ' a ≫ pr i))) ^ εp i) ^ ε a =
      ∏ p, trF φ δ (r ≫ ρ p) z (fun k => I (ρ p ≫ φ k)) (fun k => I' (ρ p ≫ φ k)) ^ ν p := by
    have := hF.trF (L := M) r z I I'
    unfold trF at this ⊢
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type] at this
    refine Eq.trans ?_ (this.trans ?_)
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_mul, mul_comm, Category.assoc]
    · refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_mul]
      dsimp only
      rw [mul_comm (δ k), Category.assoc]
  unfold ratioG
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂,
    Finset.prod_congr rfl fun p _ => congrArg (· ^ ν p) (e₃ p)]
  simp only [mul_zpow, Finset.prod_mul_distrib] at e₄ ⊢
  rw [e₄]
  simp only [inv_zpow, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Gen2

section Gen3

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {P : Type} [Fintype P] {pr : P → (X' ⟶ X)} {εp : P → ℤ}
  {K : Type} [Fintype K] {Q : Type} [Fintype Q] {P₂ : Type} [Fintype P₂]

theorem box_uniqueG {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr εp))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : Q → (Y₀ ⟶ X)} {δ : Q → ℤ} {ρ : P₂ → (Y ⟶ Y₀)} {ν : P₂ → ℤ}
    (hF : FormEq (fun q : K × P => φ' q.1 ≫ pr q.2) (fun q => ε q.1 * εp q.2) (fun q : P₂ × Q => ρ q.1 ≫ φ q.2)
      (fun q => ν q.1 * δ q.2))
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ δ)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bwE w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ q, val t (e ≫ ρ q) y J ^ ν q)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ q, val t (r ≫ ρ q) z J ^ ν q := by
  choose u hu using fun q : ((Y ⟶ X) → M.ι) × (K → M'.ι) => exists_ratioG (pr := pr) (εp := εp) w ρ ν t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens) (fun q : ((Y ⟶ X) → M.ι) × (K → M'.ι) =>
      wG (pr := pr) (εp := εp) φ' (φ := φ) ρ q.1 q.2) (fun _ => le_top)
    (fun y _ => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hM (χ y)
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(I, b), ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hI (φ' a ≫ pr i),
        Set.mem_iInter.2 hb⟩, Set.mem_iInter.2 fun q => hI (ρ q.1 ≫ φ q.2)⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratioG_trans w hw hF ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ q, val t (r ≫ ρ q) z J ^ ν q)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ wG (pr := pr) (εp := εp) φ' (φ := φ) ρ (fun χ => J (r ≫ χ)) (fun a => J' (r ≫ φ' a)) :=
      ⟨⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ (r ≫ φ' a ≫ pr i), hJ'.mem _ r⟩,
        hJ.mem (fun q : P₂ × Q => ρ q.1 ≫ φ q.2) r⟩
    have v : ∏ q, val t (r ≫ ρ q) z J ^ ν q = ∏ q, gm (r ≫ ρ q) z (LB.wchart M φ (fun k => J (r ≫ ρ q ≫ φ k)))
        (t.s (fun k => J (r ≫ ρ q ≫ φ k))) ^ ν q := Finset.prod_congr rfl fun q _ =>
      congrArg (· ^ ν q) (val_of t _ z J _ (fun k => by rw [Category.assoc]))
    have vb : ∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a =
        ∏ a, bwE w (r ≫ φ' a) z (fun i => J (r ≫ φ' a ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a := by
      simp only [Category.assoc]
    rw [v, vb]
    have w₁ := (hu ((fun χ => J (r ≫ χ)), (fun a => J' (r ≫ φ' a))) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Gen3

section Spec

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}

def rhoC (pr : Fin r → (D'.P.A ⟶ Q.B)) : (Fin r × Fin r) × Fin 2 → (D'.P.A.left ⟶ (G3 Q.B).left) := fun q =>
  ![(lift (pr q.1.1) (lift (pr q.1.1)⁻¹ (pr q.1.2))).left, (lift (pr q.1.2) (lift (pr q.1.2)⁻¹ (pr q.1.1)⁻¹)).left] q.2

def nuC (W : Matrix (Fin r) (Fin r) ℤ) : (Fin r × Fin r) × Fin 2 → ℤ := fun q => ![W q.1.1 q.1.2, -W q.1.1 q.1.2] q.2

theorem inv_left (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (i : Fin r) :
    (ι[D'.P.A]).left ≫ (pr i).left = ((pr i)⁻¹).left := by
  have := hpr i
  rw [← Over.comp_left, GrpObj.inv_hom, Hom.inv_def]

theorem inv_left_mul (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (i j : Fin r) :
    (ι[D'.P.A]).left ≫ (pr i * pr j).left = ((pr i)⁻¹ * (pr j)⁻¹).left := by
  have := hpr i
  have := hpr j
  rw [← Over.comp_left, MonObj.comp_mul, GrpObj.inv_hom, GrpObj.inv_hom, Hom.inv_def, Hom.inv_def]

theorem inv_left_one : (ι[D'.P.A]).left ≫ (1 : D'.P.A ⟶ Q.B).left = (1 : D'.P.A ⟶ Q.B).left := by
  rw [← Over.comp_left, MonObj.comp_one]

end Spec

section Spec2

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}

theorem cub_pow {T : Over (Sp R)} {U : Type} [CommGroup U] (h : (T.left ⟶ Q.B.left) → U) (g : T.left ⟶ (G3 Q.B).left)
    (n : ℤ) : ∏ I : thK.{0}, h (g ≫ thφ Q.B (x3 Q.B) I) ^ (n * thε I) =
      (∏ I : thK.{0}, h (g ≫ thφ Q.B (x3 Q.B) I) ^ thε I) ^ n := by
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [mul_comm, zpow_mul]

theorem formEq_tens (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (W : Matrix (Fin r) (Fin r) ℤ) :
    FormEq (fun q : Fin 2 × ((Fin r × Fin r) × Fin 4) =>
        (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) q.1 ≫ tensφ pr q.2)
      (fun q => (![1, -1] : Fin 2 → ℤ) q.1 * tensε W q.2)
      (fun q : ((Fin r × Fin r) × Fin 2) × thK.{0} => rhoC pr q.1 ≫ thφ Q.B (x3 Q.B) q.2)
      (fun q => nuC W q.1 * thε q.2) := by
  intro U _ h
  refine (Fintype.prod_prod_type _).trans (Finset.prod_comm.trans ((Fintype.prod_prod_type _).trans ?_))
  refine Eq.trans ?_ ((Fintype.prod_prod_type _).trans (Fintype.prod_prod_type _)).symm
  refine Finset.prod_congr rfl fun ij _ => ?_
  simp only [Fin.prod_univ_two]
  rw [cub_pow, cub_pow]
  simp only [rhoC, nuC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [prod_cub, prod_cub]
  simp only [Fin.prod_univ_four, tensφ, tensε, lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.id_comp]
  rw [inv_left_mul pr hpr, inv_left pr hpr, inv_left pr hpr, inv_left_one]
  rw [mul_inv_cancel (pr ij.1), mul_inv_cancel (pr ij.2), _root_.one_mul (pr ij.2), _root_.one_mul (pr ij.1)⁻¹,
    mul_comm (pr ij.1)⁻¹ (pr ij.2), mul_comm (pr ij.2)⁻¹ (pr ij.1)⁻¹]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, _root_.one_mul, _root_.mul_one, neg_mul, mul_neg, neg_neg, neg_smul,
    smul_add, smul_sub, smul_neg, one_smul]
  abel

end Spec2

section Spec3

variable {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {D' : DegPre R} {r : ℕ}

theorem eta_one (B : Over (Sp R)) [GrpObj B] : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B) = 1 := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem eSec_rhoC (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i)) (p : (Fin r × Fin r) × Fin 2) :
    eSec D'.P.A ≫ rhoC pr p = (lift (1 : 𝟙_ (Over (Sp R)) ⟶ Q.B) (lift 1 1)).left := by
  have h1 : ∀ i, η[D'.P.A] ≫ pr i = 1 := fun i => by
    have := hpr i
    rw [IsMonHom.one_hom, eta_one]
  have h2 : ∀ i, η[D'.P.A] ≫ (pr i)⁻¹ = 1 := fun i => by rw [GrpObj.comp_inv, h1, inv_one]
  obtain ⟨⟨i, j⟩, s⟩ := p
  fin_cases s
  · show (η[D'.P.A]).left ≫ (lift (pr i) (lift (pr i)⁻¹ (pr j))).left = _
    rw [← Over.comp_left, comp_lift, comp_lift, h1, h2, h1]
  · show (η[D'.P.A]).left ≫ (lift (pr j) (lift (pr j)⁻¹ (pr i)⁻¹)).left = _
    rw [← Over.comp_left, comp_lift, comp_lift, h1, h2, h2]

theorem sym_tensP (hG : GlobalFnsSt) (pr : Fin r → (D'.P.A ⟶ Q.B)) (hpr : ∀ i, IsMonHom (pr i))
    (W : Matrix (Fin r) (Fin r) ℤ) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))) (hw : w.IsGen)
    {Z : Scheme.{0}} (q : Z ⟶ D'.P.A.left) (y : Z) {J J'} (hJ : Good Q.M.L y J) (hJ' : Good D'.P.L y J') :
    bwE w (q ≫ (ι[D'.P.A]).left) y (fun k => J ((q ≫ (ι[D'.P.A]).left) ≫ tensφ pr k)) (J' (q ≫ (ι[D'.P.A]).left)) *
      (bwE w q y (fun k => J (q ≫ tensφ pr k)) (J' q))⁻¹ * val D'.sym q y J' =
      ∏ p, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (q ≫ rhoC pr p) y J ^ nuC W p := by
  have pp : ∀ {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) {U : Type} [CommGroup U] (f : (Z ⟶ D'.P.A.left) → U),
      ∏ a : Fin 2, f (r ≫ (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) a) ^
        (![1, -1] : Fin 2 → ℤ) a = f (r ≫ (ι[D'.P.A]).left) * (f r)⁻¹ := fun r U _ f => by
    simp [Fin.prod_univ_two]
  have key := box_uniqueG Q.M.isLB D'.P.isLB w hw (formEq_tens pr hpr W) D'.sym_gen Q.cub.isGen D'.P.A.hom
    (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (fun s I I' hI hI' => by
      have q' := pp (Z := Spec (CommRingCat.of R)) (eSec D'.P.A)
        (fun ψ => bwE w ψ s (fun i => I (ψ ≫ tensφ pr i)) (I' ψ))
      have o : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A :=
        congrArg (fun m => m.left) (GrpObj.one_inv : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A])
      rw [o, mul_inv_cancel] at q'
      have v' := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', Category.id_comp, val_one] at v'
      refine (congrArg₂ (· * ·) q' v').trans (Eq.trans (by simp) (Finset.prod_eq_one fun p _ => ?_).symm)
      rw [eSec_rhoC pr hpr p]
      exact (congrArg (· ^ nuC W p) ((isCub_cubV Q.cub (T := 𝟙_ (Over (Sp R))) hI).face 1 1)).trans (one_zpow _))
    _ q y J J' hJ hJ'
  exact (congrArg₂ (· * ·) (pp q (fun ψ => bwE w ψ y (fun i => J (ψ ≫ tensφ pr i)) (J' ψ))) rfl).symm.trans key

end Spec3

section Main

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_zeroQ (Q : Data R) : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))

theorem c_negQ (Q : Data R) (a : Q.X) : Q.c (-a) = (Q.c a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Q.c_add, neg_add_cancel, c_zeroQ]

theorem pt_negQ (Q : Data R) (a : Q.X) : toUnit (TK R) ≫ Q.c (-a) = (toUnit (TK R) ≫ Q.c a)⁻¹ := by
  rw [c_negQ, GrpObj.comp_inv]

theorem tau_negQ (Q : Data R) (a b : Q.X) (y : (TK R).left) (J) (hJ : Good Q.M.L y J) :
    val (Q.tau (-a) (-b)) (𝟙 _) y J *
      (cubV Q.cub y J (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c (-a)) (toUnit (TK R) ≫ Q.c b) *
        (cubV Q.cub y J (toUnit (TK R) ≫ Q.c b) (toUnit (TK R) ≫ Q.c (-b)) (toUnit (TK R) ≫ Q.c (-a)))⁻¹) =
      val (Q.tau a b) (𝟙 _) y J := by
  have t₁ := Q.tau_add a (-a) b y J hJ
  have t₂ := Q.tau_add b (-b) (-a) y J hJ
  rw [add_neg_cancel, Q.val_tau_zero _ y J hJ, _root_.one_mul] at t₁ t₂
  have s₁ := Q.tau_symm (-b) (-a) y J hJ
  have s₂ := Q.tau_symm b (-a) y J hJ
  apply Additive.ofMul.injective
  have E := fun {p q : ((TK R).left.presheaf.stalk y)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have b₁ := E s₁; have b₂ := E s₂
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ b₁ b₂ ⊢
  linear_combination (norm := abel) a₁ - a₂ - b₁ - b₂

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) →
    IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) →
    ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' →
      val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → D'.PsiEven := by
  intro R _ _ _ _ Q D' r W pr hpr _ xe hc w hw hpsi x
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ using fun ψ : (TK R).left ⟶ Q.B.left => exists_chart Q.M.isLB (ψ y)
  have hJ : Good Q.M.L y J := hJ
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have key := sym_tensP GlobalTheory.globalFns_holds pr hpr W w hw (D'.xK x) y hJ hJ'
  have b₁ := hpsi x y J J' hJ hJ'
  have b₂ := hpsi (-x) y J J' hJ hJ'
  have n : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit (TK R) ≫ D'.c (-x)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  rw [← n] at key
  have hu : ∀ i, (toUnit (TK R) ≫ D'.c x) ≫ pr i = toUnit (TK R) ≫ Q.c (xe x i) := fun i => by
    rw [Category.assoc, hc]
  have hu' : ∀ i, (toUnit (TK R) ≫ D'.c x) ≫ (pr i)⁻¹ = toUnit (TK R) ≫ Q.c (-(xe x i)) := fun i => by
    rw [GrpObj.comp_inv, hu, pt_negQ]
  have vC : ∀ i j, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (D'.xK x ≫ rhoC pr ((i, j), 0)) y J ^
        nuC W ((i, j), 0) * val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t
          (D'.xK x ≫ rhoC pr ((i, j), 1)) y J ^ nuC W ((i, j), 1) =
      (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x i)) (toUnit (TK R) ≫ Q.c (-(xe x i))) (toUnit (TK R) ≫ Q.c (xe x j)) *
        (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x j)) (toUnit (TK R) ≫ Q.c (-(xe x j)))
          (toUnit (TK R) ≫ Q.c (-(xe x i))))⁻¹) ^ W i j := by
    intro i j
    have e₀ : D'.xK x ≫ rhoC pr ((i, j), 0) = (lift (toUnit (TK R) ≫ Q.c (xe x i))
        (lift (toUnit (TK R) ≫ Q.c (-(xe x i))) (toUnit (TK R) ≫ Q.c (xe x j)))).left := by
      show (toUnit (TK R) ≫ D'.c x).left ≫ (lift (pr i) (lift (pr i)⁻¹ (pr j))).left = _
      rw [← Over.comp_left, comp_lift, comp_lift, hu, hu', hu]
    have e₁ : D'.xK x ≫ rhoC pr ((i, j), 1) = (lift (toUnit (TK R) ≫ Q.c (xe x j))
        (lift (toUnit (TK R) ≫ Q.c (-(xe x j))) (toUnit (TK R) ≫ Q.c (-(xe x i))))).left := by
      show (toUnit (TK R) ≫ D'.c x).left ≫ (lift (pr j) (lift (pr j)⁻¹ (pr i)⁻¹)).left = _
      rw [← Over.comp_left, comp_lift, comp_lift, hu, hu', hu']
    rw [e₀, e₁]
    simp only [nuC, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [mul_zpow, inv_zpow, zpow_neg]
    rfl
  have Qe : ∏ p, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (D'.xK x ≫ rhoC pr p) y J ^ nuC W p =
      ∏ i, ∏ j, (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x i)) (toUnit (TK R) ≫ Q.c (-(xe x i)))
          (toUnit (TK R) ≫ Q.c (xe x j)) *
        (cubV Q.cub y J (toUnit (TK R) ≫ Q.c (xe x j)) (toUnit (TK R) ≫ Q.c (-(xe x j)))
          (toUnit (TK R) ≫ Q.c (-(xe x i))))⁻¹) ^ W i j := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => (Fin.prod_univ_two _).trans (vC i j)
  have hn : ∀ i, xe (-x) i = -xe x i := fun i => by rw [map_neg]; rfl
  have E : (∏ i, ∏ j, val (Q.tau (xe (-x) i) (xe (-x) j)) (𝟙 _) y J ^ W i j) *
      ∏ p, val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t (D'.xK x ≫ rhoC pr p) y J ^ nuC W p =
      ∏ i, ∏ j, val (Q.tau (xe x i) (xe x j)) (𝟙 _) y J ^ W i j := by
    rw [Qe, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← mul_zpow, hn, hn, tau_negQ Q (xe x i) (xe x j) y J hJ]
  rw [b₁, b₂]
  exact alg _ _ _ _ _ _ key E

end Main

end GlobalTheory.PolTensEven
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataPsiEvenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_psi_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → D'.PsiEven := by
  first | exact @GlobalTheory.PolTensEven.main | exact GlobalTheory.PolTensEven.main | (intros; apply GlobalTheory.PolTensEven.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TensPol

theorem rig_exists {R : Type} [CommRing R] [IsDomain R] {B : Over (Spec (CommRingCat.of R))} [GrpObj B] {M : LB B.left}
    (hM : M.IsLB) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {A' : Over (Spec (CommRingCat.of R))} [GrpObj A'] {L' : LB A'.left}
    (hL' : L'.IsLB) (pr : Fin r → (A' ⟶ B)) (hpr : ∀ i, IsMonHom (pr i)) (w : LB.Iso L' (LB.LinComb M (tensφ pr) (tensε W)))
    (hw : w.IsGen) : ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ B.left) → M.ι)
      (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good M z J → Good L' z J' →
      val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' *
        gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  have hform : FormEq (X := B.left) (Y := (𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (PEmpty.elim : PEmpty → _) PEmpty.elim
      (GlobalTheory.LamBiext.flatφ (tensφ pr) (fun _ : PUnit => eSec A'))
      (GlobalTheory.LamBiext.flatε (tensε W) (fun _ : PUnit => (1 : ℤ))) := by
    intro U _ h
    simp only [GlobalTheory.LamBiext.flatφ, GlobalTheory.LamBiext.flatε, GlobalTheory.Mum.TensRig.eSec_tensφ pr hpr, _root_.one_mul, Finset.univ_eq_empty,
      Finset.prod_empty, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε]
    simp
  obtain ⟨t, ht, htv⟩ := exists_gen hM hform (LB.oneGen M) (GlobalTheory.Mum.TensRig.oneGen_isGen' _)
  obtain ⟨a, ha, hmaps⟩ := Transport.exists_transport
    (DVR.linComb_isLB L' hL' (fun _ : PUnit => eSec A') (fun _ => 1))
    (DVR.linComb_isLB _ (DVR.linComb_isLB M hM (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A') (fun _ => 1))
    (LB.linCombIso w (fun _ : PUnit => eSec A') (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _)
    (GlobalTheory.LamBiext.nest M (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t)
    (GlobalTheory.LamBiext.nest_isGen ht)
  refine ⟨a, ha, fun z J J' hJ hJ' => ?_⟩
  have hPM := (GlobalTheory.GtCubeCompare.maps_iff_pm w (fun _ : PUnit => eSec A') (fun _ => 1) a _).1 hmaps
  have hp : (toUnit (TK R)).left z ∈ LB.wchart (LB.LinComb M (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (ptK η[A'] ≫ tensφ pr k)
  have hq : (toUnit (TK R)).left z ∈ LB.wchart L' (fun _ : PUnit => eSec A') (fun _ => J' (ptK η[A'])) :=
    Set.mem_iInter.2 fun _ => hJ' (ptK η[A'])
  have E := hPM _ (toUnit (TK R)).left z _ _ hp hq
  have L1 : gm (toUnit (TK R)).left z (LB.wchart (LB.LinComb M (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)))
      ((GlobalTheory.LamBiext.nest M (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t).s
        (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k))) = 1 := by
    refine (gm_res _ z (GlobalTheory.LamBiext.nest_le M (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') _) hp _).trans ?_
    exact (val_of t (toUnit (TK R)).left z J (fun p => J (ptK η[A'] ≫ tensφ pr p.2))
      (fun x => congrArg J (Category.assoc _ _ _).symm)).symm.trans ((htv _ _ z J hJ).trans (val_one _))
  rw [L1, Fintype.prod_unique, zpow_one] at E
  rw [val_pull hJ' a (toUnit (TK R)).left (𝟙 _),
    val_of a _ z J' (fun _ => J' (ptK η[A'])) (fun _ => by rw [Category.id_comp]; rfl), Category.id_comp, mul_comm]
  exact E.symm

end GlobalTheory.Mum.TensPol

noncomputable section
namespace GlobalTheory.Mum.TensPol

variable {R : Type} [CommRing R] [IsDomain R]

theorem formula_trans (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left}
    (pr : Fin r → (B' ⟶ Q.B)) {w : LB.Iso L' (LB.LinComb Q.M.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → Q.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ Q.c (y i)) (z : (TK R).left) (J J₀) (hJ : Good Q.M.L z J)
    (hJ₀ : Good Q.M.L z J₀) (k k₀ : L'.ι) (hk : x.left z ∈ L'.U k) (hk₀ : x.left z ∈ L'.U k₀) :
    gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) * ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z J ^ W i j =
      (gm x.left z _ (L'.g k k₀))⁻¹ * (gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) *
        ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z J₀ ^ W i j) := by
  let H : ((TK R).left ⟶ Q.B.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ => gm ψ z _ (Q.M.L.g (J ψ) (J₀ ψ))
  let F : Fin r → Fin r → ((TK R).left.presheaf.stalk z)ˣ := fun i j =>
    ∏ a, H (lamPts (toUnit (TK R) ≫ Q.c (y i)) (toUnit (TK R) ≫ Q.c (y j)) a) ^ Oε a
  have h₁ : gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), k)) =
      gm x.left z _ ((LB.LinComb Q.M.L (tensφ pr) (tensε W)).g
        (fun a => J (x.left ≫ tensφ pr a)) (fun a => J₀ (x.left ≫ tensφ pr a))) *
      (gm x.left z _ (L'.g k k₀))⁻¹ *
      gm x.left z _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), k₀)) := by
    let L := LB.LinComb Q.M.L (tensφ pr) (tensε W)
    let j := fun a => J (x.left ≫ tensφ pr a)
    let j₀ := fun a => J₀ (x.left ≫ tensφ pr a)
    have hj : x.left z ∈ L.U j := hJ.mem (tensφ pr) x.left
    have hj₀ : x.left z ∈ L.U j₀ := hJ₀.mem (tensφ pr) x.left
    have hV : x.left z ∈ (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) := ⟨⟨hj, hk⟩, ⟨hj₀, hk₀⟩⟩
    have hw' : res (inf_le_left : (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L.U j ⊓ L'.U k) (w.s (j, k)) =
        res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L.U j ⊓ L.U j₀) (L.g j j₀) *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L'.U k ⊓ L'.U k₀) (L'.g k k₀))⁻¹ *
        res (inf_le_right : (L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀) ≤ L.U j₀ ⊓ L'.U k₀) (w.s (j₀, k₀)) :=
      hw (j, k) (j₀, k₀)
    have key := congrArg (gm x.left z ((L.U j ⊓ L'.U k) ⊓ (L.U j₀ ⊓ L'.U k₀))) hw' 
    simp only [map_mul, map_inv, gm_res x.left z _ hV] at key
    rw [gm_res x.left z (U := L.U j ⊓ L'.U k) _ hV (w.s (j, k)),
      gm_res x.left z (U := L.U j₀ ⊓ L'.U k₀) _ hV (w.s (j₀, k₀))] at key
    exact key
  have h₂ : gm x.left z _ ((LB.LinComb Q.M.L (tensφ pr) (tensε W)).g (fun a => J (x.left ≫ tensφ pr a))
      (fun a => J₀ (x.left ≫ tensφ pr a))) = ∏ i, ∏ j, F i j ^ W i j := by
    refine (gm_linComb Q.M.L (tensφ pr) (tensε W) x.left z _ _ (hJ.mem (tensφ pr) x.left) (hJ₀.mem (tensφ pr) x.left)).trans ?_
    change ∏ a, H (x.left ≫ tensφ pr a) ^ tensε W a = _
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [GlobalTheory.Mum.TraitWit.comp_tensφ, hx, hx, ← zpow_mul, mul_comm]
    rfl
  have h₃ : ∀ i j, val (Q.tau (y i) (y j)) (𝟙 _) z J = (F i j)⁻¹ * val (Q.tau (y i) (y j)) (𝟙 _) z J₀ := fun i j => by
    refine (gen_trans (Q.tau_gen (y i) (y j)) (𝟙 _) z (hJ.mem _ _) (hJ₀.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    change ∏ a, H (𝟙 _ ≫ lamPts (toUnit (TK R) ≫ Q.c (y i)) (toUnit (TK R) ≫ Q.c (y j)) a) ^ negε a = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Category.id_comp, ← zpow_neg]
    congr 1
    fin_cases a <;> rfl
  refine (congrArg₂ (· * ·) (h₁.trans (congrArg (· * _ * _) h₂)) (Finset.prod_congr rfl fun i _ =>
    Finset.prod_congr rfl fun j _ => congrArg (· ^ W i j) (h₃ i j))).trans ?_
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_psi (Q : Data R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) {B' : Over (Sp R)} {L' : LB B'.left} (hL : L'.IsLB)
    (pr : Fin r → (B' ⟶ Q.B)) {w : LB.Iso L' (LB.LinComb Q.M.L (tensφ pr) (tensε W))} (hw : w.IsGen) (x : TK R ⟶ B')
    (y : Fin r → Q.X) (hx : ∀ i, x ≫ pr i = toUnit (TK R) ≫ Q.c (y i)) :
    ∃ t : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => x.left) (fun _ => -1)), t.IsGen ∧
      ∀ z J J', Good Q.M.L z J → Good L' z J' → val t (𝟙 _) z J' =
        gm x.left z _ (w.s (fun a => J (x.left ≫ tensφ pr a), J' x.left)) *
          ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  let z₀ : (TK R).left := closedPoint (FractionRing R)
  obtain ⟨J₀, hJ₀, -⟩ := exists_good _ Q.M.isLB z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J₁, hJ₁, -⟩ := exists_good _ hL z₀ (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  obtain ⟨t, ht, hv⟩ := exists_gen_val (F := FractionRing R) hL (K := PUnit) (fun _ => x.left) (fun _ => -1) hJ₁
    (gm x.left z₀ _ (w.s (fun a => J₀ (x.left ≫ tensφ pr a), J₁ x.left)) *
      ∏ i, ∏ j, val (Q.tau (y i) (y j)) (𝟙 _) z₀ J₀ ^ W i j)
  refine ⟨t, ht, fun z J J' hJ hJ' => ?_⟩
  obtain rfl : z = z₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
  have a := gen_trans ht (𝟙 (TK R).left) z₀ (hJ'.mem (fun _ : PUnit => x.left) _) (hJ₁.mem (fun _ : PUnit => x.left) _)
  have b : trF (L := L') (fun _ : PUnit => x.left) (fun _ => -1) (𝟙 (TK R).left) z₀ (fun _ => J' (𝟙 _ ≫ x.left))
      (fun _ => J₁ (𝟙 _ ≫ x.left)) = (gm x.left z₀ _ (L'.g (J' x.left) (J₁ x.left)))⁻¹ := by
    rw [trF, Fintype.prod_unique, zpow_neg_one, Category.id_comp]
  exact (a.trans (congrArg₂ (· * ·) b hv)).trans
    (formula_trans Q W pr hw x y hx z₀ J J₀ hJ hJ₀ (J' x.left) (J₁ x.left) (hJ' _) (hJ₁ _)).symm

end GlobalTheory.Mum.TensPol

noncomputable section
namespace GlobalTheory.Mum.TensPol

def cpt {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)}
    {pr : Fin r → (A' ⟶ Q.B)} (lim : IsLimit (Fan.mk A' pr)) (y : Fin r → Q.X) : 𝟙_ (Over (Sp R)) ⟶ A' :=
  lim.lift (Fan.mk _ fun i => Q.c (y i))

theorem cpt_pr {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)}
    {pr : Fin r → (A' ⟶ Q.B)} (lim : IsLimit (Fan.mk A' pr)) (y : Fin r → Q.X) (i : Fin r) : cpt lim y ≫ pr i = Q.c (y i) :=
  lim.fac (Fan.mk _ fun i => Q.c (y i)) ⟨i⟩

theorem cpt_add {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)} [GrpObj A']
    {pr : Fin r → (A' ⟶ Q.B)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk A' pr)) (a b : Fin r → Q.X) :
    cpt lim (a + b) = cpt lim a * cpt lim b := by
  refine lim.hom_ext fun i => ?_
  have := hpr i.as
  change cpt lim (a + b) ≫ pr i.as = (cpt lim a * cpt lim b) ≫ pr i.as
  rw [MonObj.mul_comp, cpt_pr, cpt_pr, cpt_pr]
  exact Q.c_add _ _

theorem cpt_zero {R : Type} [CommRing R] [IsDomain R] {Q : Data R} {r : ℕ} {A' : Over (Sp R)} [GrpObj A']
    {pr : Fin r → (A' ⟶ Q.B)} (hpr : ∀ i, IsMonHom (pr i)) (lim : IsLimit (Fan.mk A' pr)) :
    cpt lim (0 : Fin r → Q.X) = η[A'] := by
  refine lim.hom_ext fun i => ?_
  have := hpr i.as
  change cpt lim 0 ≫ pr i.as = η[A'] ≫ pr i.as
  rw [cpt_pr, IsMonHom.one_hom]
  have h := Q.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem exists_tensPol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) →
  ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
  ∃ (D' : DegData R (maximalIdeal R)) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) ∧
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) ∧ w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j := by
  intro R _ _ _ hR Q hQ r W hW hdet
  haveI : IsNoetherianRing R := hR.1
  obtain ⟨P', pr, hpr, ⟨lim⟩, ⟨w, hw⟩⟩ := GlobalTheory.T.exists_principally_polarised_power_unimodular_form R Q W hW hdet
  obtain ⟨sym, hsym, hsr⟩ := GlobalTheory.SelfUnif.exists_sym P'
  obtain ⟨rig, hrig, hrv⟩ := rig_exists Q.M.isLB W P'.isLB pr hpr w hw
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have cub := (hL.cube _ P' ⟨P'.L, rig, P'.isLB, hrig⟩ rfl).1.some
  choose psi hpsi hpv using fun y : Fin r → Q.X =>
    exists_psi Q W P'.isLB pr hw (toUnit (TK R) ≫ cpt lim y) y (fun i => by rw [Category.assoc, cpt_pr])
  let D' : DegPre R :=
    { P := P'
      rig := rig
      rig_gen := hrig
      cub := cub
      sym := sym
      sym_gen := hsym
      sym_rig := hsr
      X := Fin r → Q.X
      c := cpt lim
      c_add := cpt_add hpr lim
      psi := psi
      psi_gen := hpsi }
  have hv : ∀ (y : D'.X) z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' =
      gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
        ∏ i, ∏ j, val (Q.tau ((AddEquiv.refl D'.X) y i) ((AddEquiv.refl D'.X) y j)) (𝟙 _) z J ^ W i j :=
    fun y z J J' hJ hJ' => hpv y z J J' hJ hJ'
  have hc : ∀ (y : D'.X) i, D'.c y ≫ pr i = Q.c ((AddEquiv.refl D'.X) y i) := fun y i => cpt_pr lim y i
  have h0 : ∀ (z : (TK R).left) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J' →
      val (D'.psi 0) (𝟙 _) z J' * val D'.rigK (𝟙 _) z J' = 1 := by
    intro z J' hJ'
    obtain ⟨J, hJ, -⟩ := exists_good Q.M.L Q.M.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    have h1 := hpv 0 z J J' hJ hJ'
    have h2 := hrv z J J' hJ hJ'
    have hprod : (∏ i, ∏ j, val (Q.tau ((0 : Fin r → Q.X) i) ((0 : Fin r → Q.X) j)) (𝟙 _) z J ^ W i j) = 1 :=
      Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
        rw [show (0 : Fin r → Q.X) i = 0 from rfl, Q.val_tau_zero _ z J hJ, one_zpow]
    rw [hprod, _root_.mul_one] at h1
    show val (psi 0) (𝟙 _) z J' * val (LB.pullGen P'.L _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' = 1
    rw [h1, _root_.mul_comm]
    have hz := cpt_zero hpr lim (Q := Q)
    revert h2
    generalize cpt lim 0 = x at hz ⊢
    subst hz
    exact id
  obtain ⟨hpos, htend⟩ := GlobalTheory.T.tensorDegenerationData_psi_pos_tendsto_zero R hR Q D' W pr hpr lim (AddEquiv.refl _) hc w hw hv hW hQ
  exact ⟨⟨D', GlobalTheory.T.tensorDegenerationData_psi_even R hR Q D' W pr hpr lim (AddEquiv.refl _) hc w hw hv,
    GlobalTheory.T.tensorDegenerationData_tau_bimultiplicative R hR Q D' W pr hpr lim (AddEquiv.refl _) hc w hw hv h0, hpos, htend⟩,
    pr, AddEquiv.refl _, w, hpr, ⟨lim⟩, hc, hw, hv⟩

end GlobalTheory.Mum.TensPol
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegDataTensorPosDefUnimodularFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degData_tensor_posDef_unimodular_form : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) →
  ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
  ∃ (D' : DegData R (maximalIdeal R)) (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) ∧ Nonempty (IsLimit (Fan.mk D'.toPre.P.A pr)) ∧
    (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) ∧ w.IsGen ∧
    ∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j := by
  first | exact @GlobalTheory.Mum.TensPol.exists_tensPol | exact GlobalTheory.Mum.TensPol.exists_tensPol | (intros; apply GlobalTheory.Mum.TensPol.exists_tensPol <;> assumption)
end
