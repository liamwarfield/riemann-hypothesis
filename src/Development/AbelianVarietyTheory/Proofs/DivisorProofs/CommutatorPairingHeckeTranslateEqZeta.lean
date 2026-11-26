module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeWeilValue

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lbIso_mulA_diag (hA : IsAbelianScheme A) {P : LB (G2 A).left} (hP : P.IsLB)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) (k : ℕ) :
    LBIso (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (k ^ 2))
      ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull (Out.mulA A k).left) := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), DiagPairing.pc hP (x * x') y =
      DiagPairing.pc hP x y + DiagPairing.pc hP x' y := fun T x x' y => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), DiagPairing.pc hP x (y * y') =
      DiagPairing.pc hP x y + DiagPairing.pc hP x y' := fun T x y y' => by
    obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂ T y y' x).2
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    unfold DiagPairing.pc
    rw [← sub_eq_zero, ← e]
    abel
  refine (cls_eq_iff (LB.isLB_linComb hD _ _) (pull_isLB hD _)).1 ?_
  rw [cls_lbPow hD, cls_pull hD, cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have e1 : pull (lift (Out.mulA A k) (Out.mulA A k)).left (cls P hP) =
      DiagPairing.pc hP (Out.mulA A k) (Out.mulA A k) := rfl
  have e2 : pull (lift (𝟙 A) (𝟙 A)).left (cls P hP) = DiagPairing.pc hP (𝟙 A) (𝟙 A) := rfl
  rw [e1, e2, Out.mulA, DiagPairing.pc_pow_left hP hB, DiagPairing.pc_pow_right hP hB', smul_smul, sq]

end GlobalTheory.HeckeWeilValue


open GlobalTheory.HeckeWeilValue in
theorem GlobalTheory.UPel.HT.Hecke.weil_value_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k M : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))) (n : ℕ), 0 < n → n.Coprime p → ∀ (u v : D.La) (e : (Γ((Over.mk x).left, ⊤))ˣ), Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((n * (k ^ 2 / c) : ℕ) : ℤ) (I.ev (n * k) (g u)) (I.ev (n * k) (g v)) e → e = unitOn (I.ζ n ^ (2 * D.EF u v)) := by
  intro p _ D R _ b g c k M hc hk hEF _ hck S s o κ _ _ x β _ I n hn hnp u v e he
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hk0 : 0 < k := levelPos_of_coprime hk
  have hc0 : 0 < c := levelPos_of_coprime hc
  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) hc0
  have hmp : (k ^ 2 / c).Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro c hmc) (Nat.Coprime.pow_left 2 hk)
  set m := k ^ 2 / c with hm
  have hN : 0 < n * (m * k ^ 2) := by positivity
  have hNp : (n * (m * k ^ 2)).Coprime p :=
    Nat.Coprime.mul_left hnp (Nat.Coprime.mul_left hmp (Nat.Coprime.pow_left 2 hk))
  have eN : n * (m * k ^ 2) = n * k * (m * k) := by ring
  have hev : ∀ w : D.La, I.ev (n * k) (g w) = I.ev (n * (m * k ^ 2)) (m • g w) ≫ Out.mulA o.A k := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, ← TateIsoO.ev_nsmul, smul_smul, mul_comm k m,
      TateIsoO.ev_nsmul, eN, I.tower (n * k) (m * k) (by positivity) (by positivity) (by rw [← eN]; exact hNp)]
  letI : IsCommMonObj o.A := o.ab.comm
  haveI : IsMonHom (Out.mulA o.A k) := by
    change IsMonHom ((𝟙 o.A) ^ k)
    constructor
    · rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
    · rw [MonObj.comp_pow, Category.comp_id, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
        tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, mul_pow]
  have hw := lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ k
  rw [hev u, hev v] at he
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG o.ab hL hL (Out.mulA o.A k) hw he
  have h2 := I.isom (n * (m * k ^ 2)) hN hNp (m • g u) (m • g v)
  have eZ : ((n * m : ℕ) : ℤ) * ((k ^ 2 : ℕ) : ℤ) = ((n * (m * k ^ 2) : ℕ) : ℤ) := by push_cast; ring
  rw [eZ] at h1
  rw [GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hL h1 h2]
  congr 1
  have eF : D.EF (m • g u) (m • g v) = ((m * k ^ 2 : ℕ) : ℤ) * D.EF u v := by
    simp only [map_nsmul, LinearMap.smul_apply, hEF, nsmul_eq_mul]
    rw [← hmc]
    push_cast
    ring
  rw [eF, show (2 : ℤ) * (((m * k ^ 2 : ℕ) : ℤ) * D.EF u v) = ((m * k ^ 2 : ℕ) : ℤ) * (2 * D.EF u v) by ring,
    zpow_mul, zpow_natCast, I.ζ_pow n (m * k ^ 2) hn (by positivity) hNp]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_heckeTranslate_eq_zeta : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k M : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∀ (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))) (n : ℕ), 0 < n → n.Coprime p → ∀ (u v : D.La) (e : (Γ((Over.mk x).left, ⊤))ˣ), Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((n * (k ^ 2 / c) : ℕ) : ℤ) (I.ev (n * k) (g u)) (I.ev (n * k) (g v)) e → e = unitOn (I.ζ n ^ (2 * D.EF u v)) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.weil_value_translate | exact GlobalTheory.UPel.HT.Hecke.weil_value_translate | (intros; apply GlobalTheory.UPel.HT.Hecke.weil_value_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRootsUnity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdPairing

open GlobalTheory.CechPic GlobalTheory.DiagPairing

section Theta

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)
  (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_one_left {T : Over S} (y : T ⟶ A) : pc hP (1 : T ⟶ A) y = 0 := by
  have := hB T 1 1 y
  rwa [_root_.mul_one, left_eq_add] at this

include hB' in
theorem pc_one_right {T : Over S} (x : T ⟶ A) : pc hP x (1 : T ⟶ A) = 0 := by
  have := hB' T x 1 1
  rwa [_root_.mul_one, left_eq_add] at this


include hB hB' in
theorem exists_theta_prod {k : ℕ} {T : Over S} (X : T ⟶ G2 A) (hX : X ^ k = 1) :
    ∃ θ : Out.ThetaGrp (G2 A) P k T, θ.pt = X := by
  have e : ∀ g : T ⊗ G2 A ⟶ G2 A, pull g.left (cls P hP) = pc hP (g ≫ fst A A) (g ≫ snd A A) := fun g => by
    unfold pc
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have tr : Out.translPt (G2 A) X = (fst T (G2 A) ≫ X) * snd T (G2 A) := rfl
  have h₁ : (fst T (G2 A) ≫ X ≫ fst A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have h₂ : (fst T (G2 A) ≫ X ≫ snd A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have z₁ : ∀ y, k • pc hP (fst T (G2 A) ≫ X ≫ fst A A) y = 0 := fun y => by
    rw [← pc_pow_left hP hB, h₁, pc_one_left hP hB]
  have z₂ : ∀ x, k • pc hP x (fst T (G2 A) ≫ X ≫ snd A A) = 0 := fun x => by
    rw [← pc_pow_right hP hB', h₂, pc_one_right hP hB']
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB (G2 A) P k X), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T (G2 A)).left _ + (-(k : ℤ)) • pull (Out.translPt (G2 A) X).left _ = 0
    rw [e, e, tr, mul_comp, mul_comp, Category.assoc, Category.assoc, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, z₁, z₂]
    abel
  exact ⟨⟨X, t, ht⟩, rfl⟩

end Theta

theorem exists_weilIs_prod_root : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (k : ℕ), 0 < k → ∀ (T : Over S) (X Y : T ⟶ G2 A), X ^ k = 1 → Y ^ k = 1 →
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ k = 1 ∧ Out.WeilIs (G2 A) P k X Y c := by
  intro S A _ _ hA P hP rig₁ rig₂ hamp k hk T X Y hX hY
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ Z : T ⟶ G2 A, Z ^ k = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp (G2 A) P k (Out.overRes V), θ.pt = Out.overResι V ≫ Z := fun Z hZ p => by
    obtain ⟨θ, hθ⟩ := exists_theta_prod hP hB hB' (k := k) (Out.overResι ⊤ ≫ Z)
      (by rw [← MonObj.comp_pow, hZ, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts X hX) (lifts Y hY)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts 1 (one_pow k)) (lifts Y hY)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG hAA hP h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs (G2 A) P k (X ^ (m + 1)) Y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ X (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP ih hc₀
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hX] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG hAA hP hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.ProdPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobson
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalForm
namespace GlobalTheory

theorem krull_inter_ideal_local (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B)
    (h : ∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) : ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  set N : Submodule B (B ⧸ a') := Submodule.map (Submodule.mkQ a') a with hN
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  have hle : N ≤ I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h k hx)
    have h1 : Submodule.mkQ a' (y + z) = z • Submodule.mkQ a' 1 := by
      have hy0 : Submodule.mkQ a' y = 0 := by
        rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero a').2 hy
      rw [map_add (f := _), hy0, zero_add, ← map_smul, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  have hNI : N ≤ I • N := by
    have e1 : N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := (inf_eq_right.2 hle).symm
    calc N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := e1
      _ = I ^ (k + 1 - k) • (I ^ k • ⊤ ⊓ N) := hk (k + 1) (Nat.le_succ k)
      _ ≤ I • N := by
        rw [Nat.add_sub_cancel_left, pow_one]
        exact Submodule.smul_mono le_rfl inf_le_right
  have hfg : N.FG := IsNoetherian.noetherian N
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N hfg hNI
  refine ⟨r, hr, fun x hx => ?_⟩
  have hx' := hrN (Submodule.mkQ a' x) ⟨x, hx, rfl⟩
  rw [← map_smul, smul_eq_mul] at hx'
  have : Submodule.mkQ a' ((1 - r) * x) = 0 := by
    rw [sub_mul, one_mul, map_sub, hx', sub_self]
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero a').1 this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalFormStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_intersection_ideal_local_form : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  first | exact @GlobalTheory.krull_inter_ideal_local | exact GlobalTheory.krull_inter_ideal_local | (intros; apply GlobalTheory.krull_inter_ideal_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobson
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem ideal_le_on_basicOpen {X : Scheme.{0}} (a a' : X.IdealSheafData) (U : X.affineOpens)
    (g : Γ(X, U)) (h : ∀ s ∈ a.ideal U, g * s ∈ a'.ideal U) :
    a.ideal (X.affineBasicOpen g) ≤ a'.ideal (X.affineBasicOpen g) := by
  have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g) :=
    X.toRingedSpace.isUnit_res_basicOpen g
  have key : (a.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ≤
      (a'.ideal U).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom := by
    refine Ideal.map_le_iff_le_comap.2 fun s hs => ?_
    rw [Ideal.mem_comap]
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (h s hs)
  rw [← a.map_ideal_basicOpen, ← a'.map_ideal_basicOpen]
  exact key

theorem exists_affineOpen_mem {X : Scheme.{0}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 :=
  TopologicalSpace.Opens.mem_iSup.1 ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))

theorem le_of_le_reductions : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R))
    (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) →
    (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  intro R _ I hI V _ p a a' hUC hle
  let S := {U : V.affineOpens // a.ideal U ≤ a'.ideal U}
  have h1 : ∀ x : V, x ∉ a'.support → ∃ U : S, x ∈ U.1.1 := by
    intro x hx
    obtain ⟨U, hU⟩ := exists_affineOpen_mem x
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, Scheme.mem_zeroLocus_iff] at hx
    push_neg at hx
    obtain ⟨f, hf, hxf⟩ := hx
    exact ⟨⟨V.affineBasicOpen f, ideal_le_on_basicOpen a a' U f fun s _ => Ideal.mul_mem_right _ _ hf⟩, hxf⟩
  have h2 : ∀ x : V, I ≤ (p x).asIdeal → ∃ U : S, x ∈ U.1.1 := by
    intro x hx
    obtain ⟨U, hU⟩ := exists_affineOpen_mem x
    haveI : IsNoetherianRing Γ(V, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.krull_intersection_ideal_local_form Γ(V, U) (I.map (cst p U.1)) (a.ideal U) (a'.ideal U)
      (fun e => by
        have := hle e U
        rwa [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, Ideal.map_pow] at this)
    refine ⟨⟨V.affineBasicOpen (1 - r), ideal_le_on_basicOpen a a' U _ hr'⟩, ?_⟩
    have hsupp : x ∈ (baseIdeal p I).support := (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.2.2 R V p I x).2 hx
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, baseIdeal_ideal, Scheme.mem_zeroLocus_iff]
      at hsupp
    have hxr := hsupp r hr
    show x ∈ V.basicOpen (1 - r)
    rw [Scheme.mem_basicOpen _ _ _ hU] at hxr ⊢
    rw [map_sub, map_one]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hxr
  let O : V.Opens := ⨆ U : S, U.1.1
  have hZ := GlobalTheory.T.eq_empty_of_isClosed_of_universallyClosed_of_le_jacobson R I hI a'.subscheme (a'.subschemeι ≫ p) hUC
    (a'.subschemeι ⁻¹' (O : Set V)ᶜ) (O.isOpen.isClosed_compl.preimage a'.subschemeι.continuous)
    (fun z hz hIz => hz (by
      obtain ⟨U, hU⟩ := h2 (a'.subschemeι z) (by simpa using hIz)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩))
  have hO : O = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_contra hxO
    by_cases hx : x ∈ a'.support
    · have hx' : x ∈ Set.range a'.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      have : z ∈ (∅ : Set a'.subscheme) := hZ ▸ hxO
      exact this
    · obtain ⟨U, hU⟩ := h1 x hx
      exact hxO (TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩)
  exact Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : S => U.1) hO (fun U => U.2)

end GlobalTheory.FormalAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobsonStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (V : Scheme.{0}) [IsLocallyNoetherian V] (p : V ⟶ Spec (CommRingCat.of R)) (a a' : V.IdealSheafData), UniversallyClosed (a'.subschemeι ≫ p) → (∀ e : ℕ, a ≤ a' ⊔ baseIdeal p (I ^ (e + 1))) → a ≤ a' := by
  first | exact @GlobalTheory.FormalAlg.le_of_le_reductions | exact GlobalTheory.FormalAlg.le_of_le_reductions | (intros; apply GlobalTheory.FormalAlg.le_of_le_reductions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConj
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif GlobalTheory.ConjTransport GlobalTheory.DetLine

namespace GlobalTheory.ConjFlat

theorem isTangent_of_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ) {t : epsR ℂ ⟶ A}
    (ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left ≫ ψ = (1 : Over.mk y ⟶ G).left) : IsTangent t := by
  refine h.1.hom_ext ?_ ?_
  · refine ((Category.assoc _ _ _).trans ht).trans ?_
    refine Eq.trans ?_ (PolBaseChange.eSec_comm h).symm
    rw [Hom.one_def]
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

theorem isVecs_conj {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y₁ : Sp ℂ ⟶ S} {A A₁ : Over (Sp ℂ)} [GrpObj A]
    [GrpObj A₁] {L : LB A.left} {L₁ : LB A₁.left} {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ)
    {ρ : A₁.left ⟶ A.left} (hρ : IsGrpPullback A₁ A cj ρ) {ψ₁ : A₁.left ⟶ G.left} (hψ : ψ₁ = ρ ≫ ψ) {g n : ℕ}
    {u : HolUnif A L g} {u₁ : HolUnif A₁ L₁ g} (hx : ∀ z, u₁.ex z = cjPt hρ (u.ex (star z)))
    {v : Fin n → (epsAt y ⟶ G)} {v₁ : Fin n → (epsAt y₁ ⟶ G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v i).left = (1 : Over.mk y ⟶ G).left)
    (h₁ : ∀ i, (v₁ i).left = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (v i).left) {V : Fin n → Fin g → ℂ}
    (hV : IsVecs u ψ v V) : IsVecs u₁ ψ₁ v₁ fun i => star (V i) := by
  intro i
  obtain ⟨t, ht, hd⟩ := hV i
  have tg : IsTangent t := isTangent_of_fibre h (by rw [ht]; exact hv i)
  have w : (spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left)) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ cj := by
    rw [Category.assoc, show (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) from Over.w t, ← DetExtendZero.spMap_comp, ← DetExtendZero.spMap_comp]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let t₁ : epsR ℂ ⟶ A₁ := Over.homMk (hρ.1.lift _ _ w) (hρ.1.lift_snd _ _ _)
  have e : t₁.left ≫ ρ = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) :=
    hρ.1.lift_fst _ _ _
  refine ⟨t₁, ?_, ?_⟩
  · rw [hψ, ← Category.assoc, e, h₁, ← ht]
    exact Category.assoc _ _ _
  · have := cj_isDiff hρ (pullId u) tg e hd
    intro U hU f
    simp only [hx]
    exact this U hU f

theorem herm_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    herm (Hm.map star) (star z) (star w) = star (herm Hm z w) := by
  rw [herm, herm, ← star_form, star_star, star_star]

theorem isWedgeCoord_conj {g p q : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {V : Fin p → Fin g → ℂ} {W : Fin q → Fin g → ℂ}
    {x : Fin q ⊕ Fin p → Fin g → ℂ} {Δ : ℂ} (h : IsWedgeCoord Hm V W x Δ) :
    IsWedgeCoord (Hm.map star) (fun i => star (V i)) (fun j => star (W j)) (fun k => star (x k)) (star Δ) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun k i => star (a k i), fun k i => ?_, ?_⟩
  · have e : star (x k) - ∑ m, star (a k m) • star (V m) = star (x k - ∑ m, a k m • V m) := by
      simp [star_sum]
    rw [e, herm_conj, ha, star_zero]
  · refine ((starRingEnd ℂ).map_det _).trans (congrArg Matrix.det ?_)
    ext k (j | i)
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Sum.elim_inl, herm_conj]
      simp
    · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem isTransport_to_conj {B : Type} [CommRing B] {b : Base l B} {s s₁ s' s₁' : Sp ℂ ⟶ Sp B} {o : Obj D l b s}
    {o₁ : Obj D l b s₁} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o o' u u' Hm Hm' φ) :
    IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, hΛ', star_star, h1, hΛ]
  · rw [hx, hx, ← cjPt_act] at hw
    rw [e, e, hx', hx', star_star, star_star, ← cjPt_act, h2 a _ _ (cjPt_injective m.cart hw)]
  · rw [e, e, herm_map_star, herm_map_star, star_star, star_star, h3]
  · rw [hx, ← cjPt_eta m] at hz
    rw [e, hx', star_star, h4 a _ (cjPt_injective m.cart hz), cjPt_eta]
  · rw [hx, ← cjPt_etaA m] at hz
    rw [e, hx', star_star, h5 a _ (cjPt_injective m.cart hz), cjPt_etaA]

theorem exists_conj_fibre (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ (o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o₁ o cj)
      (k : ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)), k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
  obtain ⟨o₁, ⟨m⟩, -⟩ := exists_conj_obj Xo c y o n
  refine ⟨o₁, m, ?_⟩
  have a : ∀ f : Sp ℂ ⟶ Xo.X, f = cj ≫ y ≫ toX Xo c →
      ∃ k : ObjMap o₁ Xo.univ f, k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
    rintro _ rfl
    exact ObjComp.objMap_comp n m
  exact a _ (Category.assoc _ _ _)

end GlobalTheory.ConjFlat

namespace GlobalTheory

open ConjFlat

theorem isFlatAt_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c)
    (e : c.F →+* ℂ) (hσ : SecU Xo c U τ σ) (h : IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e)) :
    IsFlatAt Xo c U τ σ e := by
  intro y y' v w v' w' hf hf' o o' n n' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hΔ hΔ'
  obtain ⟨o₁, m, k, hk⟩ := exists_conj_fibre Xo c y o n
  obtain ⟨o₁', m', k', hk'⟩ := exists_conj_fibre Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  obtain ⟨v₁, w₁, hf₁, a, b⟩ := exists_pull (starRingEnd ℂ) hf (x' := cj ≫ y) rfl
  obtain ⟨v₁', w₁', hf₁', a', b'⟩ := exists_pull (starRingEnd ℂ) hf' (x' := cj ≫ y') rfl
  have i1 : ∀ z : ℂ, Chart.dualMapR (starRingEnd ℂ) (algebraMap ℂ _ z) = algebraMap ℂ _ (starRingEnd ℂ z) :=
    fun z => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have i2 : Chart.dualMapR (starRingEnd ℂ) DualNumber.eps = DualNumber.eps := by ext <;> simp [Chart.dualMapR]
  have s := hσ.1 ℂ ℂ _ _ _ _ _ _ v w v₁ w₁ i1 i2 hf hf₁ rfl a b
  have s' := hσ.1 ℂ ℂ _ _ _ _ _ _ v' w' v₁' w₁' i1 i2 hf' hf₁' rfl a' b'
  have q := h (cj ≫ y) (cj ≫ y') v₁ w₁ v₁' w₁' hf₁ hf₁' o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁' _ _ _ _ _
    (fun i => star (x i)) (star Δ) (star Δ') hA₁ hA₁' (isTransport_to_conj m m' hΛ hx hΛ' hx' hφ)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.1.1 i).1) a hV)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.2.1 i).1) b hW)
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.1.1 i).1) a' hV')
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.2.1 i).1) b' hW')
    (isWedgeCoord_conj hΔ) (by
      have := isWedgeCoord_conj hΔ'
      simpa only [LinearEquiv.trans_apply, conjEquiv_apply, star_star] using this)
  rw [s, s'] at q
  refine (starRingEnd ℂ).injective ?_
  rw [map_mul, map_mul]
  exact q

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) (e : c.F →+* ℂ), SecU Xo c U τ σ → IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e) → IsFlatAt Xo c U τ σ e := by
  first | exact @GlobalTheory.isFlatAt_of_conj | exact GlobalTheory.isFlatAt_of_conj | (intros; apply GlobalTheory.isFlatAt_of_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsos
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenIsoRatio

theorem gm_pullU_res {X Y : Scheme.{0}} (β : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (h : V ≤ β ⁻¹ᵁ U) (y : Y)
    (hy : y ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU β U a)) = gm β y U a := by
  rw [gm_res (𝟙 Y) y h hy, gm_pull (𝟙 Y) β y U (h hy), Category.id_comp]

theorem gm_pull_g' {X Y : Scheme.{0}} (β : Y ⟶ X) (L : LB X) (y : Y) (i i' : L.ι) (hi : β y ∈ L.U i)
    (hi' : β y ∈ L.U i') :
    gm (𝟙 Y) y ((L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i'))
      ((L.pull β).g (fun _ => i) (fun _ => i')) = gm β y (L.U i ⊓ L.U i') (L.g i i') := by
  have hp : y ∈ (L.pull β).U (fun _ => i) ⊓ (L.pull β).U (fun _ => i') := ⟨mem_pull.2 hi, mem_pull.2 hi'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU β _ (L.g i i'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hp _).trans ((gm_pull (𝟙 Y) β y (L.U i ⊓ L.U i') ⟨hi, hi'⟩ _).trans (by rw [Category.id_comp]))

theorem ratio : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro X Y β P M N hP hM hN w w₁ v hw hw₁ hv
  let W : N.ι × P.ι × M.ι → Y.Opens := fun j =>
    N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) ⊓ (M.pull β).U (fun _ => j.2.2)
  have l₁ : ∀ j, W j ≤ N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) := fun j => inf_le_left
  have l₂ : ∀ j, W j ≤ N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2) := fun j =>
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have l₃ : ∀ j, W j ≤ β ⁻¹ᵁ (M.U j.2.2 ⊓ P.U j.2.1) := fun j y hy =>
    ⟨mem_pull.1 hy.2, mem_pull.1 hy.1.2⟩
  let r : ∀ j, Γ(Y, W j)ˣ := fun j =>
    res (l₁ j) (w₁.s (j.1, fun _ => j.2.1)) * (res (l₃ j) (pullU β _ (v.s (j.2.2, j.2.1))))⁻¹ *
      (res (l₂ j) (w.s (j.1, fun _ => j.2.2)))⁻¹
  have k : ∀ j (y : Y), y ∈ W j → gm (𝟙 Y) y (W j) (r j) =
      gm (𝟙 Y) y (N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1)) (w₁.s (j.1, fun _ => j.2.1)) *
        (gm β y (M.U j.2.2 ⊓ P.U j.2.1) (v.s (j.2.2, j.2.1)))⁻¹ *
        (gm (𝟙 Y) y (N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2)) (w.s (j.1, fun _ => j.2.2)))⁻¹ := by
    intro j y hy
    simp only [r, map_mul, map_inv]
    erw [gm_res (𝟙 Y) y (l₁ j) hy, gm_res (𝟙 Y) y (l₂ j) hy, gm_pullU_res β _ (l₃ j) y hy]
  obtain ⟨u, hu⟩ := glue_unit (⊤ : Y.Opens) W (fun _ => le_top)
    (fun y _ => by
      obtain ⟨n, hn⟩ := exists_chart hN y
      obtain ⟨i, hi⟩ := exists_chart hP (β y)
      obtain ⟨m, hm⟩ := exists_chart hM (β y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(n, i, m), ⟨hn, mem_pull.2 hi⟩, mem_pull.2 hm⟩) r
    (fun j j' y hy => by
      have hi := mem_pull.1 hy.1.1.2
      have hi' := mem_pull.1 hy.2.1.2
      have hm := mem_pull.1 hy.1.2
      have hm' := mem_pull.1 hy.2.2
      rw [k j y hy.1, k j' y hy.2,
        GlobalTheory.PartialCocycle.gm_iso hw₁ (𝟙 Y) y j.1 j'.1 (fun _ => j.2.1) (fun _ => j'.2.1) hy.1.1.1 hy.2.1.1
          hy.1.1.2 hy.2.1.2,
        GlobalTheory.PartialCocycle.gm_iso hw (𝟙 Y) y j.1 j'.1 (fun _ => j.2.2) (fun _ => j'.2.2) hy.1.1.1 hy.2.1.1
          hy.1.2 hy.2.2,
        GlobalTheory.PartialCocycle.gm_iso hv β y j.2.2 j'.2.2 j.2.1 j'.2.1 hm hm' hi hi',
        gm_pull_g' β P y _ _ hi hi', gm_pull_g' β M y _ _ hm hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨u, fun n i m hle => ?_⟩
  have e : res (l₁ (n, i, m)) (w₁.s (n, fun _ => i)) =
      res (le_top : W (n, i, m) ≤ ⊤) u * res hle (pullU β _ (v.s (m, i))) * res (l₂ (n, i, m)) (w.s (n, fun _ => m)) := by
    change _ = _ * res (l₃ (n, i, m)) (pullU β _ (v.s (m, i))) * _
    rw [hu (n, i, m)]
    simp only [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact congrArg Units.val e

end GlobalTheory.GenIsoRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUnitRatioGenericLineBundleIsosStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_unit_ratio_generic_lineBundle_isos : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  first | exact @GlobalTheory.GenIsoRatio.ratio | exact GlobalTheory.GenIsoRatio.ratio | (intros; apply GlobalTheory.GenIsoRatio.ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenericIsoConst

theorem lbIso_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left), P.IsLB → M.IsLB → LBIso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) → LBIso P M := by
  intro W K' _ _ _ _ _ _ G _ hG P M hP hM h
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom inferInstance inferInstance
  let ψ : K' ≃ₐ[W] FractionRing W := IsLocalization.algEquiv (nonZeroDivisors W) K' (FractionRing W)
  have e₂ : Out.jK W ≫ 𝟙 _ = spMap (ψ : K' →+* FractionRing W) ≫ spMap (algebraMap W K') := by
    have hr : (ψ : K' →+* FractionRing W).comp (algebraMap W K') = algebraMap W (FractionRing W) := by
      ext x; simp
    rw [Category.comp_id, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]
  have h' : LBIso (P.pull (pullback.fst G.hom (Out.jK W))) (M.pull (pullback.fst G.hom (Out.jK W))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp
      (pullback.map G.hom (Out.jK W) G.hom (spMap (algebraMap W K')) (𝟙 _) (spMap (ψ : K' →+* FractionRing W)) (𝟙 _)
        (by simp) e₂) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm h
  exact GlobalTheory.lbIso_of_generic_normal_local W inferInstance inferInstance G.left G.hom (eSec G) inferInstance inferInstance
    inferInstance (Over.w η[G]) P M hP hM h'


open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh TopologicalSpace Opposite in
theorem globalFn_eq_cst : ∀ (W K' : Type) [CommRing W] [Field K'] [Algebra W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ f : Γ(pullback G.hom (spMap (algebraMap W K')), ⊤), ∃ c : K', f = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ c := by
  intro W K' _ _ _ G _ hG f
  have hU := GlobalTheory.AbCoh.uConst_of_isAbelianScheme W G hG K' (pullback G.hom (spMap (algebraMap W K')))
    (pullback.snd G.hom (spMap (algebraMap W K'))) (pullback.fst G.hom (spMap (algebraMap W K')))
    (IsPullback.of_hasPullback _ _)
  let g : C0 (OAff (pullback.snd G.hom (spMap (algebraMap W K')))) := fun T =>
    ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE le_top).op).hom f
  have hg : d0 _ g = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    rw [Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, sub_eq_zero]
    exact Sec.res_res (pullback.snd G.hom (spMap (algebraMap W K'))) le_top (leOfHom φ.unop) f
  obtain ⟨r, hr, -⟩ := hU g hg
  refine ⟨r, TopCat.Presheaf.section_ext (pullback G.hom (spMap (algebraMap W K'))).sheaf ⊤ _ _ fun x hx => ?_⟩
  obtain ⟨U, hUa, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp (pullback G.hom (spMap (algebraMap W K'))).isBasis_affineOpens hx
  have e1 : ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom f =
      ((pullback G.hom (spMap (algebraMap W K'))).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r) := by
    refine (hr (op ⟨U, hUa⟩)).trans ?_
    show _ = GlobalTheory.AbLaw.rs _ (le_top : U ≤ ⊤) (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
    rw [GlobalTheory.AbLaw.rs_cst]
    rfl
  have h1 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU f
  have h2 := TopCat.Presheaf.germ_res_apply (pullback G.hom (spMap (algebraMap W K'))).presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU
    (GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ r)
  exact h1.symm.trans ((congrArg _ e1).trans h2)

theorem exists_iso_const_of_generic : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro W K' _ _ _ _ _ _ G _ hG P M N hP hM hN w w₁ hw hw₁
  have hP' := pull_isLB hP (pullback.fst G.hom (spMap (algebraMap W K')))
  have hM' := pull_isLB hM (pullback.fst G.hom (spMap (algebraMap W K')))
  obtain ⟨v, hv⟩ := lbIso_of_generic W K' G hG P M hP hM (LBIso.trans hP' hN hM' ⟨w₁, hw₁⟩ (LBIso.symm ⟨w, hw⟩))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_global_unit_ratio_generic_lineBundle_isos _ _ _ P M N hP hM hN w w₁ v hw hw₁ hv
  obtain ⟨c, hc⟩ := globalFn_eq_cst W K' G hG u.val
  refine ⟨v, c, hv, fun n i m hle => ?_⟩
  rw [hu n i m hle, hc, GlobalTheory.AbLaw.rs_cst]

end GlobalTheory.GenericIsoConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_const_of_genericIso_dvr : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → ∃ (v : LB.Iso P M) (c : K'), v.IsGen ∧ ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  first | exact @GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | exact GlobalTheory.GenericIsoConst.exists_iso_const_of_generic | (intros; apply GlobalTheory.GenericIsoConst.exists_iso_const_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestMore
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.GenInterior

theorem exists_j₀_eq_genericPoint (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] :
    ∃ v : V₀ TF.Y Z, j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  obtain ⟨x, hx⟩ := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  have hxm : TF.Y.j x ∈ barComp TF.Y Z := (j_mem_barComp Z x).2 hx
  let v : V₀ TF.Y Z := ⟨x, hxm⟩
  have hU : IsOpen (Set.range (j₀ TF.Y Z)) := (j₀ TF.Y Z).isOpenEmbedding.isOpen_range
  exact ((genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff hU).2 ⟨j₀ TF.Y Z v, trivial, v, rfl⟩

end GlobalTheory.GenInterior
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupLevel
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefEig

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem actLev_levB (p : PtAt ex Csz) (i : Fin D.R.m) :
    ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  have h : ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (p.O i).lev2 := (p.pins i).2.act.1
  exact ⟨fun g => h.total g, fun g => h.func g, h.one, fun g g' => h.mul g g', fun g => h.nat g, fun g => h.bor g⟩


set_option maxHeartbeats 1000000 in
theorem mem_eigSub_iff (p : PtAt ex Csz) (i : Fin D.R.m) (χ : (p.F.lv2.lvl false).P →* (p.T.Q.c.F)ˣ)
    (f : p.T.R ((i : ℕ) + 1)) :
    f ∈ eigSub (Xo := p.T.Q.Xo ((i : ℕ) + 1)) (c := p.T.Q.c)
        (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) χ ↔
      ∀ u : (p.F.lv2.lvl false).P,
        actLev p.T.Q.c (p.O i).lev2 (u : p.P.Gp) f = ((χ u : (p.T.Q.c.F)ˣ) : p.T.Q.c.F) • f := by
  simp only [eigSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  rfl


end GlobalTheory.DefEig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreComponentClosureOpenIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreComponentClosureOpenIsIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_open_compactOf_isIntegral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ V : (gen Y).Opens, (V : Set (gen Y)) = compactOf Y U ∧ IsIntegral V.toScheme := by
  intro E _ _ _ H D l Xo c O _ β Y U hn _ hU
  have hint := isIntegral_open_of_geometricallyConnected E H D l Xo c U hU
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have := Y.jQ_open
  have hop : IsOpen (compactOf Y U) := GlobalTheory.FlatRow.isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (compactOf Y U) :=
    (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  let V : (gen Y).Opens := ⟨compactOf Y U, hop⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  exact ⟨V, rfl, isIntegral_of_irreducibleSpace_of_isReduced _⟩

end GlobalTheory.DetLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreComponentClosureOpenIsIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_componentClosure_open_isIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ V : (gen Y).Opens, (V : Set (gen Y)) = compactOf Y U ∧ IsIntegral V.toScheme := by
  first | exact @GlobalTheory.DetLine.exists_open_compactOf_isIntegral | exact GlobalTheory.DetLine.exists_open_compactOf_isIntegral | (intros; apply GlobalTheory.DetLine.exists_open_compactOf_isIntegral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem exists_specializes_dominatesStalk_of_regAt (X : Scheme.{0}) [IsIntegral X]
    (V : ValuationSubring X.functionField) (y : X) (hV : ∀ g, RegAt y g → g ∈ V) :
    ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  let ψ : X.presheaf.stalk y →+* V :=
    (algebraMap (X.presheaf.stalk y) X.functionField).codRestrict V.toSubring
      fun a ↦ hV _ ⟨a, rfl⟩
  let l : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk y
  have hl : specAlgebraMap V X.functionField ≫ l = genericFieldPoint X := by
    rw [← specAlgebraMap_fromSpecStalk y, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨l (IsLocalRing.closedPoint V), ?_, dominatesStalk_iff_exists_hom.mpr ⟨l, hl, rfl⟩⟩
  have h := ((IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk y).continuous)
  rw [Scheme.fromSpecStalk_closedPoint] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegularStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specializes_dominatesStalk_of_regular : ∀ (X : Scheme.{0}) [IsIntegral X] (V : ValuationSubring X.functionField) (y : X), (∀ g, RegAt y g → g ∈ V) → ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  first | exact @GlobalTheory.exists_specializes_dominatesStalk_of_regAt | exact GlobalTheory.exists_specializes_dominatesStalk_of_regAt | (intros; apply GlobalTheory.exists_specializes_dominatesStalk_of_regAt <;> assumption)
end
end
