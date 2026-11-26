module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.HTWeilLocus

open GlobalTheory.CechPic GlobalTheory.DiagPairing

section Root

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_weilIs_root {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (M : ℕ) (T : Over S) (x y : T ⟶ o.A) (hM : 0 < M)
    (hx : x ^ M = 1) (hy : y ^ M = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ M = 1 ∧ Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ o.A, z ^ M = 1 → ∀ q : T.left, ∃ V : T.left.Opens, q ∈ V ∧
      ∃ θ : Out.ThetaGrp o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (Out.overRes V),
        θ.pt = Out.overResι V ≫ z := fun z hz q => by
    obtain ⟨θ, hθ⟩ := exists_theta_diag o.isLB hB hB' (k := M) (Out.overResι ⊤ ≫ z)
      (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG o.ab hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG o.ab hD (lifts 1 (one_pow M)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG o.ab hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG o.ab hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG o.ab hD ih hc₀
  have hp := pw (M - 1)
  rw [Nat.sub_add_cancel hM, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG o.ab hD hp (e₁' ▸ hc₁), hc₀⟩

end Root

end GlobalTheory.HTWeilLocus

namespace GlobalTheory.HTWeilLocus

open GlobalTheory.LevCover

theorem weil_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  intro p _ D R _ b N h M hM hMp S t o Z t₁ e hadd hpow
  have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hLB : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hMZ : IsUnit (M : Γ(Z.left, ⊤)) := by
    have := (b.unit M hMp).map (fnOn (Z.hom ≫ t))
    rwa [map_natCast] at this
  let ζu : (cycAway M)ˣ := Units.ofPowEqOne (zetaAway M) M (zetaAway_pow_self M hM.ne') hM.ne'
  have hζv : (ζu : cycAway M) = zetaAway M := Units.val_ofPowEqOne _ _ _ _
  have hζM : ∀ (k : Type) [Field k] (β : cycAway M →+* k), Units.map β.toMonoidHom ζu ^ M = 1 := fun k _ β => by
    rw [← map_pow, Units.pow_ofPowEqOne, map_one]
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond Z.left := fun a c k _ _ x =>
    ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) →
      Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a)
        ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))
  have locPair : ∀ a c, HkClopen.Loc (P2 a c) := fun a c => by
    obtain ⟨v, hv, hW⟩ := exists_weilIs_root o M Z (e a) (e c) hM (hpow a) (hpow c)
    refine (GlobalTheory.loc_units_eq Z.left M v (Units.map (fnOn t₁).toMonoidHom (ζu ^ (2 * omegaStd a c))) hMZ hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t₁)
      rw [map_fnOn _ g β hβ, ← GlobalTheory.SiegCover.unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hζM, one_zpow]
      exact GlobalTheory.SiegCover.unitOn_one'
    · have hW' := GlobalTheory.CommPairing.weilIs_pull hG o.ab hLB (Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) hW
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ t₁)
      have hu := map_fnOn _ g β hβ (ζu ^ (2 * omegaStd a c))
      rw [show Units.map β.toMonoidHom (ζu ^ (2 * omegaStd a c)) =
        Units.map β.toMonoidHom ζu ^ (2 * omegaStd a c) from map_zpow _ _ _] at hu
      have hzβ : ((Units.map β.toMonoidHom ζu : kˣ) : k) = β (zetaAway M) := by
        rw [Units.coe_map]; exact congrArg β hζv
      constructor
      · intro E β' z hβ' hz
        obtain rfl : β = β' := spMap_inj' (hβ.symm.trans hβ')
        obtain rfl : z = Units.map β.toMonoidHom ζu := Units.ext (hz.trans hzβ.symm)
        rw [← hu, ← E]
        exact hW'
      · intro H
        exact GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hLB hW' (hu ▸ H β _ hβ hzβ)
  have e1 : ∀ a c, e (a + M • c) = e a := fun a c => by
    rw [hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + M • c₁) (a' + M • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β z hβ hz
    rw [e1, e1]
    have hzM : z ^ M = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self M hM.ne', map_one, Units.val_one])
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + M • c₁) (a' + M • c₂) = omegaStd a a' + M * m :=
      ⟨_, GlobalTheory.SiegCover.omegaStd_add_nsmul M a a' c₁ c₂⟩
    have hz' : z ^ (2 * omegaStd (a + M • c₁) (a' + M • c₂)) = z ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (M * m) = M * (2 * m) by ring, zpow_mul _ (M : ℤ), zpow_natCast,
        hzM, one_zpow, _root_.mul_one]
    rw [hz']
    exact H β z hβ hz
  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hM
  haveI := hκ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  exact localization₂.congr fun k _ _ x =>
    ⟨fun H β z hβ hz a c => H a c β z hβ hz, fun H a c β z hβ hz => H β z hβ hz a c⟩

end GlobalTheory.HTWeilLocus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_condition_locus_isClopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := by
  first | (exact @GlobalTheory.HTWeilLocus.weil_locus_clopen) | (exact GlobalTheory.HTWeilLocus.weil_locus_clopen) | (intros; apply GlobalTheory.HTWeilLocus.weil_locus_clopen  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfCoboundary
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CompHS GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.FlagHodge

attribute [local instance] Over.cartesianMonoidalCategory

theorem ev_cocycle {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) {S : Type} [CommRing S] (z : Sp S ⟶ Z) (i j k : L.ι)
    (hij : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j)) (hjk : ⊤ ≤ z ⁻¹ᵁ (L.U j ⊓ L.U k)) (hik : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    ev z _ hij (L.g i j).val * ev z _ hjk (L.g j k).val = ev z _ hik (L.g i k).val := by
  have h3 : ⊤ ≤ z ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_preimage_inf hij (le_preimage_mono inf_le_right hjk)
  have e := congrArg (fun u => ev z _ h3 u.val) (hL.cocycle i j k)
  exact (congrArg₂ (· * ·) (ev_res z _ h3 hij _).symm (ev_res z _ h3 hjk _).symm).trans
    ((map_mul (ev z _ h3) _ _).symm.trans (e.trans (ev_res z _ h3 hik _)))

theorem lbIso_of_coboundary {Z : Scheme.{0}} {J : Type} {U : J → Z.Opens} {g g' : ∀ i j, Γ(Z, U i ⊓ U j)ˣ}
    (hA : (⟨J, U, g⟩ : LB Z).IsLB) (d : ∀ k, Γ(Z, U k)ˣ)
    (h : ∀ k k', (g' k k').val * resG Z inf_le_right (d k').val = (g k k').val * resG Z inf_le_left (d k).val) :
    LBIso (⟨J, U, g⟩ : LB Z) ⟨J, U, g'⟩ := by
  refine ⟨⟨fun p => g p.1 p.2 * res inf_le_left (d p.1)⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ U p.1 := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ U q.1 := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ U p.2 := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ U q.2 := le_preimage_mono inf_le_right hq
  have c₁ := ev_cocycle hA z p.1 p.2 q.2 hp (le_preimage_inf hp2 hq2) (le_preimage_inf hp1 hq2)
  have c₂ := ev_cocycle hA z p.1 q.1 q.2 (le_preimage_inf hp1 hq1) hq (le_preimage_inf hp1 hq2)
  have c₃ := congrArg (ev z _ (le_preimage_inf hp1 hq1)) (h p.1 q.1)
  rw [map_mul, map_mul, ev_res z _ _ hq1, ev_res z _ _ hp1] at c₃
  refine (map_mul (ev z _ hz) _ _).trans (Eq.trans ?_ (map_mul (ev z _ hz) _ _).symm)
  refine (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans ((map_mul (ev z _ hp) _ _).trans
    (congrArg (_ * ·) (ev_res z _ hp hp1 _)))) (ev_res z _ hz (le_preimage_inf hp2 hq2) _)).trans (Eq.trans ?_
    (congrArg₂ (· * ·) (ev_res z _ hz (le_preimage_inf hp1 hq1) _) ((ev_res z _ hz hq _).trans
      ((map_mul (ev z _ hq) _ _).trans (congrArg (_ * ·) (ev_res z _ hq hq1 _))))).symm)
  have alg : ∀ a b e m n u v w : S, a * b = e → m * n = e → w * v = m * u → a * u * b = w * (n * v) :=
    fun a b e m n u v w h₁ h₂ h₃ => by linear_combination u * (h₁ - h₂) - n * h₃
  exact alg _ _ _ _ _ _ _ _ c₁ c₂ c₃

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)

theorem exists_eigFrame {W : X.YY.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S] (z : Sp S ⟶ X.YY)
    (hzW : ⊤ ≤ z ⁻¹ᵁ W) : ∃ φ : c.F →+* S, ∀ (k : X.F.J) (_ : W ≤ X.F.U k) (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k),
      ∃ f : EigFrame Y φ (z ≫ X.π), ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Γ(X.YY, W) →+* S, spMap ψ ≫ tau hW = z := ⟨_, spMap_ev z hW hzW⟩
  haveI := X.proper
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  haveI : IsLocallyNoetherian X.YY := LocallyOfFiniteType.isLocallyNoetherian (X.π ≫ Y.s)
  obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* Γ(X.YY, W), spMap φ = tau hW ≫ X.π ≫ Y.s :=
    ⟨(Spec.preimage (tau hW ≫ X.π ≫ Y.s)).hom, Spec.map_preimage _⟩
  refine ⟨ψ.comp φ, fun k hk hz => ?_⟩
  obtain ⟨K, _, ρ, hρ, hK⟩ := affineOpen_injects_to_dense X.YY (flagOpen X) (dense_flagOpen X) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have h₀ : ⊤ ≤ tau hW ⁻¹ᵁ X.F.U k := tau_le hW hk
  have hz' : ⊤ ≤ (spMap ρ ≫ tau hW) ⁻¹ᵁ X.F.U k := le_preimage_comp _ h₀
  have hr : Set.range ((spMap ρ ≫ tau hW) ≫ X.π) ⊆ Set.range Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift Y.j ((spMap ρ ≫ tau hW) ≫ X.π) hr
  have hyK : yK ≫ Y.j = (spMap ρ ≫ tau hW) ≫ X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : Y.j ≫ Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ Y.X) (hx : (spMap ρ ≫ tau hW) ≫ X.π = x''),
      (∀ σ, initSpan K (X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) = eigLie c ((spMap ρ ≫ tau hW) ≫ X.π) σ := by
    rintro x'' rfl h
    exact h
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (tau hW) k h₀ hz'
    (key _ hyK.symm fun σ => X.top K yK hy _ hyK.symm k hz' σ)
  obtain ⟨f, hf⟩ := f₀.exists_isMap ψ rfl (Category.assoc _ _ _)
  refine ⟨f, fun τ => funext fun i => tan_ext_left ?_⟩
  rw [← X.F.tanPull_vecAt k ψ (tau hW) h₀ hz rfl rfl (Category.assoc _ _ _).symm τ i, tanPull_left, ← hf₀, ← hf]
  simp only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]

def allDet (k : X.F.J) : Γ(X.YY, X.F.U k) :=
  rdet (Matrix.of fun (j : Fin (X.F.M k).n) (a : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) =>
    X.F.u k ((Fintype.equivFin _).symm a).1 j ((Fintype.equivFin _).symm a).2)

theorem ev_allDet (k : X.F.J) {S : Type} [CommRing S] {z : Sp S ⟶ X.YY} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) {φ : c.F →+* S}
    {f : EigFrame Y φ (z ≫ X.π)} (hf : ∀ τ, f.vec τ = X.F.vecAt k z hz rfl τ) :
    ev z _ hz (allDet X k) = frameDet (X.F.M k).toMChart (X.F.inM hz rfl) f := by
  rw [allDet, map_rdet, frameDet]
  congr 1
  ext j a
  simp [Module.Basis.toMatrix_apply, eigBasisFin, eigBasis_apply, hf, Frames.vecAt, Frames.uAt, vec,
    Finsupp.single_apply]

theorem isUnit_allDet (k : X.F.J) : IsUnit (allDet X k) := by
  refine X.YY.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k) (x := x) hx
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW (tau hW) (tau_le hW le_rfl)
  obtain ⟨f, hf⟩ := hφ k hle (tau_le hW hle)
  have hu := isUnit_frameDet (X.F.M k).toMChart (X.F.inM (tau_le hW hle) rfl) f
  rw [← ev_allDet X k _ hf, ev_tau hW hle] at hu
  have := hu.map (X.YY.presheaf.germ W x hxW).hom
  rwa [show (X.YY.presheaf.germ W x hxW).hom (resG X.YY hle (allDet X k)) = _ from
    X.YY.presheaf.germ_res_apply (homOfLE hle) x hxW _] at this

theorem lbIso_detOm_Llam : LBIso X.detOm (X.Llam (mu0 Dw)) := by
  classical
  rw [FlagCover.Llam, unitaryWeightExponentVector_signatureWeightMuZero]
  refine lbIso_of_coboundary X.F.isLB_detOm (fun k => (isUnit_allDet X k).unit) fun k k' =>
    ext_ev_loc fun x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X.YY) (U := X.F.U k ⊓ X.F.U k') (x := x) hx
  refine ⟨W, hxW, fun S _ z hh hzW => ?_⟩
  have hz := le_preimage_mono inf_le_left hh
  have hz' := le_preimage_mono inf_le_right hh
  have hM := le_preimage_inf (X.F.inM hz rfl) (X.F.inM hz' rfl)
  obtain ⟨φ, hφ⟩ := exists_eigFrame X hW z hzW
  obtain ⟨f, hf⟩ := hφ k (fun _ h => (hle h).1) hz
  obtain ⟨f', hf'⟩ := hφ k' (fun _ h => (hle h).2) hz'
  have hco : ∀ τ, f.co f' τ = (X.F.B k k' τ).map (ev z _ hh) := fun τ => by
    ext a i
    have e := f.vec_eq f' τ i
    rw [hf', X.F.vecAt_eq_sum k k' z hz hz' hh rfl τ i, ← hf] at e
    exact ((Fintype.linearIndependent_iffₛ.1 (f.linearIndependent_vec τ)) _ _ e a).symm
  have e₁ := (ev_detChg_mul_frameDet (X.F.M k).toMChart (X.F.M k').toMChart (X.F.inM hz rfl) (X.F.inM hz' rfl) hM
    f').trans (frameDet_change _ _ f f')
  have e₂ : ∏ τ, (f.co f' τ).det = (∏ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), X.F.TAt k k' z hh (some p)).val := by
    rw [Units.coe_prod, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hco, Matrix.det_of_upperTriangular (X.F.B_map_tri k k' τ _)]
    rfl
  have e₃ := X.F.ev_LL_g (fun ix => ix.elim 0 fun _ => 1) k k' z hh
  rw [Fintype.prod_option] at e₃
  simp only [Option.elim, neg_zero, zpow_zero, one_mul, zpow_neg, zpow_one, Finset.prod_inv_distrib] at e₃
  let a : Sˣ := Units.map (ev (z ≫ X.π) _ hM).toMonoidHom (detChg (X.F.M k).toMChart (X.F.M k').toMChart)
  have e₄ : ev z _ hh (X.F.detOm.g k k').val = (a⁻¹).val :=
    (ev_unit_inv z hh _).trans (congrArg (fun u : Sˣ => (u⁻¹).val) (Units.ext (ev_appLE z X.π _ hh hM _)))
  rw [← ev_allDet X k hz hf, ← ev_allDet X k' hz' hf', e₂] at e₁
  rw [map_mul, map_mul, ev_res z _ hh hz, ev_res z _ hh hz']
  refine (congrArg (· * _) e₃).trans (Eq.trans ?_ (congrArg (· * _) e₄).symm)
  rw [_root_.one_mul, Units.inv_mul_eq_iff_eq_mul, mul_left_comm, Units.eq_inv_mul_iff_mul_eq, _root_.mul_comm (Units.val _) (ev z _ hz _)]
  exact e₁

end GlobalTheory.FlagHodge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelBaseChangeCompleteDvrExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelBaseChangeCompleteDvrExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.UTestBaseChange

theorem baseChange : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsDiscreteValuationRing V₂] [Algebra (FractionRing V₂) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ → (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) → ∀ σ : FractionRing u.V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing u.V) (PadicAlgCl p) →
  ∃ (u' : ρ.UTest p y₀) (τ : FractionRing V₂ →+* FractionRing u'.V) (e : u'.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).comp τ = algebraMap (FractionRing V₂) (PadicAlgCl p) ∧
    (∀ χ r, u.PsiNorm (e χ) r → u'.PsiNorm χ r) ∧
    (∀ x, (T x).left ≫ u.φ = x.left ≫ u'.φ) ∧
    (∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) x', 1 ≤ m → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk'.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x')) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk' : QkPt u'.D.toPre (PadicAlgCl p) m, e pk'.y = pk.y ∧ QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' (T.symm x)) := by
  intro o Ω _ _ _ S ρ p _ y₀ u V₂ _ _ _ _ hc₂ hn₂ σ hσ
  have inj₂ := IsFractionRing.injective V₂ (FractionRing V₂)
  have hσv : ∀ z, algebraMap (FractionRing V₂) (PadicAlgCl p) (σ z) = algebraMap (FractionRing u.V) (PadicAlgCl p) z :=
    fun z => RingHom.congr_fun hσ z
  have hmem : ∀ v : u.V, σ (algebraMap u.V (FractionRing u.V) v) ∈ Set.range (algebraMap V₂ (FractionRing V₂)) :=
    fun v => (hn₂ _).1 (by rw [hσv]; exact (u.norm_le _).2 ⟨v, rfl⟩)
  choose gf hgf using hmem
  let g : u.V →+* V₂ :=
    { toFun := gf
      map_one' := inj₂ (by rw [hgf, map_one, map_one, map_one])
      map_mul' := fun a b => inj₂ (by rw [map_mul, hgf, hgf, hgf, map_mul, map_mul])
      map_zero' := inj₂ (by rw [hgf, map_zero, map_zero, map_zero])
      map_add' := fun a b => inj₂ (by rw [map_add (f := _), hgf, hgf, hgf, map_add (f := _), map_add (f := _)]) }
  have hgv : ∀ v, algebraMap V₂ (FractionRing V₂) (g v) = σ (algebraMap u.V _ v) := hgf
  have hK : σ.comp (algebraMap u.V _) = (algebraMap V₂ _).comp g := RingHom.ext fun v => (hgv v).symm
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V) (σ.injective (by rw [← hgv, ← hgv, h]))
  have hI : (IsLocalRing.maximalIdeal u.V).map g ≤ IsLocalRing.maximalIdeal V₂ := by
    rw [Ideal.map_le_iff_le_comap]
    intro v hv
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨w, hw⟩
    apply (IsLocalRing.mem_maximalIdeal _).1 hv
    have hv0 : algebraMap u.V (FractionRing u.V) v ≠ 0 := by
      intro h0
      have : g v = 0 := inj₂ (by rw [hgv, h0, map_zero, map_zero])
      rw [← hw] at this
      exact w.ne_zero this
    have e1 : algebraMap V₂ (FractionRing V₂) (w⁻¹ : V₂ˣ) = σ (algebraMap u.V _ v)⁻¹ := by
      rw [map_inv₀ σ, ← hgv, ← hw]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    obtain ⟨t, ht⟩ := (u.norm_le _).1 (by rw [← hσv, ← e1]; exact (hn₂ _).2 ⟨_, rfl⟩)
    refine isUnit_iff_exists_inv.2 ⟨t, IsFractionRing.injective u.V (FractionRing u.V) ?_⟩
    rw [map_mul, ht, mul_inv_cancel₀ hv0, map_one]
  have aV : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have aV₂ : AdmBase V₂ (IsLocalRing.maximalIdeal V₂) := ⟨inferInstance, inferInstance, inferInstance, hc₂⟩
  have sq : spMap σ ≫ jK u.V = jK V₂ ≫ spMap g := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hK
  obtain ⟨D', hD, A', gA, U', hPU, gp, hL, hgen⟩ := GlobalTheory.UnifMove.exists_pull aV aV₂ g hg hI σ sq u.semi u.U
  have hyK : spMap (σ.comp u.yK) = spMap σ ≫ spMap u.yK :=
    (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom σ))
  have cart' : IsGrpPullback A'.A ρ.P.A (spMap (σ.comp u.yK)) (gA ≫ u.φ) := (gp.comp u.cart).congr hyK.symm rfl
  have lb' : LBIso A'.L (ρ.P.L.pull (gA ≫ u.φ)) :=
    LBIso.trans A'.isLB (pull_isLB u.A.isLB gA) (pull_isLB ρ.P.isLB _) hL (GlobalTheory.PolDeg.lbIso_pull_comp u.lb gA rfl)
  have semi' : IsSemiAbelian ((Over.pullback (specOf g)).obj u.G) :=
    GlobalTheory.isSemiAbelian_of_unifPre_dvr V₂ D' A' _ U'.toUnifPre
  have fac' : (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp (σ.comp u.yK) = y₀ := by
    rw [← RingHom.comp_assoc, hσ, u.fac]
  let u' : ρ.UTest p y₀ :=
    { V := V₂, complete := hc₂, norm_le := hn₂, yK := σ.comp u.yK, fac := fac'
      A := A', φ := gA ≫ u.φ, cart := cart', lb := lb'
      G := (Over.pullback (specOf g)).obj u.G, semi := semi', D := D', U := U' }
  have sF : jFK (R := V₂) (PadicAlgCl p) ≫ spMap σ = jFK (R := u.V) (PadicAlgCl p) := by
    refine (Spec.map_comp _ _).symm.trans ?_
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hσ
  have wI : ∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A,
      x.left ≫ u.A.A.hom = jFK (R := V₂) (PadicAlgCl p) ≫ spMap σ :=
    fun x => (Over.w x).trans sF.symm
  let Tf : (TFK (R := V₂) (PadicAlgCl p) ⟶ A'.A) → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) := fun x =>
    Over.homMk (x.left ≫ gA) (by
      show (x.left ≫ gA) ≫ u.A.A.hom = jFK (R := u.V) (PadicAlgCl p)
      rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w x]; exact sF)
  let Ti : (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) → (TFK (R := V₂) (PadicAlgCl p) ⟶ A'.A) := fun x =>
    Over.homMk (gp.1.lift x.left (jFK (R := V₂) (PadicAlgCl p)) (wI x)) (gp.1.lift_snd _ _ _)
  let T : (TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    { toFun := Tf, invFun := Ti
      left_inv := fun x => Over.OverMorphism.ext
        (gp.1.hom_ext (gp.1.lift_fst _ _ _) ((gp.1.lift_snd _ _ _).trans (Over.w x).symm))
      right_inv := fun x => Over.OverMorphism.ext (gp.1.lift_fst _ _ _) }
  have hT : ∀ x, (T x).left = x.left ≫ gA := fun x => rfl
  have hTs : ∀ x, (T.symm x).left ≫ gA = x.left := fun x => gp.1.lift_fst _ _ _
  have hL2 := GlobalTheory.abelianSchemeLaws_all
  have hFc : ∀ r : u.V, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) r) =
      algebraMap (FractionRing V₂) (PadicAlgCl p) (algebraMap V₂ (FractionRing V₂) (g r)) := fun r => by
    rw [hgv]; exact (hσv _).symm
  have hτall := fun m : ℕ => GlobalTheory.exists_qk_pull_equiv hL2.1 hL2.2 u.V V₂ g u.D.toPre D'.toPre hD u.D.tau_bimult
    D'.tau_bimult (PadicAlgCl p) hFc m
  choose τq hτq using hτall
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj u.G)).hom := by
    show IsMonHom (𝟙 _); infer_instance
  have fwd : ∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
      (x' : TFK (R := V₂) (PadicAlgCl p) ⟶ A'.A), 1 ≤ m → x'.left ≫ gA = x.left →
      QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU U'.toUnifPre (PadicAlgCl p) m (τq m pk) x' := by
    intro m pk x x' hm hx H
    obtain ⟨hy, hgq⟩ := ((hτq m).1 pk _).1 rfl
    refine GlobalTheory.qkToAk_baseChange hL2.1.globalFns hL2.1.secBaseChange u.V V₂ _ _ aV aV₂ g u.D u.A u.G u.U
      _ (Iso.refl _) mR A' D' hD U' hPU (PadicAlgCl p) hFc m hm pk x (τq m pk) x' hy hgq ?_ H
    have n : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
    have hbc : (Iso.refl ((Over.pullback (specOf g)).obj u.G)).hom.left ≫ pullback.fst u.G.hom (specOf g) =
        pullback.fst u.G.hom (spMap g) := Category.id_comp _
    rw [hbc, ← hgen, ← Category.assoc U'.gen.inv.left, n, Category.id_comp, ← Category.assoc, hx]
  refine ⟨u', RingHom.id _, hD.xe, T, rfl, ?_, fun x => Category.assoc _ _ _, ?_, ?_⟩
  · intro χ r h j hj
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.ZH.RealCase.exists_chart u (hD.xe χ)
    have e := GlobalTheory.ZH.PsiNormPull.norm_psi_pull p u.V V₂ g (fun v => by rw [hgv]; exact (hσv _).symm)
      (fun v => (hn₂ _).2 ⟨v, rfl⟩) u.D.toPre D'.toPre hD χ (j₀ PUnit.unit) (j PUnit.unit) hj₀ hj
    exact e.trans (h j₀ hj₀)
  · intro m pk' x' hm H'
    obtain ⟨w₀, hw₀⟩ := U'.ext
    open MonObj in
    have ht' : x' ^ m = 1 := (H' w₀ hw₀).1
    open MonObj in
    have ht : (T x') ^ m = 1 := GlobalTheory.ThetaDescent.pow_eq_one_of_pull sF gp (hT x').symm ht'
    have hmF : ((m : ℕ) : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨pk₀, H₀⟩ := GlobalTheory.TorsionAnyChar.exists_qkToAkU u.V _ aV u.D u.A u.G u.semi u.U (PadicAlgCl p) m hmF
      (T x') ht
    have H₁ : QkToAkU U'.toUnifPre (PadicAlgCl p) m (τq m pk₀) x' := fwd m pk₀ (T x') x' hm rfl H₀
    have hE : QkPt.Equiv D'.toPre (PadicAlgCl p) (τq m pk₀) pk' :=
      GlobalTheory.TorsionMapInj.qkToAk_injective_closed V₂ _ aV₂ D' A' _ semi' U' (PadicAlgCl p) m hm _ _ x' H₁ H'
    have hE' : QkPt.Equiv u.D.toPre (PadicAlgCl p) pk₀ ((τq m).symm pk') :=
      ((hτq m).2.1 pk₀ ((τq m).symm pk')).2 (by rw [Equiv.apply_symm_apply]; exact hE)
    obtain ⟨hy, -⟩ := ((hτq m).1 ((τq m).symm pk') pk').1 (Equiv.apply_symm_apply _ _)
    refine ⟨(τq m).symm pk', ?_, GlobalTheory.ArcClauseCompare.qkToAkU_of_equiv u.U.toUnifPre hm hE' H₀⟩
    rw [hy, AddEquiv.apply_symm_apply]
  · intro m pk x hm H
    obtain ⟨hy, -⟩ := ((hτq m).1 pk _).1 rfl
    exact ⟨τq m pk, by rw [hy]; exact hD.xe.apply_symm_apply _, fwd m pk x (T.symm x) hm (hTs x) H⟩
end GlobalTheory.Poinc.UTestBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelBaseChangeCompleteDvrExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedModel_baseChange_complete_dvr_extension : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsDiscreteValuationRing V₂] [Algebra (FractionRing V₂) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ → (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) → ∀ σ : FractionRing u.V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing u.V) (PadicAlgCl p) →
  ∃ (u' : ρ.UTest p y₀) (τ : FractionRing V₂ →+* FractionRing u'.V) (e : u'.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).comp τ = algebraMap (FractionRing V₂) (PadicAlgCl p) ∧
    (∀ χ r, u.PsiNorm (e χ) r → u'.PsiNorm χ r) ∧
    (∀ x, (T x).left ≫ u.φ = x.left ≫ u'.φ) ∧
    (∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) x', 1 ≤ m → QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk'.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x')) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk' : QkPt u'.D.toPre (PadicAlgCl p) m, e pk'.y = pk.y ∧ QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' (T.symm x)) := by
  first | exact @GlobalTheory.Poinc.UTestBaseChange.baseChange | exact GlobalTheory.Poinc.UTestBaseChange.baseChange | (intros; apply GlobalTheory.Poinc.UTestBaseChange.baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperUniformisedSemiAbelianOverOpenInAbLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperUniformisedSemiAbelianOverOpenInAbLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnifProperOpen

theorem isProper_of_polGeneric_of_abLocus : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.UU.CDVR V →
    ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ → (∀ x, x ∈ abLocus G) → IsProper G.hom := by
  intro V _ _ _ hV A G _ _ hG φ hφ hab
  haveI := hV.1
  haveI := hV.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hφ
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends l₁ V A G hG e he
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package l₁ V hV A G hG e he L hL
  obtain ⟨w, hw⟩ := hL
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  have h0 : IsAbelianScheme (thickObj V (maximalIdeal V) 0 G) := by
    have h₂ := IsSemiAbelian.pullback (thick V (maximalIdeal V) 0) G hG
    letI := hF.toField
    exact ⟨h₂.comm, h₂.smooth, GlobalTheory.ArcNotAbelian.isProper_fibre G hG _ _ p (hab _), h₂.geomConnected⟩
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V) 0 P
  let s : GlobalTheory.UU.HidaSetting V A G := ⟨hV, hG, e, he, P, w, hw, PUnit, GlobalTheory.UU.TQ.abelian _ h0 PUnit, P₀, h₀,
    GlobalTheory.UU.SettingConsistentExample.ab_even h0 PUnit P₀⟩
  obtain ⟨D, U, -, -, -⟩ := GlobalTheory.uniformisation_dvr_unconditional V A G s
  let g := U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus G hG _ hF (thick V (maximalIdeal V) 0) p (hab _)
    D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hV.2.1 D A G hG U hs).proper

theorem exists_polGeneric_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
    (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V),
    Function.Injective φ → ∃ (A' : PolAV (Sp (FractionRing V))) (ψ : A'.A.left ⟶ ((Over.pullback (spMap φ)).obj G).left),
    IsGrpPullback A'.A ((Over.pullback (spMap φ)).obj G) (jK V) ψ := by
  intro R _ _ A G _ gen hgen V _ _ φ hφ
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hφ
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  obtain ⟨A', eA, heA, -⟩ := GlobalTheory.GoodReductionUnif.exists_baseChange GlobalTheory.polBaseChange_holds (spMap ψ) A
  have h₁ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (spMap ψ) A.A eA heA
  have h₂ := GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G gen hgen
  have h₃ := h₁.comp h₂
  refine ⟨A', pullback.lift ((eA.inv.left ≫ pullback.fst A.A.hom (spMap ψ)) ≫ gen.inv.left ≫
    pullback.fst G.hom (jK R)) (A'.A.hom ≫ jK V) (by rw [h₃.1.w, hg, Category.assoc]), ?_⟩
  exact (isGrpPullback_pullback G (spMap φ)).cancel (h₃.congr hg (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)

theorem range_spMap_away (R : Type) [CommRing R] (f : R) :
    Set.range (spMap (algebraMap R (Localization.Away f))) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
  have e : ⇑(spMap (algebraMap R (Localization.Away f))) = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) := by
    ext x : 1
    simp [spMap, Spec.map_base]
    rfl
  rw [e]
  exact PrimeSpectrum.localization_away_comap_range _ f

theorem isProper_away (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R]
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (gen : (Over.pullback (jK R)).obj G ≅ A.A) (hgen : IsMonHom gen.hom) (f : R) (hf : f ≠ 0)
    (hab : ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ abLocus G) :
    IsProper (pullback.snd G.hom (spMap (algebraMap R (Localization.Away f)))) := by
  haveI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : IsNoetherianRing (Localization.Away f) := IsLocalization.isNoetherianRing (Submonoid.powers f) _ inferInstance
  set j := spMap (algebraMap R (Localization.Away f)) with hj
  let Gf := (Over.pullback j).obj G
  haveI hGf : IsSemiAbelian Gf := IsSemiAbelian.pullback j G hG
  haveI := hGf.separated
  haveI := hGf.quasiCompact
  haveI := hGf.smooth
  haveI : IsIntegral Gf.left := GlobalTheory.isIntegral_left_of_isSemiAbelian Gf
  change IsProper Gf.hom
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint (Localization.Away f) Gf.left Gf.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+* V, spMap φ = y ≫ j := ⟨(Spec.preimage (y ≫ j)).hom, by simp [spMap]⟩
  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint Gf.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ Gf.hom ≫ j) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, GlobalTheory.ProperOfAbelianFibres.apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [← Category.assoc, hxy, Category.assoc, ← hφ] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj
  let GV := (Over.pullback (spMap φ)).obj G
  have hGV : IsSemiAbelian GV := IsSemiAbelian.pullback (spMap φ) G hG
  have habV : ∀ z, z ∈ abLocus GV := fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (spMap φ)) z).1
      (hab _ ⟨y z, by rw [hφ, Scheme.Hom.comp_apply]⟩)
  obtain ⟨A', ψ, hψ⟩ := exists_polGeneric_pullback R A G gen hgen V φ hinj
  have hpV : IsProper GV.hom := isProper_of_polGeneric_of_abLocus V ⟨inferInstance, inferInstance, inferInstance⟩ A' GV hGV ψ hψ habV
  let xV : Sp K ⟶ GV.left := pullback.lift (x ≫ pullback.fst G.hom j) (spMap (algebraMap V K)) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hxy]
    rw [Category.assoc, hφ])
  have hE : ValuativeCriterion.Existence GV.hom := by
    have h : UniversallyClosed GV.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq GV.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨(pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  have e₁ : spMap (algebraMap V K) ≫ l.l = xV := l.fac_left
  have e₂ : l.l ≫ GV.hom = 𝟙 _ := l.fac_right
  refine ⟨pullback.lift (l.l ≫ pullback.fst G.hom (spMap φ)) y ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [e₂]
    rw [Category.id_comp, hφ]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, e₁]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, pullback.lift_snd]
      exact hxy.symm

theorem isProper_restrict : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G →
    IsProper (G.hom ∣_ W) := by
  intro R _ _ _ hR D A G _ _ hG U W hW
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR
  haveI := hN
  haveI := hc
  let I := {f : R // f ≠ 0 ∧ ∀ z ∈ Set.range (spMap (algebraMap R (Localization.Away f))), z ∈ W}
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom (I := I)
    (fun i => spMap (algebraMap R (Localization.Away i.1))) (fun i => pullback.snd G.hom _)
    (fun i => pullback.fst G.hom _) (fun i => IsPullback.of_hasPullback _ _) (fun _ => ⊤) (fun i => ?_) W
    (fun i => ?_) (fun z hz => ?_)
  · exact IsZariskiLocalAtTarget.restrict
      (isProper_away R A G hG U.gen U.gen_hom i.1 i.2.1 fun z hz => hW (i.2.2 z hz)) ⊤
  · rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact i.2.2 _ ⟨_, rfl⟩
  · obtain ⟨_, ⟨f, rfl⟩, hzf, hfW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr := range_spMap_away R f
    have hzf' : z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hzf
    have hfW' : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ (W : Set (Sp R)) := hfW
    have hf : f ≠ 0 := by
      rintro rfl
      exact hzf' (zero_mem _)
    refine ⟨⟨f, hf, fun z' hz' => hfW' (by rw [hr] at hz'; exact hz')⟩, ?_⟩
    obtain ⟨a, ha⟩ : z ∈ Set.range (spMap (algebraMap R (Localization.Away f))) := by rw [hr]; exact hzf'
    exact ⟨⟨a, trivial⟩, ha⟩

end GlobalTheory.UnifProperOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperUniformisedSemiAbelianOverOpenInAbLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_uniformisedSemiAbelian_over_open_in_abLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G → IsProper (G.hom ∣_ W) := by
  first | exact @GlobalTheory.UnifProperOpen.isProper_restrict | exact GlobalTheory.UnifProperOpen.isProper_restrict | (intros; apply GlobalTheory.UnifProperOpen.isProper_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def TateAt {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k] (x : Sp k ⟶ S)
    (l : D.La → (Over.mk x ⟶ o.A)) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ y, l y = I.ev N' y

theorem tateAt_congr {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k]
    {x x' : Sp k ⟶ S} (e : x = x') (l : D.La → (Over.mk x ⟶ o.A)) (l' : D.La → (Over.mk x' ⟶ o.A))
    (h : ∀ a, (Over.homMk (𝟙 _) (by simp [e]) : Over.mk x' ⟶ Over.mk x) ≫ l a = l' a) :
    TateAt o N' x l → TateAt o N' x' l' := by
  subst e
  have h' : ∀ a, l a = l' a := fun a => by
    rw [← h a]
    have : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := by ext; simp
    rw [this, Category.id_comp]
  rintro ⟨I, hI⟩
  exact ⟨I, fun a => (h' a).symm.trans (hI a)⟩

theorem comp_actN_nsmul {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {T : Over S}
    (x : T ⟶ A) (n : ℕ) (c : D.O) : x ≫ act.act (n • c) = (x ^ n) ≫ act.act c := by
  have := act.hom c
  rw [add_map_nsmul act.add, MonObj.comp_pow, MonObj.pow_comp]

theorem exists_liftHom {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) (hc : N'.Coprime p)
    (hd : N ∣ N') :
    ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧
      (∀ a, et (N' • a) = 1) ∧ (∀ (c : D.O) a, et (c • a) = et a ≫ o.act.act c) ∧
      (∀ a, et ((N' / N) • a) = toUnit Z ≫ o.eta a) ∧
      ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N' • a) = 1) →
        (∀ (c : D.O) a, lv (c • a) = lv a ≫ o.act.act c) → (∀ a, lv ((N' / N) • a) = toUnit T ≫ o.eta a) →
          ∃! h : T ⟶ Z, ∀ a, h ≫ et a = lv a := by
  have hN' := levelPos_of_coprime hc
  have hNS : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit N' hc).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨Z, y, hfin, het, yadd, ypow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A N' D.La o.ab hNS
  have R : RepTors o.A N' D.La Z y := ⟨hfin, het, yadd, ypow, huniv⟩
  haveI := hfin
  haveI := het
  have ymod : ∀ a c, y (a + N' • c) = y a := fun a c => by
    rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have etaN : ∀ a, o.eta (N' • a) = 1 := fun a => by
    rw [← Nat.mul_div_cancel' hd, mul_smul, o.eta_ker]
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod D.O hN'
  have c1 : ClopenCond Z fun _ h => ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := o.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ o.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := o.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, o.act.add, MonObj.comp_mul, comp_actN_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond Z fun _ h => ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) :=
    R.clopenCond (fun a => y ((N' / N) • a)) (fun a => toUnit Z ≫ o.eta a) (fun a a' => by rw [smul_add, yadd])
      (fun a => ypow _) (fun a a' => by rw [o.eta_add, MonObj.comp_mul]) fun a => by
        rw [← MonObj.comp_pow, ← add_map_nsmul o.eta_add, etaN, MonObj.comp_one]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU W i).2 ((Hi W i).2 ⟨𝟙 W, Category.id_comp i⟩)
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [add_map_nsmul yadd, ypow, MonObj.comp_one],
    fun c a => by beta_reduce; rw [hi.1, Category.assoc], fun a => ?_, fun T lv hadd hker hlin hlev => ?_⟩
  · beta_reduce
    rw [hi.2, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have hpow : ∀ a, lv a ^ N' = 1 := fun a => by rw [← add_map_nsmul hadd, hker]
  obtain ⟨h, hh, -⟩ := huniv T lv hadd hpow
  have hP1 : ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := fun c a => by
    rw [hh, hlin, ← hh a, Category.assoc]
  have hP2 : ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) := fun a => by
    rw [hh, hlev, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 ⟨hP1, hP2⟩)
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
  have : g ≫ i = h' ≫ i := R.ext fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hh]
  exact (cancel_mono i).1 this

theorem exists_liftScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  intro p _ D R _ b N N' hc hd S _ s o
  obtain ⟨Z, et, hZf, hZe, eadd, eker, elin, elev, huniv⟩ := exists_liftHom o N' hc hd
  haveI := hZf
  haveI := hZe
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hsp : ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ Z.left)
      (x' : Sp k' ⟶ Z.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u →
      (TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        TateAt o N' (x' ≫ Z.hom) (fun a => (Over.homMk x' rfl : Over.mk (x' ≫ Z.hom) ⟶ Z) ≫ et a)) :=
    fun x x' u u' h => GlobalTheory.T.tateSimilitude_iff_of_specializes_geometric_points p D R b N N' hc S s o Z et eadd eker elin x x' u u' h
  let U : Set Z.left := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ Z.left),
    z ∈ Set.range x.base ∧
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a)}
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.left),
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        Set.range x.base ⊆ U := by
    intro k _ _ x
    refine ⟨fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩, fun hx => ?_⟩
    let pt : Sp k := (⊥ : PrimeSpectrum k)
    obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
    exact (hsp x x' pt u' (hu' ▸ specializes_rfl)).2 hG'
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff Z.left U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  let U' : Z.left.Opens := ⟨U, hclo.isOpen⟩
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U' hclo.isClosed
  refine ⟨V, fun a => i ≫ et a, hV1, hV2, fun T lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hker, hlin, hlev, hgeo⟩ := hL
    obtain ⟨h, hh, hu⟩ := huniv T lv hadd hker hlin hlev
    have hr : Set.range h.left ⊆ U' := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := FinEt.exists_algClosed_point T.left t
      obtain ⟨u, hu⟩ : t ∈ Set.range x.base := by rw [show Set.range x.base = {t} from hx]; rfl
      have hG := tateAt_congr o N' (x' := (x ≫ h.left) ≫ Z.hom)
        (by rw [Category.assoc, Over.w h]) _
        (fun a => (Over.homMk (x ≫ h.left) rfl : Over.mk ((x ≫ h.left) ≫ Z.hom) ⟶ Z) ≫ et a)
        (fun a => by rw [← hh a, ← Category.assoc, ← Category.assoc]; congr 1; try (ext; simp)) (hgeo k x)
      refine (key k (x ≫ h.left)).1 hG ⟨u, ?_⟩
      rw [Scheme.Hom.comp_apply, hu]
    obtain ⟨h', hh'⟩ := (Hi T h).1 hr
    refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
    have : g ≫ i = h := hu _ fun a => by rw [Category.assoc]; exact hg a
    exact (cancel_mono i).1 (this.trans hh'.symm)
  · obtain ⟨f, hf⟩ := hex
    have hf' : ∀ a, lv a = (f ≫ i) ≫ et a := fun a => by rw [Category.assoc]; exact (hf a).symm
    refine ⟨fun a c => by rw [hf', hf', hf', eadd, MonObj.comp_mul], fun a => by rw [hf', eker, MonObj.comp_one],
      fun c a => by rw [hf', hf', elin]; simp only [Category.assoc], fun a => ?_, fun k _ _ x => ?_⟩
    · rw [hf', elev, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have hr : Set.range (f ≫ i).left ⊆ U' := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hG := (key k (x ≫ (f ≫ i).left)).2 fun z ⟨u, hu⟩ => hr ⟨x.base u, by rw [← hu, Scheme.Hom.comp_apply]⟩
    refine tateAt_congr o N' (by rw [Category.assoc, Over.w (f ≫ i)]) _ _ ?_ hG
    intro a
    rw [hf' a]
    simp only [← Category.assoc]
    congr 1
    try (ext; simp)

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_etale_level_lift_scheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  first | exact @GlobalTheory.UPel.HT.exists_liftScheme | exact GlobalTheory.UPel.HT.exists_liftScheme | (intros; apply GlobalTheory.UPel.HT.exists_liftScheme <;> assumption)
end
end
