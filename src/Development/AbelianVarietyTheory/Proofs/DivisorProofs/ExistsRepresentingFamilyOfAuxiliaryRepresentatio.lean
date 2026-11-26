module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionDescendsFiniteEtaleGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTateLevelConditionDescendsGaloisCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTateLevelConditionDescendsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.GeomDesc

theorem diag_comp {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left := by
  apply pullback.hom_ext
  · have h1 := sq.1
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := sq.2
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P₀ : LB (G2 A₀).left}
    (hP : P.IsLB) (hP₀ : P₀.IsLB) (pol : LBIso P (P₀.pull φ₂)) :
    LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) := by
  have h₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp pol _ (diag_comp sq).symm
  have h₂ : LBIso ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) φ rfl
  exact LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.GeomDesc


open GlobalTheory.UPel.HT.GeomDesc in
theorem GlobalTheory.UPel.HT.geom_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ N φ₂ P P₀ eta eta₀ hG hA hA₀ gp hact sq hP hP₀ pol heta hgeom k _ _ x β hx
  have := hG.etale
  have := hG.onto
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  obtain ⟨I, hI⟩ := hgeom k y β (by rw [← Category.assoc, hx])
  have iso := diag_lbIso sq hP hP₀ pol
  refine ⟨GlobalTheory.UPel.HT.TateIsoO.transport (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    show (g ≫ act.act c).left ≫ φ = (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y) g ≫ act₀.act c).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X A₀ A π φ _ _ (pull_isLB hP₀ _) (pull_isLB hP _) gp iso
      (Over.mk y) n g g' _ _ _ (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g)
      (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g')).1 hc
  · rw [GlobalTheory.UPel.HT.TateIsoO.transport_ev, ← hI a]
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left]
    show (toUnit (Over.mk (y ≫ π)) ≫ eta₀ a).left = (toUnit (Over.mk y) ≫ eta a).left ≫ φ
    rw [Over.comp_left, Over.comp_left, Category.assoc, heta a, ← Category.assoc]
    congr 1

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTateLevelConditionDescendsGaloisCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_tate_level_condition_descends_galois_cover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  first | exact @GlobalTheory.UPel.HT.geom_descends_galoisCover | exact GlobalTheory.UPel.HT.geom_descends_galoisCover | (intros; apply GlobalTheory.UPel.HT.geom_descends_galoisCover; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMaps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_sympLev_pull {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'}
    {f : S' ⟶ S} (m : ObjMap o' o f) {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {t₁ : S ⟶ Sp B}
    {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    ∃ l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ o'.A), IsSympLev o'.P h M ζ (f ≫ t₁) l ∧
      ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left := by
  refine ⟨fun a => GlobalTheory.ObjPull.secPull m.cart (lev a), ⟨fun a c => by dsimp only; rw [hl.1, map_mul],
    fun a => by dsimp only; rw [← map_pow, hl.2.1, map_one], fun k _ _ x β z hx hz => ?_⟩,
    fun a => GlobalTheory.ObjPull.secPull_left m.cart _⟩
  let Φ := GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)
  have hΦ : ∀ a, Φ (toUnit _ ≫ GlobalTheory.ObjPull.secPull m.cart (lev a)) = toUnit (Over.mk (x ≫ f)) ≫ lev a :=
    fun a => GlobalTheory.ObjPull.pushEquiv_secPull m.cart _ _
  obtain ⟨hker, honto, hw⟩ := hl.2.2 k (x ≫ f) β z ((Category.assoc _ _ _).trans hx) hz
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← hker a, ← hΦ a]
    exact (map_eq_one_iff Φ Φ.injective).symm
  · obtain ⟨a, ha⟩ := honto (Φ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, Φ.injective ((hΦ a).trans ha)⟩
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A o'.A f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o'.isLB _) m.cart
      (DiagComp.diag_lbIso m) (Over.mk x) _ _ _ (toUnit (Over.mk (x ≫ f)) ≫ lev a)
      (toUnit (Over.mk (x ≫ f)) ≫ lev b) _ (by rw [← hΦ a]; rfl) (by rw [← hΦ b]; rfl)).2 (hw a b)

theorem reduceMod_eq_zero_iff {h M : ℕ} (a : Fin h ⊕ Fin h → ℤ) : reduceMod M a = 0 ↔ ∃ c, a = M • c := by
  constructor
  · intro ha
    have hd : ∀ i, (M : ℤ) ∣ a i := fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (congrFun ha i)
    choose c hc using hd
    exact ⟨c, funext fun i => by rw [Pi.smul_apply, hc i, nsmul_eq_mul]⟩
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]

theorem omegaMod_reduceMod {h : ℕ} (M : ℕ) (a c : Fin h ⊕ Fin h → ℤ) :
    omegaMod M (reduceMod M a) (reduceMod M c) = ((omegaStd a c : ℤ) : ZMod M) := by
  simp [omegaMod, omegaStd, reduceMod]

theorem lev_nsmul {S : Scheme.{0}} {A : Over S} [GrpObj A] {h : ℕ} (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A))
    (hadd : ∀ a c, l (a + c) = l a * l c) (n : ℕ) (a : Fin h ⊕ Fin h → ℤ) : l (n • a) = l a ^ n := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {h : ℕ}

theorem ev_add (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (hl : ∀ a c, l (a + c) = l a * l c) {k : Type} [Field k]
    (y : Sp k ⟶ S) (a c : Fin h ⊕ Fin h → ℤ) :
    toUnit (Over.mk y) ≫ l (a + c) = (toUnit (Over.mk y) ≫ l a) * (toUnit (Over.mk y) ≫ l c) := by
  rw [hl, MonObj.comp_mul]

theorem ev_sub (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) (hl : ∀ a c, l (a + c) = l a * l c) {k : Type} [Field k]
    (y : Sp k ⟶ S) (a c : Fin h ⊕ Fin h → ℤ) :
    toUnit (Over.mk y) ≫ l (a - c) = (toUnit (Over.mk y) ≫ l a) * (toUnit (Over.mk y) ≫ l c)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← ev_add l hl y, sub_add_cancel]

theorem ev_eq_iff {P : LB (G2 A).left} {M : ℕ} {B : Type} [CommRing B] {ζ : B} {t₁ : S ⟶ Sp B}
    {l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)} (hl : IsSympLev P h M ζ t₁ l) (k : Type) [Field k] [IsAlgClosed k]
    (y : Sp k ⟶ S) (β : B →+* k) (z : kˣ) (hy : y ≫ t₁ = spMap β) (hz : (z : k) = β ζ) (a c : Fin h ⊕ Fin h → ℤ) :
    toUnit (Over.mk y) ≫ l a = toUnit (Over.mk y) ≫ l c ↔ reduceMod M a = reduceMod M c := by
  have hk := (hl.2.2 k y β z hy hz).1 (a - c)
  rw [ev_sub l hl.1 y, mul_inv_eq_one] at hk
  rw [hk, ← sub_eq_zero, ← reduceMod_eq_zero_iff]
  constructor <;> intro e
  · rw [← e]; funext i; simp [reduceMod]
  · rw [← e]; funext i; simp [reduceMod]

end

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_sim_point {h M : ℕ} (hM : 0 < M) (hodd : Odd M) {T : Scheme.{0}} {t : T ⟶ Sp R} (o : Obj b N t)
    {t₁ t₁' : T ⟶ Sp (cycAway M)} {l l' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)}
    (hl : IsSympLev o.P h M (zetaAway M) t₁ l) (hl' : IsSympLev o.P h M (zetaAway M) t₁' l')
    (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ T) (β β' : cycAway M →+* k) (hβ : y ≫ t₁ = spMap β)
    (hβ' : y ≫ t₁' = spMap β') :
    ∃ (a : sympSimGrp h M) (i : ℕ), (∀ u v, omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) u)
        ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) v) = (i : ZMod M) * omegaMod M u v) ∧
      β' (zetaAway M) = β (zetaAway M) ^ i ∧
      ∀ c, toUnit (Over.mk y) ≫ l' c = toUnit (Over.mk y) ≫ sympTwist a l c := by
  haveI : NeZero M := ⟨hM.ne'⟩
  have hzk : IsPrimitiveRoot (β (zetaAway M)) M := isPrimitiveRoot_map hM.ne' β
  have hzk' : IsPrimitiveRoot (β' (zetaAway M)) M := isPrimitiveRoot_map hM.ne' β'
  let z : kˣ := Units.mk0 _ (hzk.ne_zero hM.ne')
  let z' : kˣ := Units.mk0 _ (hzk'.ne_zero hM.ne')
  have hz : IsPrimitiveRoot z M := IsPrimitiveRoot.coe_units_iff.1 hzk
  obtain ⟨-, onto, hw⟩ := hl.2.2 k y β z hβ rfl
  obtain ⟨-, -, hw'⟩ := hl'.2.2 k y β' z' hβ' rfl
  have E := ev_eq_iff hl k y β z hβ rfl
  have E' := ev_eq_iff hl' k y β' z' hβ' rfl
  have hpre : ∀ c : Fin h ⊕ Fin h → ℤ, ∃ B, toUnit (Over.mk y) ≫ l B = toUnit (Over.mk y) ≫ l' c := fun c =>
    onto _ (by rw [← MonObj.comp_pow, hl'.2.1, MonObj.comp_one])
  choose B hB using hpre
  let γ0 : (Fin h ⊕ Fin h → ZMod M) → (Fin h ⊕ Fin h → ZMod M) := fun c => reduceMod M (B (liftMod c))
  have hchar : ∀ c b, reduceMod M b = γ0 c ↔
      toUnit (Over.mk y) ≫ l b = toUnit (Over.mk y) ≫ l' (liftMod c) := fun c b => by
    rw [← hB, E]
  have hadd : ∀ c c', γ0 (c + c') = γ0 c + γ0 c' := fun c c' => by
    have e1 : reduceMod M (B (liftMod c) + B (liftMod c')) = reduceMod M (B (liftMod c)) + reduceMod M (B (liftMod c')) := by
      funext i; simp [reduceMod]
    show γ0 (c + c') = reduceMod M (B (liftMod c)) + reduceMod M (B (liftMod c'))
    rw [← e1]
    refine ((hchar _ _).2 ?_).symm
    rw [ev_add l hl.1 y, hB, hB, ← ev_add l' hl'.1 y, E']
    funext i; simp [reduceMod, liftMod]
  have hinj : Function.Injective γ0 := fun c c' e => by
    have h1 := (hchar c' (B (liftMod c))).1 e
    rw [hB, E', reduceMod_liftMod, reduceMod_liftMod] at h1
    exact h1
  let γl : (Fin h ⊕ Fin h → ZMod M) →ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M) :=
    (AddMonoidHom.mk' γ0 hadd).toZModLinearMap M
  have hγl : ∀ c, γl c = γ0 c := fun _ => rfl
  have hbij : Function.Bijective γl := by
    have hi : Function.Injective γl := fun c c' e => hinj (by rwa [hγl, hγl] at e)
    exact ⟨hi, Finite.surjective_of_injective hi⟩
  let γe := LinearEquiv.ofBijective γl hbij
  have hγe : ∀ c, γe c = γ0 c := fun _ => rfl
  obtain ⟨i, -, hi⟩ := hzk.eq_pow_of_pow_eq_one hzk'.pow_eq_one
  have hi' : z ^ i = z' := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi)
  have hcop : i.Coprime M := (hz.pow_iff_coprime hM i).1 (hi' ▸ IsPrimitiveRoot.coe_units_iff.1 hzk')
  have h2 : IsUnit ((2 : ℕ) : ZMod M) := (ZMod.unitOfCoprime 2 (Nat.coprime_two_right.2 hodd).symm).isUnit
  have hpair : ∀ a c, ((omegaStd (B a) (B c) : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a c : ℤ) : ZMod M) := by
    intro a c
    have h1 := hw (B a) (B c)
    rw [hB, hB] at h1
    have e2 := GlobalTheory.weilIs_unique_fieldPoint T o.A _ (pull_isLB o.isLB _) k y M _ _ _ _ h1 (hw' a c)
    rw [← hi', ← zpow_natCast, ← zpow_mul] at e2
    have h3 : z ^ (2 * omegaStd (B a) (B c) - (i : ℤ) * (2 * omegaStd a c)) = 1 := by
      rw [zpow_sub, e2, mul_inv_cancel]
    rw [hz.zpow_eq_one_iff_dvd] at h3
    have h4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).2 h3
    push_cast at h4
    have h5 : ((2 : ℕ) : ZMod M) * (((omegaStd (B a) (B c) : ℤ) : ZMod M) - (i : ZMod M) * ((omegaStd a c : ℤ) : ZMod M)) = 0 := by
      push_cast; linear_combination h4
    exact sub_eq_zero.1 (h2.mul_right_eq_zero.1 h5)
  have hsim : ∀ u v, omegaMod M (γe u) (γe v) = (i : ZMod M) * omegaMod M u v := by
    intro u v
    conv_rhs => rw [← reduceMod_liftMod u, ← reduceMod_liftMod v]
    rw [hγe, hγe, omegaMod_reduceMod, omegaMod_reduceMod, hpair]
  let m : (ZMod M)ˣ := ZMod.unitOfCoprime i hcop
  refine ⟨⟨γe, m, fun u v => by rw [hsim, ZMod.coe_unitOfCoprime]⟩, i, hsim, hi.symm, fun c => ?_⟩
  show _ = toUnit (Over.mk y) ≫ l (liftMod (γe (reduceMod M c)))
  rw [hγe, (hchar _ _).1 (reduceMod_liftMod _), E', reduceMod_liftMod]

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_spMap_eq {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem exists_open_eq_cycAway {M : ℕ} (hM : M ≠ 0) {T : Scheme.{0}} (f g : T ⟶ Sp (cycAway M)) (k : Type) [Field k]
    (y : Sp k ⟶ T) (hy : y ≫ f = y ≫ g) : ∃ V : T.Opens, Set.range y ⊆ (V : Set T) ∧ V.ι ≫ f = V.ι ≫ g := by
  haveI : FormallyUnramified (spMap (algebraMap ℤ (cycAway M))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact RingHom.formallyUnramified_algebraMap.2 (formallyUnramified_cycAway hM ℤ)
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ (cycAway M))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 (finiteType_cycAway M)
  have hab : f ≫ spMap (algebraMap ℤ (cycAway M)) = g ≫ spMap (algebraMap ℤ (cycAway M)) :=
    specZIsTerminal.hom_ext _ _
  haveI := GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified (spMap (algebraMap ℤ (cycAway M))) hab
  refine ⟨(equalizer.ι f g).opensRange, GlobalTheory.range_subset_range_equalizer_ι y hy, ?_⟩
  rw [← cancel_epi (equalizer.ι f g).isoOpensRange.hom, ← Category.assoc, ← Category.assoc,
    Scheme.Hom.isoOpensRange_hom_ι, equalizer.condition]

theorem false_of_sympLev_zero {M : ℕ} (hM : 2 ≤ M) (hMp : M.Coprime p) {T : Scheme.{0}} {t : T ⟶ Sp R}
    (o : Obj b N t) {t₁ : T ⟶ Sp (cycAway M)} {l : (Fin 0 ⊕ Fin 0 → ℤ) → (𝟙_ (Over T) ⟶ o.A)}
    (hl : IsSympLev o.P 0 M (zetaAway M) t₁ l) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ T)
    (βR : R →+* k) (hR : y ≫ t = spMap βR) (β : cycAway M →+* k) (hβ : y ≫ t₁ = spMap β) : False := by
  have hM0 : 0 < M := by omega
  have hzk : IsPrimitiveRoot (β (zetaAway M)) M := isPrimitiveRoot_map hM0.ne' β
  obtain ⟨-, onto, -⟩ := hl.2.2 k y β (Units.mk0 _ (hzk.ne_zero hM0.ne')) hβ rfl
  obtain ⟨I, -⟩ := o.geom k y βR hR
  haveI := D.freeLa
  haveI := D.finLa
  let bs := Module.Free.chooseBasis ℤ D.La
  have hpos : 0 < Module.finrank ℤ D.La := by have := Datum.two_le_finrank_La D; omega
  obtain ⟨i₀⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ D.La) := by
    rw [← Fintype.card_pos_iff, ← Module.finrank_eq_card_chooseBasisIndex]; exact hpos
  have hnd : ¬ ∃ c, bs i₀ = M • c := by
    rintro ⟨c, hc⟩
    have e := congrArg (fun v => bs.repr v i₀) hc
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at e
    have : (M : ℤ) ∣ 1 := ⟨_, e⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  have hne : I.ev M (bs i₀) ≠ 1 := fun e => hnd ((I.ker M hM0 hMp _).1 e)
  have hpow : I.ev M (bs i₀) ^ M = 1 := (I.onto M hM0 hMp _).2 ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := onto _ hpow
  have ha0 : a = 0 := funext fun i => i.elim (fun j => j.elim0) (fun j => j.elim0)
  have l0 : l 0 = 1 := by
    have e := hl.1 0 0
    rw [add_zero] at e
    exact (mul_left_cancel (e.symm.trans (_root_.mul_one _).symm))
  rw [ha0, l0, MonObj.comp_one] at ha
  exact hne ha.symm

end GlobalTheory.HTLocSim

namespace GlobalTheory.HTLocSim

theorem exists_local_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : sympSimGrp h M), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  intro p _ D R _ b N h M hN hNp hM hodd hMp X s s₁ u lev hlev hU ρ hρ T t o x x' hx hx' ⟨m⟩ ⟨m'⟩ q
  obtain ⟨l, hl, hlp⟩ := exists_sympLev_pull m hlev
  obtain ⟨l', hl', hlp'⟩ := exists_sympLev_pull m' hlev
  let k := AlgebraicClosure (T.residueField q)
  let y : Sp k ⟶ T := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField q) k)) ≫ T.fromSpecResidueField q
  have hyq : q ∈ Set.range y :=
    ⟨(⊥ : PrimeSpectrum k), (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply q _)⟩
  have hM0 : 0 < M := by omega
  haveI : NeZero M := ⟨hM0.ne'⟩
  obtain ⟨β, hβ⟩ := exists_spMap_eq (y ≫ x ≫ s₁)
  obtain ⟨β', hβ'⟩ := exists_spMap_eq (y ≫ x' ≫ s₁)
  obtain ⟨βR, hβR⟩ := exists_spMap_eq (y ≫ t)
  obtain ⟨a, i, hmul, hzi, ha⟩ := exists_sim_point hM0 hodd o hl hl' k y β β' hβ hβ'
  obtain ⟨hρs, ⟨n, σ, hn, hσ, hρ1⟩, ma, hma⟩ := hρ a
  have hz := isPrimitiveRoot_map hM0.ne' β
  have hni : β (zetaAway M) ^ n = β (zetaAway M) ^ i := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact (false_of_sympLev_zero (by omega) hMp o hl k y βR hβR β hβ).elim
    · let e₁ : Fin h ⊕ Fin h → ZMod M := Sum.elim (fun j => if j = ⟨0, hh⟩ then 1 else 0) (fun _ => 0)
      let e₂ : Fin h ⊕ Fin h → ZMod M := Sum.elim (fun _ => 0) (fun j => if j = ⟨0, hh⟩ then 1 else 0)
      have hω : omegaMod M e₁ e₂ = 1 := by simp [omegaMod, e₁, e₂]
      have h1 := (hn e₁ e₂).symm.trans (hmul e₁ e₂)
      rw [hω, _root_.mul_one, _root_.mul_one, ZMod.natCast_eq_natCast_iff'] at h1
      have key : ∀ j, β (zetaAway M) ^ j = β (zetaAway M) ^ (j % M) := fun j => by
        conv_lhs => rw [← Nat.mod_add_div j M, pow_add, pow_mul, hz.pow_eq_one, one_pow, _root_.mul_one]
      rw [key n, key i, h1]
  have hσβ : β.comp σ = β' := cycAway_hom_ext hM0.ne' (by rw [RingHom.comp_apply, hσ, map_pow, hni, hzi])
  have hy1 : y ≫ (x ≫ ρ a ≫ s₁) = y ≫ (x' ≫ s₁) := by
    calc y ≫ (x ≫ ρ a ≫ s₁) = (y ≫ x ≫ s₁) ≫ spMap σ := by rw [hρ1]; simp only [Category.assoc]
      _ = spMap (β.comp σ) := by rw [hβ, spMap, spMap, spMap, ← Spec.map_comp]; rfl
      _ = y ≫ x' ≫ s₁ := by rw [hσβ, hβ']
  obtain ⟨V₁, hV₁y, hV₁⟩ := exists_open_eq_cycAway hM0.ne' (x ≫ ρ a ≫ s₁) (x' ≫ s₁) k y hy1
  have hunit : IsUnit ((M : ℕ) : Γ(T, ⊤)) := by
    have h2 := ((b.unit M hMp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map t.appTop.hom
    simpa only [map_natCast] using h2
  have hV : ∀ c : Fin h ⊕ Fin h → ZMod M, ∃ W : T.Opens, Set.range y ⊆ (W : Set T) ∧
      W.ι ≫ (l' (liftMod c)).left = W.ι ≫ (sympTwist a l (liftMod c)).left := fun c =>
    GlobalTheory.UPel.LocSim.exists_open_eq_of_torsion_point T o.A o.ab M hunit _ _ (hl'.2.1 _) (hl.2.1 _) k y (ha _)
  choose W hWy hW using hV
  let V : T.Opens := V₁ ⊓ ⟨⋂ c, (W c : Set T), isOpen_iInter_of_finite fun c => (W c).isOpen⟩
  have hqV : q ∈ V := ⟨hV₁y hyq, Set.mem_iInter.2 fun c => hWy c hyq⟩
  have hVW : ∀ c, V ≤ W c := fun c => fun z hz => Set.mem_iInter.1 hz.2 c
  have hV1 : V ≤ V₁ := fun z hz => hz.1
  have hagree : ∀ c, V.ι ≫ (l' c).left = V.ι ≫ (sympTwist a l c).left := by
    intro c
    have e1 : l' c = l' (liftMod (reduceMod M c)) := by
      obtain ⟨e, he⟩ := (reduceMod_eq_zero_iff (M := M) (c - liftMod (reduceMod M c))).1 (by
        funext j
        simp only [reduceMod, liftMod, Pi.zero_apply, Pi.sub_apply, Int.cast_sub, Int.cast_natCast,
          ZMod.natCast_zmod_val, sub_self])
      have hc : c = M • e + liftMod (reduceMod M c) := by rw [← he, sub_add_cancel]
      calc l' c = l' (M • e + liftMod (reduceMod M c)) := congrArg l' hc
        _ = l' (M • e) * l' (liftMod (reduceMod M c)) := hl'.1 _ _
        _ = _ := by rw [lev_nsmul l' hl'.1, hl'.2.1, _root_.one_mul]
    have e2 : sympTwist a l c = sympTwist a l (liftMod (reduceMod M c)) := by
      simp only [sympTwist, reduceMod_liftMod]
    rw [e1, e2, ← Scheme.homOfLE_ι T (hVW (reduceMod M c)), Category.assoc, Category.assoc, hW]
  have hVs : V.ι ≫ (x ≫ ρ a ≫ s₁) = V.ι ≫ (x' ≫ s₁) := by
    rw [← Scheme.homOfLE_ι T hV1, Category.assoc, Category.assoc, hV₁]
  obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N T V t V.ι o
  obtain ⟨lV, hlV, hlVp⟩ := exists_sympLev_pull mV hl'
  obtain ⟨f, -, huniq⟩ := hU V (V.ι ≫ t) (V.ι ≫ x' ≫ s₁) oV lV hlV
  let compMap {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
      {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
      (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) :=
    { φ := m₁.φ ≫ m₂.φ
      φ₂ := m₁.φ₂ ≫ m₂.φ₂
      cart := IsGrpPullback.comp m₁.cart m₂.cart
      sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
        by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
      act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
      pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
        (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂)
          (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
          m₂.pol)
      eta := fun y => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  have P1 : (V.ι ≫ x ≫ ρ a) ≫ s = V.ι ≫ t ∧ (V.ι ≫ x ≫ ρ a) ≫ s₁ = V.ι ≫ x' ≫ s₁ ∧
      ∃ m : ObjMap oV u (V.ι ≫ x ≫ ρ a), ∀ c, (lV c).left ≫ m.φ = (V.ι ≫ x ≫ ρ a) ≫ (lev c).left := by
    refine ⟨by simp only [Category.assoc, hρs, hx], by simpa only [Category.assoc] using hVs,
      compMap mV (compMap m ma), fun c => ?_⟩
    show (lV c).left ≫ (mV.φ ≫ (m.φ ≫ ma.φ)) = (V.ι ≫ x ≫ ρ a) ≫ (lev c).left
    calc (lV c).left ≫ (mV.φ ≫ (m.φ ≫ ma.φ)) = ((lV c).left ≫ mV.φ) ≫ m.φ ≫ ma.φ := by
          simp only [Category.assoc]
      _ = (V.ι ≫ (l' c).left) ≫ m.φ ≫ ma.φ := by rw [hlVp c]
      _ = (V.ι ≫ (sympTwist a l c).left) ≫ m.φ ≫ ma.φ := by rw [hagree c]
      _ = V.ι ≫ ((sympTwist a l c).left ≫ m.φ) ≫ ma.φ := by simp only [Category.assoc]
      _ = V.ι ≫ (x ≫ (sympTwist a lev c).left) ≫ ma.φ := by
          rw [show (sympTwist a l c).left ≫ m.φ = x ≫ (sympTwist a lev c).left from hlp _]
      _ = V.ι ≫ x ≫ ((sympTwist a lev c).left ≫ ma.φ) := by simp only [Category.assoc]
      _ = V.ι ≫ x ≫ ρ a ≫ (lev c).left := by rw [hma c]
      _ = (V.ι ≫ x ≫ ρ a) ≫ (lev c).left := by simp only [Category.assoc]
  have P2 : (V.ι ≫ x') ≫ s = V.ι ≫ t ∧ (V.ι ≫ x') ≫ s₁ = V.ι ≫ x' ≫ s₁ ∧
      ∃ m : ObjMap oV u (V.ι ≫ x'), ∀ c, (lV c).left ≫ m.φ = (V.ι ≫ x') ≫ (lev c).left := by
    refine ⟨by simp only [Category.assoc, hx'], Category.assoc _ _ _, compMap mV m', fun c => ?_⟩
    show (lV c).left ≫ (mV.φ ≫ m'.φ) = (V.ι ≫ x') ≫ (lev c).left
    rw [← Category.assoc, hlVp c, Category.assoc, hlp' c, Category.assoc]
  exact ⟨V, a, hqV, (huniq _ P1).trans (huniq _ P2).symm⟩

end GlobalTheory.HTLocSim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSymplecticSimilitudeClassifyingMapsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_symplecticSimilitude_classifyingMaps : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : sympSimGrp h M), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  first | (exact @GlobalTheory.HTLocSim.exists_local_similitude) | (exact GlobalTheory.HTLocSim.exists_local_similitude) | (intros; apply GlobalTheory.HTLocSim.exists_local_similitude  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompBis
noncomputable section

namespace GlobalTheory.UPel.HT.ObjMapComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {s'' : S'' ⟶ Sp R}
  {o : Obj b N s} {o' : Obj b N s'} {o'' : Obj b N s''} {f : S' ⟶ S} {g : S'' ⟶ S'}

def comp (m₁ : ObjMap o'' o' g) (m₂ : ObjMap o' o f) : ObjMap o'' o (g ≫ f) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
         by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o''.isLB (pull_isLB o'.isLB m₁.φ₂) (pull_isLB o.isLB _) m₁.pol
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o'.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

end GlobalTheory.UPel.HT.ObjMapComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamily
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.SympAct

theorem exists_smul_iff {h : ℕ} (M : ℕ) (w : Fin h ⊕ Fin h → ℤ) : (∃ c, w = M • c) ↔ reduceMod M w = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]
  · intro hw
    refine ⟨fun i => w i / M, ?_⟩
    funext i
    have hd : (M : ℤ) ∣ w i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun hw i)
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [Int.mul_ediv_cancel' hd]

theorem lev_eq_of_reduce {h : ℕ} {T : Type*} [Monoid T] {M : ℕ} (hM : 0 < M) (lev : (Fin h ⊕ Fin h → ℤ) → T)
    (hadd : ∀ a b, lev (a + b) = lev a * lev b) (htor : ∀ a, lev a ^ M = 1) {x y : Fin h ⊕ Fin h → ℤ}
    (hxy : reduceMod M x = reduceMod M y) : lev x = lev y := by
  have hsm : ∀ (n : ℕ) c, lev ((n + 1) • c) = lev c ^ (n + 1) := by
    intro n c
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, hadd, ih, ← pow_succ]
  obtain ⟨c, hc⟩ := (exists_smul_iff M (x - y)).2 (by
    funext i
    have e := congrFun hxy i
    simp only [reduceMod] at e
    simp only [reduceMod, Pi.sub_apply, Int.cast_sub, e, sub_self, Pi.zero_apply])
  have hx : x = y + M • c := by rw [← hc]; abel
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  rw [hx, hadd, hsm, htor, _root_.mul_one]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (a b : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd a b : ℤ) : ZMod M) = omegaMod M (reduceMod M a) (reduceMod M b) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem zpow_eq_of_cast_eq {G : Type*} [Group G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℤ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ k - l := (ZMod.intCast_eq_intCast_iff_dvd_sub l k M).1 hkl.symm
  have e : k = l + M * t := by linarith
  rw [e, zpow_add, zpow_mul, zpow_natCast, hz, one_zpow, _root_.mul_one]

theorem pow_eq_of_cast_eq {G : Type*} [Monoid G] {M : ℕ} (z : G) (hz : z ^ M = 1) {k l : ℕ}
    (hkl : (k : ZMod M) = l) : z ^ k = z ^ l := by
  rw [ZMod.natCast_eq_natCast_iff'] at hkl
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod l M, hkl, pow_add, pow_add, pow_mul, pow_mul, hz, one_pow, one_pow]

theorem mult_unique {h M : ℕ} (hh : 0 < h) (g : sympSimGrp h M) {n n' : ℕ} (hn : IsMultOf g n)
    (hn' : IsMultOf g n') : (n : ZMod M) = n' := by
  classical
  let e : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inl ⟨0, hh⟩) 1
  let f : Fin h ⊕ Fin h → ZMod M := Pi.single (Sum.inr ⟨0, hh⟩) 1
  have hef : omegaMod M e f = 1 := by
    simp [omegaMod, e, f, Pi.single_apply]
  have := (hn e f).symm.trans (hn' e f)
  rw [hef] at this
  simpa using this

theorem isMultOf_mul {h M : ℕ} {a c : sympSimGrp h M} {n n' : ℕ} (ha : IsMultOf a n) (hc : IsMultOf c n') :
    IsMultOf (a * c) (n * n') := by
  intro x y
  change omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
    ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
    ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
  rw [ha, hc]
  push_cast
  ring

theorem isMultOf_one {h M : ℕ} : IsMultOf (1 : sympSimGrp h M) 1 := by
  intro x y
  change omegaMod M x y = ((1 : ℕ) : ZMod M) * omegaMod M x y
  simp

theorem exists_mult {h M : ℕ} [NeZero M] (a : sympSimGrp h M) :
    ∃ n : ℕ, IsMultOf a n ∧ n.Coprime M ∧ (h = 0 → n = 1) := by
  by_cases hh : h = 0
  · subst hh
    exact ⟨1, fun x y => by simp [omegaMod], Nat.coprime_one_left _, fun _ => rfl⟩
  · obtain ⟨m, hm⟩ := a.2
    exact ⟨(m : ZMod M).val, fun x y => by rw [ZMod.natCast_zmod_val]; exact hm x y,
      ZMod.val_coe_unit_coprime m, fun h0 => absurd h0 hh⟩

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def idObjMap {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) :=
  { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
    act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }

theorem isSympLev_twist {b : Base D R} {N h M : ℕ} (hM : 0 < M) {X : Scheme.{0}} {s : X ⟶ Sp R}
    {s₁ : X ⟶ Sp (cycAway M)} (u : Obj b N s) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A))
    (hlev : IsSympLev u.P h M (zetaAway M) s₁ lev) (a : sympSimGrp h M) (n : ℕ) (ha : IsMultOf a n)
    (σ : cycAway M →+* cycAway M) (hσ : σ (zetaAway M) = zetaAway M ^ n) :
    IsSympLev u.P h M (zetaAway M) (s₁ ≫ spMap σ) (sympTwist a lev) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlev
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  have hred_add : ∀ x y : Fin h ⊕ Fin h → ℤ, reduceMod M (x + y) = reduceMod M x + reduceMod M y := by
    intro x y; funext i; simp [reduceMod]
  refine ⟨fun x y => ?_, fun x => htor _, ?_⟩
  · simp only [sympTwist]
    rw [← hadd]
    apply hres
    simp only [hred_add, reduceMod_liftMod, map_add (f := _)]
  · intro k _ _ x β z hx hz
    obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : cycAway M →+* k, x ≫ s₁ = spMap β₀ :=
      ⟨(Spec.preimage (x ≫ s₁)).hom, by simp [spMap]⟩
    have hββ : β = β₀.comp σ := by
      have e : spMap β = spMap (β₀.comp σ) := by
        rw [← hx, ← Category.assoc, hβ₀, spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
    have hζ := isPrimitiveRoot_zetaAway hM.ne'
    let z₀ : kˣ := ((hζ.isUnit hM.ne').map β₀).unit
    have hz₀ : (z₀ : k) = β₀ (zetaAway M) := IsUnit.unit_spec _
    have hz' : z = z₀ ^ n := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz, hββ, RingHom.comp_apply, hσ, map_pow, hz₀]
    have hz₀M : z₀ ^ M = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz₀, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one]
    obtain ⟨hker, hsurj, hweil⟩ := hgeo k x β₀ z₀ hβ₀ hz₀
    refine ⟨fun w => ?_, fun g hg => ?_, fun w v => ?_⟩
    · simp only [sympTwist]
      rw [hker, exists_smul_iff, exists_smul_iff, reduceMod_liftMod]
      exact LinearEquiv.map_eq_zero_iff _
    · obtain ⟨w, hw⟩ := hsurj g hg
      refine ⟨liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)).symm (reduceMod M w)), ?_⟩
      simp only [sympTwist]
      rw [reduceMod_liftMod, LinearEquiv.apply_symm_apply, ← hw]
      congr 1
      exact hres (reduceMod_liftMod _)
    · simp only [sympTwist]
      have key : z ^ (2 * omegaStd w v) = z₀ ^ (2 * omegaStd
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M w)))
          (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M v)))) := by
        rw [hz', ← zpow_natCast, ← zpow_mul]
        apply zpow_eq_of_cast_eq z₀ hz₀M
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod, ha]
        ring
      rw [key]
      exact hweil _ _

theorem exists_sympActs : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∃ ρ : sympSimGrp h M → (X ⟶ X), ρ 1 = 𝟙 X ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ SympActs s s₁ u lev ρ := by
  intro p _ D R _ b N h M hM X s s₁ u lev hlev huniv
  haveI : NeZero M := ⟨hM.ne'⟩
  have hζ := isPrimitiveRoot_zetaAway hM.ne'
  have hζM : zetaAway M ^ M = 1 := hζ.pow_eq_one
  have hadd := hlev.1
  have htor := hlev.2.1
  have hres : ∀ {x y : Fin h ⊕ Fin h → ℤ}, reduceMod M x = reduceMod M y → lev x = lev y :=
    fun hxy => lev_eq_of_reduce hM lev hadd htor hxy
  choose n hn hcop h0 using fun a : sympSimGrp h M => exists_mult a
  have hσex : ∀ a, ∃ σ : cycAway M →+* cycAway M, σ (zetaAway M) = zetaAway M ^ n a := fun a =>
    let ⟨σ, hσ⟩ := exists_cycAway_aut hM.ne' (hcop a); ⟨σ.toRingHom, hσ⟩
  choose σ hσ using hσex
  have hU : ∀ a, ∃! f : X ⟶ X, f ≫ s = s ∧ f ≫ s₁ = s₁ ≫ spMap (σ a) ∧
      ∃ m : ObjMap u u f, ∀ x, (sympTwist a lev x).left ≫ m.φ = f ≫ (lev x).left :=
    fun a => huniv X s (s₁ ≫ spMap (σ a)) u (sympTwist a lev)
      (isSympLev_twist hM u lev hlev a (n a) (hn a) (σ a) (hσ a))
  choose ρ hρ hρu using hU
  have hcons : ∀ a c, zetaAway M ^ n (a * c) = zetaAway M ^ (n a * n c) := by
    intro a c
    by_cases hh : h = 0
    · rw [h0 _ hh, h0 _ hh, h0 _ hh]
    · exact pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn _) (isMultOf_mul (hn a) (hn c)))
  have hone : zetaAway M ^ n 1 = zetaAway M := by
    by_cases hh : h = 0
    · rw [h0 _ hh, pow_one]
    · rw [pow_eq_of_cast_eq _ hζM (mult_unique (Nat.pos_of_ne_zero hh) _ (hn 1) isMultOf_one), pow_one]
  refine ⟨ρ, ?_, fun a c => ?_, fun a => ⟨(hρ a).1, ⟨n a, σ a, hn a, hσ a, (hρ a).2.1⟩, (hρ a).2.2⟩⟩
  · have hσ1 : σ 1 = RingHom.id _ := cycAway_hom_ext hM.ne' (by rw [hσ, hone]; rfl)
    refine (hρu 1 (𝟙 X) ⟨Category.id_comp _, ?_, ?_⟩).symm
    · rw [hσ1, Category.id_comp]
      simp [spMap]
    · refine ⟨idObjMap u, fun x => ?_⟩
      change (lev (liftMod (reduceMod M x))).left ≫ 𝟙 _ = 𝟙 X ≫ (lev x).left
      rw [Category.comp_id, Category.id_comp, hres (reduceMod_liftMod _)]
  · have hσmul : σ (a * c) = (σ a).comp (σ c) := cycAway_hom_ext hM.ne' (by
      rw [hσ, RingHom.comp_apply, hσ, map_pow, hσ, ← pow_mul, hcons])
    refine (hρu (a * c) (ρ a ≫ ρ c) ⟨?_, ?_, ?_⟩).symm
    · rw [Category.assoc, (hρ c).1, (hρ a).1]
    · rw [Category.assoc, (hρ c).2.1, ← Category.assoc, (hρ a).2.1, Category.assoc, hσmul, spMap, spMap, spMap,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · obtain ⟨ma, hma⟩ := (hρ a).2.2
      obtain ⟨mc, hmc⟩ := (hρ c).2.2
      refine ⟨ObjMapComp.comp ma mc, fun x => ?_⟩
      change (sympTwist (a * c) lev x).left ≫ ma.φ ≫ mc.φ = (ρ a ≫ ρ c) ≫ (lev x).left
      have e1 : sympTwist (a * c) lev x = sympTwist a lev
          (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))) := by
        simp only [sympTwist, reduceMod_liftMod]
        rfl
      rw [e1, ← Category.assoc, hma, Category.assoc]
      change ρ a ≫ (sympTwist c lev x).left ≫ mc.φ = _
      rw [hmc, Category.assoc]

end GlobalTheory.UPel.HT.SympAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticSimilitudeActionOnLevelFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticSimilitude_action_on_levelFamily : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
    ∃ ρ : sympSimGrp h M → (X ⟶ X), ρ 1 = 𝟙 X ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ SympActs s s₁ u lev ρ := by
  first | exact @GlobalTheory.UPel.HT.SympAct.exists_sympActs | exact GlobalTheory.UPel.HT.SympAct.exists_sympActs | (intros; apply GlobalTheory.UPel.HT.SympAct.exists_sympActs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfLocalEqPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZM.IsGaloisCover

theorem eq_of_local_eq_pullback : ∀ (X Y S Z : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (g : S ⟶ Y) (h₁ h₂ : S ⟶ Z), GlobalTheory.ZM.IsGaloisCover Ga ρ π → (∀ q : ↥(pullback g π), ∃ V : (pullback g π).Opens, q ∈ V ∧ V.ι ≫ pullback.fst g π ≫ h₁ = V.ι ≫ pullback.fst g π ≫ h₂) → h₁ = h₂ := by
  intro X Y S Z π Ga _ ρ g h₁ h₂ h hloc
  have hp : IsPullback (pullback.snd g π) (pullback.fst g π) π g := (IsPullback.of_hasPullback g π).flip
  have : Etale (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
  have : IsFinite (pullback.fst g π) := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
  have : Surjective (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
  have e : pullback.fst g π ≫ h₁ = pullback.fst g π ≫ h₂ :=
    Scheme.hom_ext_of_forall _ _ fun q ↦ hloc q
  exact (cancel_epi (pullback.fst g π)).1 e

end GlobalTheory.ZM.IsGaloisCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatio
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.HTQuot

theorem objMap_comp_φ_of_comp {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := _root_.GlobalTheory.HTQuotRigid.objMap_comp_φ (p := p) (D := D) (R := R) (b := b) (N := N) (S₁ := S₁) (S₂ := S₂) (S₃ := S₃) (s₁ := s₁) (s₂ := s₂) (s₃ := s₃) (o₁ := o₁) (o₂ := o₂) (o₃ := o₃) (f := f) (g := g) h₁ h₂

theorem obj_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (G : Type)
    [Group G] (ρ : G → (X ⟶ X)) (o : Obj b N (π ≫ sY)), GlobalTheory.ZM.IsGaloisCover G ρ π → IsQProjOver (π ≫ sY) →
    IsQProjOver sY → (∀ a, Nonempty (ObjMap o o (ρ a))) → ∃ oY : Obj b N sY, Nonempty (ObjMap o oY π) := by
  intro p _ D R _ _ b N hN hNp X Y π sY G _ ρ o hG hq hqY hmaps
  have : IsLocallyNoetherian Y := by
    obtain ⟨M, i, hi, -, hi'⟩ := hqY
    have := isProper_str R M
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str R M)
  have m : ∀ a, ObjMap o o (ρ a) := fun a => (hmaps a).some
  let ν : G → (o.A.left ⟶ o.A.left) := fun a => (m a).φ
  have uniq : ∀ {f f' : X ⟶ X} (_ : f = f') (m₁ : ObjMap o o f) (m₂ : ObjMap o o f'), m₁.φ = m₂.φ := by
    rintro f f' rfl m₁ m₂
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp X X _ _ o o f m₁ m₂
  have ν1 : ν 1 = 𝟙 _ := by
    have key : ∀ {f : X ⟶ X} (_ : f = 𝟙 X) (m₁ : ObjMap o o f), m₁.φ = 𝟙 _ := by
      rintro f rfl m₁
      exact GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp X _ o m₁
    exact key hG.one (m 1)
  have νmul : ∀ a c, ν (a * c) = ν a ≫ ν c := by
    intro a c
    obtain ⟨m', hm'⟩ := objMap_comp_φ_of_comp (m a) (m c)
    exact (uniq (hG.mul a c) (m (a * c)) m').trans hm'
  have hcart : ∀ a, IsGrpPullback o.A o.A (ρ a) (ν a) := fun a => (m a).cart
  have hqA : IsQProjOver (o.A.hom ≫ π ≫ sY) :=
    GlobalTheory.RelAmpleQProjNoeth.isQProjOver_of_relAmple_noeth R X (π ≫ sY) o.A _ hq (pull_isLB o.isLB _) o.ample
  obtain ⟨A₀, _, φ, hA₀, gp, hφ⟩ :=
    GlobalTheory.abelianScheme_descends_galoisCover_noetherian R X Y π sY G ρ o.A ν hG hqA o.ab hcart ν1 νmul
  have := hA₀.comm
  obtain ⟨act₀, hact⟩ := GlobalTheory.GaloisActDesc.exists_oActN_descend D.O X Y π G ρ o.A A₀ φ ν o.act hG o.ab hA₀ gp hφ
    hcart (fun a c => (m a).act c)
  obtain ⟨P₀, φ₂, hP₀, hsq, iso, rig0⟩ := GlobalTheory.SquareDescent.exists_bundle_descent X Y π G ρ o.A A₀ φ ν o.P hG o.ab
    hA₀ gp hφ hcart ν1 νmul o.isLB o.rig₁ (fun a => ⟨(m a).φ₂, (m a).sq, (m a).pol⟩)
  obtain ⟨rig₁, rig₂⟩ := GlobalTheory.T.descended_birigidified_bundle_trivial_on_axes X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.rig₁ o.rig₂
  have symm := GlobalTheory.T.descended_birigidified_bundle_swap_symmetric X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso rig0 o.symm
  have ample := GlobalTheory.T.relAmple_diagonal_descends_finiteEtaleGalois X Y π G ρ o.A A₀ φ φ₂ o.P P₀ hG o.ab hA₀ gp hsq o.isLB hP₀ iso o.ample
  have kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ A₀),
      (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, hk⟩ := o.kerP
    exact ⟨e, he, GlobalTheory.T.descended_polarisation_kernel_killed_same_integer X Y π G ρ o.A A₀ φ φ₂ o.P P₀ e hG o.ab hA₀ gp hsq o.isLB hP₀ iso hk⟩
  have rosati := GlobalTheory.T.rosati_condition_descends_galois_cover D.O (fun c => (D.star c).unop) X Y π G ρ o.A A₀ φ φ₂ o.P P₀ o.act act₀ hG o.ab hA₀ gp
    hsq o.isLB hP₀ iso rig0 hact o.rosati
  obtain ⟨eta₀, eta_add, eta_lin, eta_ker, heta⟩ := GlobalTheory.LevelSecDesc.levelSections_descend D.O D.La N X Y π G ρ o.A A₀ φ
    ν o.act act₀ o.eta hG gp hφ hact (fun a y => (m a).eta y) o.eta_add o.eta_lin o.eta_ker
  have lie := GlobalTheory.T.lie_condition_descends_finite_etale_galois_cover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lie
  have lieRank := GlobalTheory.T.lie_multiplicities_geometric_points_descend p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ hG o.ab hA₀ gp hact o.lieRank
  have geom := GlobalTheory.T.geometric_tate_level_condition_descends_galois_cover p D R b X Y π sY G ρ o.A A₀ φ o.act act₀ N φ₂ o.P P₀ o.eta eta₀ hG o.ab hA₀ gp hact hsq
    o.isLB hP₀ iso heta o.geom
  let oY : Obj b N sY :=
    { A := A₀, ab := hA₀, act := act₀, P := P₀, isLB := hP₀, rig₁ := rig₁, rig₂ := rig₂, symm := symm
      ample := ample, kerP := kerP, rosati := rosati, lie := lie, lieRank := lieRank, eta := eta₀,
      eta_add := eta_add, eta_lin := eta_lin, eta_ker := eta_ker, geom := geom }
  exact ⟨oY, ⟨⟨φ, φ₂, gp, hsq, hact, iso, heta⟩⟩⟩

theorem exists_repFam_of_levelCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R]
    [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (u : Obj b N s) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)),
    IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) →
    (∀ a, Nonempty (ObjMap u u (ρ a))) →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) →
    (∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : Ga → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧ y ≫ s = π₁ ≫ t ∧
        Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (o : Obj b N t) (x x' : T ⟶ X), x ≫ s = t → x' ≫ s = t →
      Nonempty (ObjMap o u x) → Nonempty (ObjMap o u x') →
      ∀ q : T, ∃ (V : T.Opens) (a : Ga), q ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') →
    ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N hN hNp X s u Ga _ _ ρ hq h1 hmul hbase hmaps hfree hcov huniq
  obtain ⟨Y, π, sY, hπs, hgal, hsep, hlft, -⟩ :=
    GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver_noetherian R X s Ga ρ hq h1 hmul hbase hfree
  have hqY : IsQProjOver sY := GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover R X Y π sY Ga ρ
    hgal hsep hlft (by rw [hπs]; exact hq)
  subst hπs
  obtain ⟨uY, ⟨mu⟩⟩ := obj_descends_galoisCover p D R b N hN hNp X Y π sY Ga ρ u hgal hq hqY hmaps
  have hrep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s'),
      ∃! f : S ⟶ Y, f ≫ sY = s' ∧ Nonempty (ObjMap o uY f) := by
    intro S s' o
    obtain ⟨S₁, π₁, ρ₁, y, o', hgal₁, hequi, hys, ⟨m₁⟩, ⟨m₂⟩⟩ := hcov S s' o
    have hinv : ∀ a, ρ₁ a ≫ (y ≫ π) = y ≫ π := by
      intro a; rw [← Category.assoc, hequi a, Category.assoc, hgal.inv a]
    obtain ⟨f, hf, hfu⟩ := hgal₁.existsUnique_desc (y ≫ π) hinv
    have canc : ∀ {Z : Scheme.{0}} (h₁ h₂ : S ⟶ Z), π₁ ≫ h₁ = π₁ ≫ h₂ → h₁ = h₂ := by
      intro Z h₁ h₂ e
      obtain ⟨w, -, hwu⟩ := hgal₁.existsUnique_desc (π₁ ≫ h₁) (fun a => by rw [← Category.assoc, hgal₁.inv a])
      exact (hwu h₁ rfl).trans (hwu h₂ e.symm).symm
    have hfs : f ≫ sY = s' := canc _ _ (by rw [← Category.assoc, hf, Category.assoc, hys])
    have hmf : Nonempty (ObjMap o uY f) := by
      obtain ⟨m₃⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' u uY y π m₂ mu
      rw [← hf] at m₃
      exact GlobalTheory.T.harrisTaylor_moduliMap_descends_galoisCover p D R b N S S₁ Y s' sY π₁ Ga ρ₁ f o o' uY hN hNp hgal₁ m₁ m₃
    refine ⟨f, ⟨hfs, hmf⟩, ?_⟩
    rintro f' ⟨hf's, ⟨m'⟩⟩
    obtain ⟨m₄⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o' o uY π₁ f' m₁ m'
    obtain ⟨oT, ⟨mT⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ (pullback (π₁ ≫ f') π) (π₁ ≫ s')
      (pullback.fst (π₁ ≫ f') π) o'
    obtain ⟨mT1⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' u _ y mT m₂
    obtain ⟨mT2⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ oT o' uY _ _ mT m₄
    rw [pullback.condition] at mT2
    obtain ⟨mT3⟩ := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ oT u uY
      (pullback.snd (π₁ ≫ f') π) π).2 ⟨mT2⟩ ⟨mu⟩
    have key : y ≫ π = π₁ ≫ f' := by
      apply GlobalTheory.ZM.IsGaloisCover.eq_of_local_eq_pullback X Y S₁ Y π Ga ρ (π₁ ≫ f') (y ≫ π) (π₁ ≫ f') hgal
      intro q
      obtain ⟨V, a, hqV, hV⟩ := huniq _ _ oT (pullback.fst (π₁ ≫ f') π ≫ y) (pullback.snd (π₁ ≫ f') π)
        (by rw [Category.assoc, hys])
        (by rw [← Category.assoc, ← pullback.condition]; simp [hf's]) ⟨mT1⟩ ⟨mT3⟩ q
      refine ⟨V, hqV, ?_⟩
      calc V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ y ≫ π
          = (V.ι ≫ (pullback.fst (π₁ ≫ f') π ≫ y) ≫ ρ a) ≫ π := by simp [hgal.inv]
        _ = (V.ι ≫ pullback.snd (π₁ ≫ f') π) ≫ π := by rw [hV]
        _ = V.ι ≫ pullback.fst (π₁ ≫ f') π ≫ π₁ ≫ f' := by rw [Category.assoc, ← pullback.condition]
    exact hfu f' key.symm
  exact ⟨⟨Y, sY, uY, hrep⟩, hqY⟩

theorem exists_representing_family_of_level_structure : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  intro p _ D R _ _ b N M e hN hNp hM hodd hMp hep hMe hperf hrep
  obtain ⟨X, s, s₁, u, lev, hlev, hq, huniv⟩ := hrep
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨ρ, h1, hmul, hact⟩ := GlobalTheory.T.exists_symplecticSimilitude_action_on_levelFamily p D R b N _ M (by omega) X s s₁ u lev hlev huniv
  exact exists_repFam_of_levelCover p D R b N hN hNp X s u _ ρ hq h1 hmul (fun a => (hact a).1)
    (fun a => let ⟨m, _⟩ := (hact a).2.2; ⟨m⟩)
    (GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one p D R b N _ M hN hNp (by omega) X s s₁ u lev hlev ρ hact)
    (GlobalTheory.T.symplectic_level_over_cyclotomic p D R b N M e hN hNp hM hodd hMp hep hMe hperf X s s₁ u lev hlev huniv ρ hact)
    (GlobalTheory.T.exists_local_symplecticSimilitude_classifyingMaps p D R b N _ M hN hNp hM hodd hMp X s s₁ u lev hlev huniv ρ hact)

end GlobalTheory.HTQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  first | (exact @GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (exact GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (intros; apply GlobalTheory.HTQuot.exists_representing_family_of_level_structure <;> assumption)
end
