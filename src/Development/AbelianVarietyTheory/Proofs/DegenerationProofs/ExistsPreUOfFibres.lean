module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAbelianSchemeOfAbelianThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialFibreTestGeometricTest
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivLocal

open GlobalTheory.AbLaw GlobalTheory.UU

theorem ring_retraction {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] (φ : A →+* C) (hφ : φ.Finite)
    (ε : C →+* A) (he : ∀ a, ε (φ a) = a)
    (h : ∀ c, c - φ (ε c) ∈ (IsLocalRing.maximalIdeal A).map φ) (c : C) : φ (ε c) = c := by
  algebraize [φ]
  have hle : (⊤ : Submodule A C) ≤ LinearMap.range (Algebra.linearMap A C) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) fun x _ => ?_
    refine Submodule.mem_sup.2 ⟨φ (ε x), ⟨ε x, rfl⟩, x - φ (ε x), ?_, by ring⟩
    rw [Ideal.smul_top_eq_map]
    exact h x
  obtain ⟨a, rfl⟩ := hle (Submodule.mem_top (x := c))
  exact congrArg φ (he a)

theorem comp_section_eq_id_spec {A : Type} [CommRing A] [IsLocalRing A] {C : CommRingCat.{0}}
    (f : Spec C ⟶ Spec (CommRingCat.of A)) [hf : IsFinite f] (e : Spec (CommRingCat.of A) ⟶ Spec C)
    (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ Spec C),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ε, rfl⟩ := Spec.map_surjective e
  have hφ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hf
  have he' : φ ≫ ε = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, he, Spec.map_id])
  let I : Ideal C := (IsLocalRing.maximalIdeal A).map φ.hom
  let τ : IsLocalRing.ResidueField A →+* C ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp φ.hom) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have k := h _ (spMap τ) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)
  rw [← Spec.map_comp, ← Spec.map_comp] at k
  have k' := Spec.map_injective k
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  refine ring_retraction φ.hom hφ ε.hom (fun a => congrArg (fun q => q.hom a) he') (fun x => ?_) c
  exact Ideal.Quotient.eq.1 (congrArg (fun q => q.hom x) k').symm

theorem comp_section_eq_id {A : Type} [CommRing A] [IsLocalRing A] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of A)) [IsFinite f] (e : Spec (CommRingCat.of A) ⟶ H) (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ H),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  have : IsAffine H := isAffine_of_isAffineHom f
  have k := comp_section_eq_id_spec (H.isoSpec.inv ≫ f) (e ≫ H.isoSpec.hom) (by simpa using he)
    fun T t y hy => by
      have := h T t (y ≫ H.isoSpec.inv) (by simpa using hy)
      simp only [Category.assoc] at this ⊢
      rw [reassoc_of% this]
      simp
  rw [← cancel_epi H.isoSpec.inv, ← cancel_mono H.isoSpec.hom]
  simpa using k

theorem kTriv_of_closed_fibre : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  intro hLaws _ A _ _ _ B _ _ hB L hLB hL hk
  have hG := hLaws.globalFns
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG A B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG A B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ (T : Over (Spec (CommRingCat.of A))) (x : T ⟶ B), InK B L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (inK_one hLB (𝟙_ _))
  have h := isGrpPullback_pullback B (spMap (IsLocalRing.residue A))
  have hL' : (L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))).IsLB := DVR.linComb_isLB _ hLB _ _
  have key : H.hom ≫ e.left = 𝟙 _ := by
    refine comp_section_eq_id H.hom e.left (Over.w e) fun T t y hy => ?_
    have hdi : (y ≫ j.left) ≫ B.hom = t ≫ spMap (IsLocalRing.residue A) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ (Over.pullback (spMap (IsLocalRing.residue A))).obj B :=
      Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (IsLocalRing.residue A)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := InK.eq_one hk (inK_of_push h hLB hL' (lbIso_self hL') x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : z ≫ toUnit H ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, Category.assoc, he, MonObj.comp_one, MonObj.comp_one]
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    exact (congrArg (fun q => y ≫ q ≫ e.left) h2).symm.trans (congrArg (fun q => q.left) h1)
  have hj1 : j = 1 := by
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    have h1 : toUnit H ≫ e = 𝟙 H :=
      Over.OverMorphism.ext ((congrArg (fun q => q ≫ e.left) h2).trans key)
    rw [← Category.id_comp j, ← h1, Category.assoc, he, MonObj.comp_one]
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRingStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_of_closed_fibre_localRing : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  first | exact @GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | exact GlobalTheory.KTrivLocal.kTriv_of_closed_fibre | (intros; apply GlobalTheory.KTrivLocal.kTriv_of_closed_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAlgebraisationFormalTowerAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAlgebraisationFormalTowerAmple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TowerAlg

theorem isPullback_of_grp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {f : S' ⟶ S}
    {F : B'.left ⟶ B.left} (h : IsGrpPullback B' B f F) : IsPullback F B'.hom B.hom f := h.1

theorem exists_alg (hG : GlobalFnsSt) (hE : Ega) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
    (hA : admitted R I) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)]
    [∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e)) (N : ∀ e, CP (Y e))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (h : ∀ e, IsCPPullback (N e) (N (e + 1)) (thickTrans R I e) (β e))
    (hamp : RelAmple (Y 0) (N 0).L.L) :
    ∃ (B : Over (Spec (CommRingCat.of R))) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : CP B)
      (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ RelAmple B Q.L.L ∧
      (∀ e, IsCPPullback (N e) Q (thick R I e) (b e)) ∧ ∀ e, β e ≫ b (e + 1) = b e := by
  have hN : IsNoetherianRing R := hA.1.1
  have hI : I ≠ ⊤ := hA.2.2.2.1.ne_top
  have hc : IsAdicComplete I R := hA.1.2.2.2
  choose hβ v hv using h
  obtain ⟨B, M, b, hp, hs, hM, ha, hb, hβb, hiso⟩ := hE.1 R I hI hc hA.2.1 Y β
    (fun e => (N e).L.L) v (fun e => isPullback_of_grp (hβ e)) (fun e => (hY e).smooth)
    (fun e => ⟨(N e).L.isLB, (hv e).gen⟩) hamp
  obtain ⟨g, hB, hg⟩ := GlobalTheory.T.isAbelianScheme_of_abelian_thickenings hE R I hA Y β hY hβ B b hp hs hb hβb
  have c := hB.comm
  obtain ⟨Q, hQ, hq⟩ := exists_cp_alg hG hE.2.2.1 hI hc N hB hp hg hM hiso hY
  exact ⟨B, g, c, Q, b, hB, by rw [hQ]; exact ha, hq, hβb⟩

theorem nonempty_alg : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  intro hL _ hE R _ _ _ I hA G _ _ P X _ T hamp
  obtain ⟨B, _, _, Q, b, h₁, h₂, h₃, h₄⟩ := exists_alg hL.globalFns hE hA (fun e => (T.l e).Q.B)
    (fun e => (T.l e).Q.isAb) (fun e => (T.l e).D.M) T.β T.β_pb hamp
  exact ⟨⟨B, h₁, Q, h₂, b, h₃, h₄⟩⟩

end GlobalTheory.TowerAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAlgebraisationFormalTowerAmpleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_algebraisation_formal_tower_ample : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  first | exact @GlobalTheory.TowerAlg.nonempty_alg | exact GlobalTheory.TowerAlg.nonempty_alg | (intros; apply GlobalTheory.TowerAlg.nonempty_alg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdditiveWeightPointsOfTorusTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtGenPullIff
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.WeightPoint

section Sum
variable {S : Scheme.{0}} (B : Over S) [GrpObj B] {Y Y' : Scheme.{0}}

def IsSum (a b c : Y ⟶ B.left) : Prop :=
  ∃ (s : Y ⟶ S) (a₀ b₀ : Over.mk s ⟶ B), a₀.left = a ∧ b₀.left = b ∧ (a₀ * b₀).left = c

variable {B}

theorem isSum_mul {T : Over S} (a b : T ⟶ B) : IsSum B a.left b.left (a * b).left := ⟨T.hom, a, b, rfl, rfl, rfl⟩

theorem IsSum.unique {a b c c' : Y ⟶ B.left} (h : IsSum B a b c) (h' : IsSum B a b c') : c = c' := by
  obtain ⟨s, a₀, b₀, rfl, rfl, rfl⟩ := h
  obtain ⟨s', a₁, b₁, ha, hb, rfl⟩ := h'
  obtain rfl : s = s' := (Over.w a₀).symm.trans ((congrArg (· ≫ B.hom) ha.symm).trans (Over.w a₁))
  rw [Over.OverMorphism.ext ha, Over.OverMorphism.ext hb]

theorem IsSum.comp {a b c : Y ⟶ B.left} (h : IsSum B a b c) (r : Y' ⟶ Y) {a' b' : Y' ⟶ B.left} (ha : a' = r ≫ a)
    (hb : b' = r ≫ b) : IsSum B a' b' (r ≫ c) := by
  obtain ⟨s, a₀, b₀, rfl, rfl, rfl⟩ := h
  let ρ : Over.mk (r ≫ s) ⟶ Over.mk s := Over.homMk r rfl
  exact ⟨r ≫ s, ρ ≫ a₀, ρ ≫ b₀, ha.symm, hb.symm, congrArg (fun q => q.left) (MonObj.comp_mul ρ a₀ b₀).symm⟩

theorem point_eq_of_lbIso {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L) {S' : Scheme.{0}} {f : S' ⟶ S}
    {b : Y ⟶ B.left} {p : Y ⟶ S'} (pb : IsPullback b p B.hom f) {x y : S' ⟶ B.left} (hx : x ≫ B.hom = f)
    (hy : y ≫ B.hom = f) {τ τ' : Y ⟶ B.left} (hτ : IsSum B (p ≫ x) b τ) (hτ' : IsSum B (p ≫ y) b τ')
    (H : LBIso (LB.LinComb L (K := Fin 2) ![τ, b] ![-1, 1]) (LB.LinComb L (K := Fin 2) ![τ', b] ![-1, 1])) :
    x = y := by
  have H₁ := hasGen_sum_of_lbIso L _ _ _ _ H
  let T : Over S := Over.mk f
  let x₀ : T ⟶ B := Over.homMk x hx
  let y₀ : T ⟶ B := Over.homMk y hy
  let w : T ⊗ B ⟶ B := (fst T B ≫ y₀⁻¹) * snd T B
  let h : (T ⊗ B).left ⟶ Y := pb.lift w.left (fst T B).left ((Over.w w).trans (Over.w (fst T B)).symm)
  have hb : h ≫ b = w.left := pb.lift_fst _ _ _
  have hp : h ≫ p = (fst T B).left := pb.lift_snd _ _ _
  have key : ∀ (d : T ⟶ B) (σ : Y ⟶ B.left), IsSum B (p ≫ d.left) b σ → h ≫ σ = (translPt B (d * y₀⁻¹)).left :=
    fun d σ hσ => by
      have e : (fst T B ≫ d) * w = translPt B (d * y₀⁻¹) := by
        change _ = (fst T B ≫ (d * y₀⁻¹)) * snd T B
        rw [MonObj.comp_mul, _root_.mul_assoc]
      rw [← e]
      exact (hσ.comp h (by rw [← Category.assoc, hp]; rfl) hb.symm).unique (isSum_mul (fst T B ≫ d) w)
  have k₁ : h ≫ τ' = (snd T B).left := by
    rw [key y₀ τ' hτ', mul_inv_cancel, KerPow.translPt_one]
  have H₂ := H₁.pull h (φ' := Sum.elim ![(snd T B).left, w.left] ![(translPt B (x₀ * y₀⁻¹)).left, w.left]) fun k => by
    rcases k with k | k <;> fin_cases k
    exacts [k₁, hb, key x₀ τ hτ, hb]
  have triv : KerPow.HasGen L (Y := (T ⊗ B).left) (K := Fin 0) ![] ![] :=
    KerPow.hasGen_of_trivial hL fun U _ h => by simp
  have H₃ := H₂.comb hL triv (φ'' := ![(translPt B (x₀ * y₀⁻¹)).left, (snd T B).left]) (ε'' := ![1, -1])
    fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
      apply Additive.ofMul.injective
      simp
      abel
  exact congrArg (fun q => q.left) (mul_inv_eq_one.1
    (KerPow.eq_one_of_locGen hK (x₀ * y₀⁻¹) fun _ => ⟨⊤, trivial, H₃.pull _ fun _ => rfl⟩))

end Sum

section Wt
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {X : Type} [AddCommGroup X]

def HasWtGen (i : splitTorus S X ⟶ G) (M : LB G.left) (χ : X) : Prop :=
  ∃ u : LB.Gen M, u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ

variable {i : splitTorus S X ⟶ G} {χ : X}

theorem HasWtGen.chartPull {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F)
    {i' : splitTorus S' X ⟶ G'} (hi : TorusCompat f F i' i) {M : LB G.left} {M' : LB G'.left} (a : ChartPull M' M F)
    (H : HasWtGen i M χ) : HasWtGen i' M' χ := by
  obtain ⟨t, ht, hw⟩ := H
  refine ⟨⟨fun i => res (a.le i) (pullU F _ (t.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_,
    fun j => (hw _).pull hF hi (a.le j)⟩
  have hm : F y ∈ M.U (a.idx i) ⊓ M.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := (gm_res F y _ hm _).symm.trans ((congrArg (gm F y _) (ht (a.idx i) (a.idx j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res F y _ hm _))))
  exact ((gm_res _ y _ hy _).trans (gm_rp₁ F y _ _ (a.le i) hy.1 _)).trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2) ((gm_res _ y _ hy _).trans (gm_rp₁ F y _ _ (a.le j) hy.2 _)))).symm)

theorem HasWtGen.chart {M M' : LB G.left} (a : ChartPull M' M (𝟙 _)) (H : HasWtGen i M χ) : HasWtGen i M' χ :=
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  H.chartPull (isGrpPullback_of_iso (Iso.refl G)) (TorusCompat.refl i) a

theorem hasWtGen_pull_iff {A Y : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ}
    {F : G.left ⟶ Y} {ψ : K → (G.left ⟶ A)} (e : ∀ k, ψ k = F ≫ φ k) :
    HasWtGen i ((LB.LinComb L φ ε).pull F) χ ↔ HasWtGen i (LB.LinComb L ψ ε) χ := by
  obtain rfl : ψ = fun k => F ≫ φ k := funext e
  exact ⟨.chart (chartPullIn L φ ε F), .chart (chartPullOut L φ ε F _ fun _ => rfl)⟩

theorem HasWtGen.inv {A : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {φ : K → (G.left ⟶ A)} {ε ε' : K → ℤ}
    (e : ∀ k, ε' k = -ε k) (H : HasWtGen i (LB.LinComb L φ ε) (-χ)) : HasWtGen i (LB.LinComb L φ ε') χ := by
  obtain rfl : ε' = fun k => -ε k := funext e
  obtain ⟨t, ht, hw⟩ := H
  exact ⟨LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun j => neg_neg χ ▸ (hw j).inv⟩

theorem HasWtGen.of_lbIso {Y : Scheme.{0}} {F : G.left ⟶ Y}
    (hF : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F = g.left ≫ F)
    {N N' : LB Y} (hN : N.IsLB) (hN' : N'.IsLB) (H : LBIso N N') (h : HasWtGen i (N.pull F) χ) :
    HasWtGen i (N'.pull F) χ := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullId N) (Geo.Tor.chartPullPull N' (𝟙 Y) (𝟙 Y) rfl)
  obtain ⟨a, ha, hχ⟩ := h
  obtain ⟨u, hu, hv⟩ := exists_up ((isGen_iff w).1 hw) hN' hN a ha
  rw [← Category.comp_id F]
  refine ⟨u, hu, fun p => isWt_of_gm _ _ fun Z t g z m₂ => ?_⟩
  obtain ⟨q, hq⟩ := exists_chart hN (F (g.left z))
  have e : F (((t ≫ i) * g).left z) = F (g.left z) := congrArg (fun q => q z) (hF Z t g)
  have n₂ : g.left z ∈ (N.pull F).U fun _ => q := mem_pull.2 hq
  have n₁ : ((t ≫ i) * g).left z ∈ (N.pull F).U fun _ => q := mem_pull.2 (e ▸ hq)
  have m₁ : ((t ≫ i) * g).left z ∈ (N'.pull (F ≫ 𝟙 Y)).U p := by
    have : F (g.left z) ∈ N'.U (p PUnit.unit) := mem_pull.1 m₂
    exact mem_pull.2 (show F _ ∈ N'.U (p PUnit.unit) from e ▸ this)
  refine (hv _ _ z p _ m₁ n₁).trans (Eq.trans ?_ (congrArg _ (hv _ _ z p _ m₂ n₂).symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ (gm_eq_of_isWt (hχ _) t g z n₁ n₂)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.pw
  simp only [hF]

end Wt

section Rep
variable {S S' S'' : Scheme.{0}} {B : Over S} [GrpObj B] {G : Over S'} [GrpObj G] {G' : Over S''} [GrpObj G']
  {X : Type} [AddCommGroup X]

def Rep (Q : TQ G X) (L : LB B.left) (b : Q.B.left ⟶ B.left) (x : S' ⟶ B.left) (χ : X) : Prop :=
  ∃ τ, IsSum B (Q.B.hom ≫ x) b τ ∧
    HasWtGen Q.i ((LB.LinComb L (K := Fin 2) ![τ, b] ![-1, 1]).pull Q.q.left) χ

variable {Q : TQ G X} {L : LB B.left} {b : Q.B.left ⟶ B.left} {χ : X}

theorem Rep.unique (hL : L.IsLB) (hK : KTriv B L) {f : S' ⟶ S} (pb : IsPullback b Q.B.hom B.hom f)
    {x y : S' ⟶ B.left} (hx : x ≫ B.hom = f) (hy : y ≫ B.hom = f) (h : Rep Q L b x χ) (h' : Rep Q L b y χ) :
    x = y := by
  obtain ⟨τ, hτ, u, hu⟩ := h
  obtain ⟨τ', hτ', u', hu'⟩ := h'
  exact point_eq_of_lbIso hL hK pb hx hy hτ hτ' (lbIso_of_genWt _ _ _ Q _ _ u u' χ (DVR.linComb_isLB _ hL _ _)
    (DVR.linComb_isLB _ hL _ _) hu hu')

theorem Rep.pull {Q' : TQ G' X} {g : S'' ⟶ S'} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G g F)
    (hi : TorusCompat g F Q'.i Q.i) {β : Q'.B.left ⟶ Q.B.left} (hβ : β ≫ Q.B.hom = Q'.B.hom ≫ g)
    (hq : Q'.q.left ≫ β = F ≫ Q.q.left) {b' : Q'.B.left ⟶ B.left} (hb : β ≫ b = b') {x : S' ⟶ B.left}
    (h : Rep Q L b x χ) : Rep Q' L b' (g ≫ x) χ := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨β ≫ τ, hτ.comp β (by rw [← Category.assoc, ← hβ, Category.assoc]) hb.symm,
    (hasWtGen_pull_iff fun _ => rfl).2 (((hasWtGen_pull_iff fun _ => rfl).1 h).chartPull hF hi
      (chartPullSame L _ _ _ F fun k => ?_))⟩
  fin_cases k
  · show Q'.q.left ≫ β ≫ τ = F ≫ Q.q.left ≫ τ
    rw [reassoc_of% hq]
  · show Q'.q.left ≫ b' = F ≫ Q.q.left ≫ b
    rw [← hb, reassoc_of% hq]

theorem Rep.section {f : S' ⟶ S} (w : b ≫ B.hom = Q.B.hom ≫ f) (c : 𝟙_ _ ⟶ B) (h : Rep Q L b (f ≫ c.left) χ) :
    HasWtGen Q.i ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)) χ := by
  obtain ⟨τ, hτ, h⟩ := h
  have e : τ = b ≫ ((toUnit B ≫ c) * 𝟙 B).left := hτ.unique ((isSum_mul (toUnit B ≫ c) (𝟙 B)).comp b (by
    rw [Over.comp_left, Rosenlicht.toUnit_left, ← Category.assoc, ← w, Category.assoc]) (Category.comp_id b).symm)
  refine (hasWtGen_pull_iff (ψ := fun k => Q.q.left ≫ ![τ, b] k) fun k => ?_).2
    ((hasWtGen_pull_iff fun _ => rfl).1 h)
  fin_cases k
  · exact (congrArg (Q.q.left ≫ ·) e).trans (Category.assoc _ _ _).symm
  · exact (Category.comp_id _).symm

end Rep

theorem exists_rep (hP : PicardZeroDegenerationCondition) {R A : Type} [CommRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {B : Over (Spec (CommRingCat.of R))} [GrpObj B] [IsCommMonObj B] (M : CP B) (hA : RelAmple B M.L.L)
    (hK : KTriv B M.L.L) {G : Over (Spec (CommRingCat.of A))} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    (Q : TQ G X) {f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)} {b : Q.B.left ⟶ B.left}
    (pb : IsGrpPullback Q.B B f b) (χ : X) : ∃ x, x ≫ B.hom = f ∧ Rep Q M.L.L b x χ := by
  have hL := M.L.isLB
  have hL' := pull_isLB hL b
  have hw := (isGen_iff _).1 (pullIso_isGen hL b)
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim A Q.B Q.isAb
  have hs : Sym B M.L.L := fun _ => ⟨⊤, trivial, by
    obtain ⟨u, hu, -⟩ := exists_gen (φ' := ![(B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left, (B.hom ⁻¹ᵁ ⊤).ι])
      (ε' := ![1, -1]) hL (fun U _ h => Finset.prod_congr rfl fun k _ => by
        fin_cases k
        exacts [rfl, congrArg (fun q => h q ^ (-1 : ℤ)) (Category.comp_id _)])
      _ (DVR.pullGen_isGen _ _ _ _ M.sym_gen (B.hom ⁻¹ᵁ ⊤).ι)
    exact ⟨u, hu⟩⟩
  let P : PolAV (Spec (CommRingCat.of A)) := ⟨Q.B, Q.isAb, g, hg, M.L.L.pull b, hL',
    PolBaseChange.rigidified_pull pb ⟨M.L.rig, M.L.rigGen⟩, PolBaseChange.sym_pull pb hs,
    relAmple_pull pb.1 hL hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hA, kTriv_pull pb hL hL' hw hK⟩
  obtain ⟨N, t, hN, ht, hΛ⟩ := WtBundle.exists_genWt Q (-χ)
  obtain ⟨x, hx⟩ := hP A P N hN hΛ
  replace hx : LBIso N (LB.LinComb (M.L.L.pull b) (K := Fin 2) ![((toUnit Q.B ≫ x) * 𝟙 Q.B).left, 𝟙 Q.B.left]
    ![1, -1]) := hx
  have H := hx.trans hN (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _) (iso_linComb hw _ _)
  have H₁ := HasWtGen.of_lbIso (i := Q.i) (fun Z x g => by
    rw [← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]) hN (DVR.linComb_isLB _ hL _ _) H ⟨t, ht⟩
  refine ⟨x.left ≫ b, ?_, ((toUnit Q.B ≫ x) * 𝟙 Q.B).left ≫ b, ?_, (hasWtGen_pull_iff fun _ => rfl).2
    (HasWtGen.inv (ε := ![1, -1]) (fun k => by fin_cases k <;> rfl) ((hasWtGen_pull_iff fun k => ?_).1 H₁))⟩
  · rw [Category.assoc, pb.1.w, ← Category.assoc, Over.w x]
    exact Category.id_comp _
  · refine ⟨_, pushPt pb.1.w (toUnit Q.B ≫ x), pushPt pb.1.w (𝟙 Q.B), ?_, Category.id_comp b,
      pb.2 _ _ _ _ _ rfl rfl⟩
    show (toUnit Q.B ≫ x).left ≫ b = _
    rw [Over.comp_left, Rosenlicht.toUnit_left, Category.assoc]
  · fin_cases k
    exacts [rfl, congrArg (Q.q.left ≫ ·) (Category.id_comp b).symm]

end GlobalTheory.WeightPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdditiveWeightPointsOfTorusTower
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.WeightPoint

theorem w_of_isCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B'] [GrpObj B]
    [IsCommMonObj B] {M' : CP B'} {M : CP B} {f : S' ⟶ S} {β : B'.left ⟶ B.left} (h : IsCPPullback M' M f β) :
    β ≫ B.hom = B'.hom ≫ f := by
  obtain ⟨h, -⟩ := h
  exact h.1.w

section Tower
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]
  {T : TowerR I P X} (a : T.Alg)


omit [IsDomain R] [IsLocalRing R] [IsCommMonObj G] in
theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel ((isGrpPullback_pullback G (thick R I e)).congr
    (thickTrans_comp R I e).symm ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm)
    (pullback.lift_snd _ _ _)


omit [IsDomain R] in
theorem exists_section [IsAdicComplete I R] {B : Over (Spec (CommRingCat.of R))}
    (x : ∀ e : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ B.left) (hx : ∀ e, x e ≫ B.hom = thick R I e)
    (hc : ∀ e, thickTrans R I e ≫ x (e + 1) = x e) : ∃ c : 𝟙_ _ ⟶ B, ∀ e, thick R I e ≫ c.left = x e := by
  obtain ⟨c, ⟨h₁, h₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (I := I) (f := x) (𝟙 _) B.hom hc
    fun e => (hx e).trans (Category.comp_id _).symm
  exact ⟨Over.homMk c h₁, h₂⟩

theorem isGrpPullback_level (e : ℕ) : IsGrpPullback (T.l e).Q.B a.B (thick R I e) (a.b e) := by
  obtain ⟨h, -⟩ := a.b_pb e
  exact h

theorem exists_rep_level (hP : PicardZeroDegenerationCondition) [IsNoetherianRing R] (hI : I ≠ ⊤) (hK : KTriv a.B a.M.L.L) (χ : X) (e : ℕ) :
    ∃ x, x ≫ a.B.hom = thick R I e ∧ Rep (T.l e).Q a.M.L.L (a.b e) x χ :=
  have := isLocalRing_quotient_pow hI e
  exists_rep hP a.M a.ample hK (T.l e).Q (isGrpPullback_level a e) χ

theorem rep_level_pull {χ : X} {e : ℕ} {x} (h : Rep (T.l (e + 1)).Q a.M.L.L (a.b (e + 1)) x χ) :
    Rep (T.l e).Q a.M.L.L (a.b e) (thickTrans R I e ≫ x) χ :=
  Rep.pull (Q := (T.l (e + 1)).Q) (Q' := (T.l e).Q) (isGrpPullback_thickMap e) (T.tor e)
    (w_of_isCPPullback (T.β_pb e)) (T.β_q e) (a.b_β e) h

theorem exists_repWt (hP : PicardZeroDegenerationCondition) [IsNoetherianRing R] [IsAdicComplete I R] (hK : KTriv a.B a.M.L.L) (χ : X) :
    ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  choose x hx hr using exists_rep_level a hP (ne_top_of_isHausdorff I) hK χ
  obtain ⟨c, hc⟩ := exists_section x hx fun e => Rep.unique a.M.L.isLB hK (isGrpPullback_level a e).1
    (by rw [Category.assoc, hx, thickTrans_comp]) (hx e) (rep_level_pull a (hr (e + 1))) (hr e)
  refine ⟨c, fun e => Rep.section (isGrpPullback_level a e).1.w c ?_⟩
  rw [hc]
  exact hr e

theorem repWt_unique [IsHausdorff I R] (hK : KTriv a.B a.M.L.L) {χ : X} {c c' : 𝟙_ _ ⟶ a.B}
    (hc : ∀ e, a.RepWt c χ e) (hc' : ∀ e, a.RepWt c' χ e) : c = c' := by
  refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isHausdorff I fun e => ?_)
  obtain ⟨pb, -⟩ := a.b_pb e
  have k := section_eq_of_isWt a.M.L.isLB hK c c' (T.l e).Q pb.1 χ (hc e) (hc' e)
  rw [Over.comp_left, Over.comp_left, Rosenlicht.toUnit_left] at k
  exact k

theorem repWt_add {χ χ' : X} {c c' : 𝟙_ _ ⟶ a.B} {e : ℕ} (h : a.RepWt c χ e) (h' : a.RepWt c' χ' e) :
    a.RepWt (c * c') (χ + χ') e := by
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end Tower

theorem exists_weightPoints : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X) (a : T.Alg), KTriv a.B a.M.L.L → ∃ c : X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  intro _ _ hE R _ _ _ I hR G _ _ P X _ T a hK
  have := hR.1.1
  have := hR.1.2.2.2
  choose c hc using exists_repWt a hE.2.2.2 hK
  exact ⟨c, fun χ χ' => repWt_unique a hK (hc _) fun e => repWt_add a (hc χ e) (hc χ' e), hc⟩

end GlobalTheory.WeightPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdditiveWeightPointsOfTorusTowerStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_weightPoints_of_torusTower : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X) (a : T.Alg), KTriv a.B a.M.L.L → ∃ c : X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  first | exact @GlobalTheory.WeightPoint.exists_weightPoints | exact GlobalTheory.WeightPoint.exists_weightPoints | (intros; apply GlobalTheory.WeightPoint.exists_weightPoints <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.PreUnifLocal

section Quot
variable {Y A B : Scheme.{0}} {N : LB Y} {L : LB A} {M : LB B} {F : Y ⟶ A} {p : Y ⟶ B}

def IsQuotIso (u : LB.Iso N (L.pull F)) (v : LB.Iso N (M.pull p)) (w : LB.Iso (L.pull F) (M.pull p)) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (j : M.ι) (k : L.ι) (m : N.ι), p (x z) ∈ M.U j → F (x z) ∈ L.U k →
    x z ∈ N.U m → gw v x z j m = gw w x z j (fun _ => k) * gw u x z k m

theorem exists_isQuotIso (hN : N.IsLB) (hL : L.IsLB) (hM : M.IsLB) {u : LB.Iso N (L.pull F)}
    {v : LB.Iso N (M.pull p)} (hu : PGen u) (hv : PGen v) : ∃ w, IsQuotIso u v w := by
  have glue : ∀ (j : M.ι) (k : L.ι), ∃ s : Γ(Y, (M.pull p).U (fun _ => j) ⊓ (L.pull F).U (fun _ => k))ˣ,
      ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (m : N.ι), p (x z) ∈ M.U j → F (x z) ∈ L.U k → x z ∈ N.U m →
        gm x z _ s = gw v x z j m * (gw u x z k m)⁻¹ := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : N.ι → Y.Opens, ∀ m y, y ∈ W m ↔ p y ∈ M.U j ∧ F y ∈ L.U k ∧ y ∈ N.U m :=
      ⟨fun m => p ⁻¹ᵁ M.U j ⊓ (F ⁻¹ᵁ L.U k ⊓ N.U m), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ m, W m ≤ (M.pull p).U (fun _ => j) ⊓ (L.pull F).U (fun _ => k) := fun m y hy =>
      ⟨mem_pull.2 ((hW m y).1 hy).1, mem_pull.2 ((hW m y).1 hy).2.1⟩
    have l₁ : ∀ m, W m ≤ (M.pull p).U (fun _ => j) ⊓ N.U m := fun m y hy =>
      ⟨mem_pull.2 ((hW m y).1 hy).1, ((hW m y).1 hy).2.2⟩
    have l₂ : ∀ m, W m ≤ (L.pull F).U (fun _ => k) ⊓ N.U m := fun m y hy =>
      ⟨mem_pull.2 ((hW m y).1 hy).2.1, ((hW m y).1 hy).2.2⟩
    obtain ⟨a, ha⟩ : ∃ a : ∀ m, Γ(Y, W m)ˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (m : N.ι), x z ∈ W m →
        gm x z (W m) (a m) = gw v x z j m * (gw u x z k m)⁻¹ :=
      ⟨fun m => res (l₁ m) (v.s (fun _ => j, m)) * (res (l₂ m) (u.s (fun _ => k, m)))⁻¹, fun Z x z m hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res x z (l₁ m) hy _)
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res x z (l₂ m) hy _))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun y hy => by
        obtain ⟨m, hm⟩ := exists_chart hN y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, (hW m y).2 ⟨mem_pull.1 hy.1, mem_pull.1 hy.2, hm⟩⟩) a
      (fun m m' y hy => by
        have h₁ := (hW m y).1 hy.1
        have h₂ := (hW m' y).1 hy.2
        rw [ha _ (𝟙 Y) y m hy.1, ha _ (𝟙 Y) y m' hy.2, hv _ (𝟙 Y) y j j m m' h₁.1 h₁.1 h₁.2.2 h₂.2.2,
          hu _ (𝟙 Y) y k k m m' h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2, gm_self hM (𝟙 Y ≫ p) y h₁.1,
          gm_self hL (𝟙 Y ≫ F) y h₁.2.1]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z x z m hj hk hm => ?_⟩
    have hy := (hW m (x z)).2 ⟨hj, hk, hm⟩
    exact (gm_res x z (l₀ m) hy s).symm.trans ((congrArg (gm x z (W m)) (hs m)).trans (ha Z x z m hy))
  choose s hs using glue
  refine ⟨⟨fun c => s (c.1 PUnit.unit) (c.2 PUnit.unit)⟩, fun Z x z j k m hj hk hm => ?_⟩
  exact (inv_mul_cancel_right _ _).symm.trans (congrArg (· * gw u x z k m) (hs j k Z x z m hj hk hm).symm)

theorem IsQuotIso.isGen (hN : N.IsLB) {u : LB.Iso N (L.pull F)} {v : LB.Iso N (M.pull p)} (hu : PGen u)
    (hv : PGen v) {w : LB.Iso (L.pull F) (M.pull p)} (h : IsQuotIso u v w) : w.IsGen := by
  refine (isGen_iff _).2 fun Z x z j j' k k' hj hj' hk hk' => ?_
  obtain ⟨m, hm⟩ := exists_chart hN (x z)
  have a := hv _ x z j j' m m hj hj' hm hm
  rw [h _ x z j (k PUnit.unit) m hj (mem_pull.1 hk) hm, h _ x z j' (k' PUnit.unit) m hj' (mem_pull.1 hk') hm,
    hu _ x z (k PUnit.unit) (k' PUnit.unit) m m (mem_pull.1 hk) (mem_pull.1 hk') hm hm] at a
  rw [gm_pull_g L F x z k k' hk hk']
  change gw w x z j (fun _ => k PUnit.unit) = _ * gw w x z j' (fun _ => k' PUnit.unit)
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

theorem exists_ratio (hN : N.IsLB) (hM : M.IsLB) {v v' : LB.Iso N (M.pull p)} (hv : PGen v) (hv' : PGen v') :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) (j : M.ι) (m : N.ι), p (x z) ∈ M.U j → x z ∈ N.U m →
      gw v' x z j m = gm x z ⊤ a * gw v x z j m := by
  let W : M.ι × N.ι → Y.Opens := fun c => (M.pull p).U (fun _ => c.1) ⊓ N.U c.2
  let b : ∀ c, Γ(Y, W c)ˣ := fun c => v'.s (fun _ => c.1, c.2) * (v.s (fun _ => c.1, c.2))⁻¹
  have hb : ∀ (Z : Scheme.{0}) (x : Z ⟶ Y) (z : Z) c,
      gm x z (W c) (b c) = gw v' x z c.1 c.2 * (gw v x z c.1 c.2)⁻¹ := fun Z x z c =>
    (map_mul _ _ _).trans (congrArg (gw v' x z c.1 c.2 * ·) (map_inv _ _))
  obtain ⟨a, ha⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hM (p y)
      obtain ⟨m, hm⟩ := exists_chart hN y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, m), mem_pull.2 hj, hm⟩) b (fun c c' y hy => by
      rw [hb, hb, hv _ (𝟙 Y) y c.1 c'.1 c.2 c'.2 (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) hy.1.2 hy.2.2,
        hv' _ (𝟙 Y) y c.1 c'.1 c.2 c'.2 (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) hy.1.2 hy.2.2]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨a, fun Z x z j m hj hm => ?_⟩
  have := (gm_res x z le_top (show x z ∈ W (j, m) from ⟨mem_pull.2 hj, hm⟩) a).symm.trans
    ((congrArg (gm x z (W (j, m))) (ha (j, m))).trans (hb Z x z (j, m)))
  rw [this, inv_mul_cancel_right]

end Quot

section Unique
variable {S S' : Scheme.{0}} {G : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B]

theorem gw_eq_of_isCPMap (hG : GlobalFnsSt) [ConnectedSpace S'] [ConnectedSpace G.left] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] (Q : TQ G X) {P : CP G} {M : CP B} {f : S' ⟶ S} {p : G.left ⟶ B.left} {hp} {v v'}
    (h : IsCPMap P M f p hp v) (h' : IsCPMap P M f p hp v') (Z : Scheme.{0}) (x : Z ⟶ G.left) (z : Z) (j m)
    (hj : p (x z) ∈ M.L.L.U j) (hm : x z ∈ P.L.L.U m) : gw v' x z j m = gw v x z j m := by
  obtain ⟨a, ha⟩ := exists_ratio P.L.isLB M.L.isLB ((isGen_iff _).1 h.gen) ((isGen_iff _).1 h'.gen)
  have key : ∀ (T : Over S') (z : T.left), gm (1 : T ⟶ G).left z ⊤ a = 1 ∧
      (∀ x : T ⟶ G, gm (x⁻¹).left z ⊤ a = gm x.left z ⊤ a) ∧ ∀ x y u : T ⟶ G,
        gm (x * y * u).left z ⊤ a * gm x.left z ⊤ a * gm y.left z ⊤ a * gm u.left z ⊤ a =
          gm (x * y).left z ⊤ a * gm (x * u).left z ⊤ a * gm (y * u).left z ⊤ a := by
    intro T z
    obtain ⟨J', hJ'⟩ := exists_good_pt P.L.isLB z
    obtain ⟨J, hJ⟩ := exists_good_pt M.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw v x.left z (J (x.left ≫ p)) (J' x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨U, hU⟩ : ∃ U : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ, ∀ x, gm x.left z ⊤ a = U x := ⟨_, fun _ => rfl⟩
    obtain ⟨a₁, a₂, a₃⟩ := h.vals T z J' J hJ' hJ W hW
    obtain ⟨b₁, b₂, b₃⟩ := h'.vals T z J' J hJ' hJ (fun x => U x * W x) (fun x => by
      rw [hW, ← hU]; exact (ha _ x.left z _ _ (hJ (x.left ≫ p)) (hJ' x.left)).symm)
    simp only [hU]
    have o : U 1 = 1 := by
      have := mul_right_cancel (b₁.symm.trans a₁)
      exact mul_eq_right.1 this
    refine ⟨o, fun x => ?_, fun x y u => ?_⟩
    · have a := congrArg Additive.ofMul (a₂ x)
      have b := congrArg Additive.ofMul (b₂ x)
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at a b ⊢
      linear_combination (norm := abel) a - b
    · have a := a₃ x y u
      have b := b₃ x y u
      rw [o] at b
      generalize @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J (toBase hp x)
        (toBase hp y) (toBase hp u)) = C at a b
      have a' := congrArg Additive.ofMul a
      have b' := congrArg Additive.ofMul b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_one] at a' b' ⊢
      linear_combination (norm := abel) a' - b'
  have one : a = 1 := by
    refine GlobalTheory.even_cubic_unit_eq_one hG S' X G Q a fun T U hU => ?_
    let E : (T ⟶ G) → Γ(T.left, ⊤)ˣ := fun x => Units.map x.left.appTop.hom.toMonoidHom a
    have hE : ∀ x, U x = (E x).val := hU
    have e : ∀ (x : T ⟶ G) z, gm (𝟙 T.left) z ⊤ (E x) = gm x.left z ⊤ a := fun x z => (gm_top _ _ _).symm
    simp only [hE, ← Units.val_mul]
    refine ⟨congrArg Units.val (show E 1 = 1 from unit_ext fun z _ => ?_),
      fun x => congrArg Units.val (unit_ext fun z _ => ?_), fun x y u => congrArg Units.val (unit_ext fun z _ => ?_)⟩
    · rw [e, map_one]; exact (key T z).1
    · rw [e, e]; exact (key T z).2.1 x
    · simp only [map_mul, e]; exact (key T z).2.2 x y u
  rw [ha Z x z j m hj hm, one, map_one, _root_.one_mul]

theorem gw_compat (hG : GlobalFnsSt) [ConnectedSpace S'] [ConnectedSpace G.left] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] (Q : TQ G X) {S₁ : Scheme.{0}} {G₁ : Over S₁} {H : Over S} [GrpObj G₁] [IsCommMonObj G₁]
    [GrpObj H] [IsCommMonObj H] {P₀ : CP G} {P₁ : CP G₁} {P : CP H} {M : CP B} {t : S' ⟶ S₁} {f₁ : S₁ ⟶ S}
    {f₀ : S' ⟶ S} {m : G.left ⟶ G₁.left} {F₁ : G₁.left ⟶ H.left} {F₀ : G.left ⟶ H.left} {p₁ : G₁.left ⟶ B.left}
    {p₀ : G.left ⟶ B.left} (ef : t ≫ f₁ = f₀) (eF : m ≫ F₁ = F₀) (ep : m ≫ p₁ = p₀)
    (hm : IsGrpPullback G G₁ t m) {hF₀ hF₁ hp₀ hp₁ u₀ u₁ v₀ v₁} (U₀ : IsCPMap P₀ P f₀ F₀ hF₀ u₀)
    (U₁ : IsCPMap P₁ P f₁ F₁ hF₁ u₁) (V₀ : IsCPMap P₀ M f₀ p₀ hp₀ v₀) (V₁ : IsCPMap P₁ M f₁ p₁ hp₁ v₁) {w₀ w₁}
    (W₀ : IsQuotIso u₀ v₀ w₀) (W₁ : IsQuotIso u₁ v₁ w₁) (Z : Scheme.{0}) (x : Z ⟶ G.left) (z : Z) (j k)
    (hj : p₀ (x z) ∈ M.L.L.U j) (hk : F₀ (x z) ∈ P.L.L.U k) :
    gw w₁ (x ≫ m) z j (fun _ => k) = gw w₀ x z j (fun _ => k) := by
  subst ef eF ep
  obtain ⟨r, R, Tr⟩ := (isCPMap_comp_cancel _ _ _ f₁ t H G₁ G P P₁ P₀ F₁ hF₁ u₁ m hm.1.w hF₀ U₁).2
    (fun T x y => Over.OverMorphism.ext (hm.2 T x y _ _ rfl rfl).symm) u₀ U₀
  obtain ⟨v', Tv, V'⟩ := V₁.exists_comp R hp₀
  obtain ⟨c, hc⟩ := exists_chart P₀.L.isLB (x z)
  obtain ⟨d, hd⟩ := exists_chart P₁.L.isLB (m (x z))
  have e₀ := W₀ Z x z j k c hj hk hc
  have e₁ := W₁ Z (x ≫ m) z j k d hj hk hd
  rw [gw_eq_of_isCPMap hG Q V' V₀ Z x z j c hj hc, Tv Z x z j d c hj hd hc, Tr Z x z k d c hk hd hc, e₁,
    _root_.mul_assoc] at e₀
  exact mul_right_cancel e₀

end Unique

section Vals
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S'} {H B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]
  [IsCommMonObj H] [GrpObj B] [IsCommMonObj B]


omit [GrpObj G] [IsCommMonObj G] [IsCommMonObj H] in
theorem cubV_toBase {L : RigLB H} (c : CubicalStr H L) (F : (Over.map f).obj G ⟶ H)
    (hF : (show G.left ⟶ H.left from F.left) ≫ H.hom = G.hom ≫ f) {T : Over S'} (z : T.left) (J)
    (x y u : T ⟶ G) :
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := Over.mk (T.hom ≫ f)) z J (toBase hF x)
      (toBase hF y) (toBase hF u)) =
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := (Over.map f).obj T) z J ((Over.map f).map x ≫ F)
      ((Over.map f).map y ≫ F) ((Over.map f).map u ≫ F)) := by
  have e : ∀ x : T ⟶ G, toBase hF x = (Over.map f).map x ≫ F := fun x => Over.OverMorphism.ext rfl
  rw [e, e, e]

theorem IsQuotIso.vals {P₀ : CP G} {P : CP H} {M : CP B} (F : (Over.map f).obj G ⟶ H) (p : (Over.map f).obj G ⟶ B)
    {hF hp u v} (hu : IsCPMap P₀ P f F.left hF u) (hv : IsCPMap P₀ M f p.left hp v) {w} (hw : IsQuotIso u v w)
    (Z : Over S') (z : Z.left) (JG : (Z.left ⟶ H.left) → P.L.L.ι) (J : (Z.left ⟶ B.left) → M.L.L.ι)
    (hJG : Good P.L.L z JG) (hJ : Good M.L.L z J) (W : (Z ⟶ G) → (Z.left.presheaf.stalk z)ˣ)
    (hW : ∀ x, W x = gw w x.left z (J (x.left ≫ p.left)) (fun _ => JG (x.left ≫ F.left))) :
    (val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig (Z.hom ≫ f) z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec H) (ε := fun _ => 1) P.L.rig (Z.hom ≫ f) z JG) ∧
      (∀ x : Z ⟶ G, val M.sym (x.left ≫ p.left) z J * W x = W x⁻¹ * val P.sym (x.left ≫ F.left) z JG) ∧
      ∀ x y u : Z ⟶ G,
        @id (Z.left.presheaf.stalk z)ˣ (cubV M.c (T := (Over.map f).obj Z) z J
            ((Over.map f).map x ≫ p) ((Over.map f).map y ≫ p) ((Over.map f).map u ≫ p)) *
            W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u *
          @id (Z.left.presheaf.stalk z)ˣ (cubV P.c (T := (Over.map f).obj Z) z JG
            ((Over.map f).map x ≫ F) ((Over.map f).map y ≫ F) ((Over.map f).map u ≫ F)) := by
  obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB z
  obtain ⟨U, hU⟩ : ∃ U : (Z ⟶ G) → (Z.left.presheaf.stalk z)ˣ,
    ∀ x, U x = gw u x.left z (JG (x.left ≫ F.left)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨a₁, a₂, a₃⟩ := hu.vals Z z J' JG hJ' hJG U hU
  obtain ⟨b₁, b₂, b₃⟩ := hv.vals Z z J' J hJ' hJ (fun x => W x * U x) (fun x => by
    rw [hW, hU]
    exact (hw _ x.left z _ _ _ (hJ (x.left ≫ p.left)) (hJG (x.left ≫ F.left)) (hJ' x.left)).symm)
  refine ⟨b₁.trans ((_root_.mul_assoc _ _ _).trans (congrArg (W 1 * ·) a₁.symm)), fun x => ?_, fun x y t => ?_⟩
  · have a := congrArg Additive.ofMul (a₂ x)
    have b := congrArg Additive.ofMul (b₂ x)
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a b ⊢
    linear_combination (norm := abel) b - a
  · have a := a₃ x y t
    have b := b₃ x y t
    rw [cubV_toBase P.c F hF] at a
    rw [cubV_toBase M.c p hp] at b
    generalize @id (Z.left.presheaf.stalk z)ˣ (cubV M.c (T := (Over.map f).obj Z) z J
            ((Over.map f).map x ≫ p) ((Over.map f).map y ≫ p) ((Over.map f).map t ≫ p)) = C at b ⊢
    generalize @id (Z.left.presheaf.stalk z)ˣ (cubV P.c (T := (Over.map f).obj Z) z JG
            ((Over.map f).map x ≫ F) ((Over.map f).map y ≫ F) ((Over.map f).map t ≫ F)) = C' at a ⊢
    have a' := congrArg Additive.ofMul a
    have b' := congrArg Additive.ofMul b
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a' b' ⊢
    linear_combination (norm := abel) b' - a'

end Vals

section Assemble
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {P : CP G} {X : Type} [AddCommGroup X]

theorem sym_of_cp {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] (M : CP B) : Sym B M.L.L := fun _ =>
  ⟨⊤, trivial, gen_chartPull (chartPullSame M.L.L _ _ _ (B.hom ⁻¹ᵁ ⊤).ι fun k => by
    fin_cases k
    exacts [rfl, (Category.comp_id _).symm]) M.sym M.sym_gen⟩


omit [IsDomain R] in
theorem isLocalRing_quot (hI : I ≠ ⊤) (e : ℕ) : IsLocalRing (R ⧸ I ^ (e + 1)) := by
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective


omit [IsDomain R] [IsLocalRing R] [IsCommMonObj G] in
theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem exists_preU (hG : GlobalFnsSt)
    (hc : ∀ (D : DegPre R) (e : ℕ) (g : GtCoord I D e G) (g' : GtCoord I D (e + 1) G),
      thickMap R I e G ≫ g'.pG.left = g.pG.left → TorusCompat (thickTrans R I e) (thickMap R I e G) g.i g'.i →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g'.t χ) (thickMap R I e G)) (g.t χ))
    (hI : I ≠ ⊤) (hs : IsSemiAbelian G) [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (a : T.Alg)
    (hK : KTriv a.B a.M.L.L) (c : X → (𝟙_ _ ⟶ a.B)) (hadd : ∀ χ χ', c (χ + χ') = c χ * c χ')
    (hw : ∀ χ e, a.RepWt (c χ) χ e) (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A)
    (hgen : IsMonHom gen.hom) (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R)))) :
    ∃ (D : DegPre R) (U : PreU I D A G), U.P = P ∧ U.gen = gen := by
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R a.B a.isAb
  obtain ⟨wA, hwA⟩ := hA
  choose psi hpsi using fun χ : X => DVR.exists_gen_of_local (V := FractionRing R) a.M.L.L a.M.L.isLB (K := PUnit)
    (fun _ => ptK (c χ)) (fun _ => -1)
  let B : PolAV (Spec (CommRingCat.of R)) :=
    { A := a.B, isAb := a.isAb, g := g, smoothDim := hg, L := a.M.L.L, isLB := a.M.L.isLB,
      rigid := ⟨a.M.L.rig, a.M.L.rigGen⟩, sym := sym_of_cp a.M, ample := a.ample, ktriv := hK }
  let D : DegPre R :=
    { P := B, rig := a.M.L.rig, rig_gen := a.M.L.rigGen, cub := a.M.c, sym := a.M.sym, sym_gen := a.M.sym_gen,
      sym_rig := a.M.sym_rig, X := X, c := c, c_add := hadd, psi := psi, psi_gen := hpsi }
  choose gt hi hp using fun e => GlobalTheory.exists_gtCoord_of_torusQuotient hG R I D e G (T.l e).Q (a.b e)
    (a.b_pb e).1 (fun χ => hw χ e)
  have hq : ∀ e, thickMap R I e G ≫ (gt (e + 1)).pG.left = (gt e).pG.left := fun e => by
    rw [hp, hp, ← Category.assoc, ← T.β_q, Category.assoc, a.b_β]
  choose u hu using fun e => (T.l e).lev
  have hv : ∀ e, ∃ v, IsCPMap (T.l e).Pe a.M (thick R I e) (gt e).pG.left (Over.w (gt e).pG) v := fun e => by
    obtain ⟨h, v, hv⟩ := a.b_pb e
    have : ∀ f p (_ : f = 𝟙 _ ≫ thick R I e) (_ : p = (T.l e).Q.q.left ≫ a.b e) hw,
        ∃ v, IsCPMap (T.l e).Pe a.M f p hw v := by
      rintro _ _ rfl rfl hw
      obtain ⟨v', -, h'⟩ := hv.exists_comp (T.l e).D.map hw
      exact ⟨v', h'⟩
    exact this _ _ (Category.id_comp _).symm (hp e) _
  choose v hv using hv
  choose w hw using fun e => exists_isQuotIso (T.l e).Pe.L.isLB P.L.isLB a.M.L.isLB ((isGen_iff _).1 (hu e).gen)
    ((isGen_iff _).1 (hv e).gen)
  refine ⟨D,
    { semi := hs, gen := gen, gen_hom := hgen, P := P, wA := wA, wA_gen := hwA, gt := gt, gt_q := hq
      gt_t := fun e => hc D e _ _ (hq e) (by rw [hi, hi]; exact T.tor e)
      w := w
      w_gen := fun e => (hw e).isGen (T.l e).Pe.L.isLB ((isGen_iff _).1 (hu e).gen) ((isGen_iff _).1 (hv e).gen)
      w_vals := fun e Z z JG J hJG hJ W hW => ?_
      w_compat := fun e Z x z j k hj hk => ?_ }, rfl, rfl⟩
  · exact IsQuotIso.vals (fstG I e G) (gt e).pG (hu e) (hv e) (hw e) Z z JG J hJG hJ W hW
  · have := isLocalRing_quot hI e
    have := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing (R ⧸ I ^ (e + 1))
    have hs' := Geo.Tor.IsSemiAbelian.pullback (thick R I e) G hs
    have := hs'.smooth
    have := hs'.geomConnected
    have : ConnectedSpace (thickObj R I e G).left := (GlobalTheory.GroupConn.connectedSpace_group _ (thickObj R I e G)).1
    exact gw_compat hG (T.l e).Q (thickTrans_comp R I e) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) (hq e)
      (isGrpPullback_thickMap e) (hu e) (hu (e + 1)) (hv e) (hv (e + 1)) (hw e) (hw (e + 1)) Z x z j k hj hk

end Assemble

section Principal
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}


omit [IsDomain R] in
theorem isAdicComplete_quot [IsNoetherianRing R] (h : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (J : Ideal R)
    [IsLocalRing (R ⧸ J)] : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ J)) (R ⧸ J) := by
  have := GlobalTheory.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal R) (R ⧸ J)
  rwa [show algebraMap R (R ⧸ J) = Ideal.Quotient.mk J from rfl,
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at this


omit [IsDomain R] in
theorem kTriv_closedFibre {J : Ideal R} (hJ : J ≠ ⊤) {B : Over (Sp R)} [GrpObj B] {B₀ : Over (Sp (R ⧸ J))} [GrpObj B₀]
    {b : B₀.left ⟶ B.left} (hb : IsGrpPullback B₀ B (spMap (Ideal.Quotient.mk J)) b) {M : LB B.left} {M₀ : LB B₀.left}
    (hM : M.IsLB) (hM₀ : M₀.IsLB) {v : LB.Iso M₀ (M.pull b)} (hv : v.IsGen) (hK : KTriv B₀ M₀) :
    KTriv ((Over.pullback (spMap (IsLocalRing.residue R))).obj B)
      (M.pull (pullback.fst B.hom (spMap (IsLocalRing.residue R)))) := by
  let x : Sp (IsLocalRing.ResidueField R) ⟶ Sp (R ⧸ J) :=
    spMap (Ideal.Quotient.lift J (IsLocalRing.residue R) fun r hr =>
      (IsLocalRing.residue_eq_zero_iff r).2 (IsLocalRing.le_maximalIdeal hJ hr))
  have hx : x ≫ spMap (Ideal.Quotient.mk J) = spMap (IsLocalRing.residue R) := by
    rw [← Spec.map_comp]; rfl
  have sq : pullback.fst B.hom (spMap (IsLocalRing.residue R)) ≫ B.hom =
      (pullback.snd B.hom (spMap (IsLocalRing.residue R)) ≫ x) ≫ spMap (Ideal.Quotient.mk J) := by
    rw [Category.assoc, hx, pullback.condition]
  have hφ := hb.1.lift_fst _ _ sq
  have h := hb.cancel ((isGrpPullback_pullback B (spMap (IsLocalRing.residue R))).congr hx.symm hφ.symm)
    (hb.1.lift_snd _ _ sq)
  have hL' : (M.pull (pullback.fst B.hom (spMap (IsLocalRing.residue R)))).IsLB := LB.isLB_pull hM _
  obtain ⟨r, hr⟩ : LBIso (M.pull (pullback.fst B.hom (spMap (IsLocalRing.residue R))))
      (M.pull (hb.1.lift _ _ sq ≫ b)) := by
    rw [hφ]; exact GlobalTheory.lbIso_refl hL'
  obtain ⟨w, Tw⟩ := Geo.Tor.exists_cancel hM v r ((isGen_iff _).1 hv) ((isGen_iff _).1 hr) hM₀ hL'
  exact kTriv_pull h hM₀ hL' (Tw.pgen_cancel hM ((isGen_iff _).1 hv) ((isGen_iff _).1 hr)) hK

end Principal

theorem exists_preU_of_fibres (hF : Laws → Laws2 → Laws3 → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))), RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧ KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x))) :
    Laws → Laws2 → Laws3 → Ega → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → IsPrincipalIdealRing (R ⧸ I) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → SplitOver G I → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : PreU I D A G), U.P = P ∧ U.gen = gen := by
  intro hL hL2 hL3 hE hU R _ _ _ I hR hP G _ _ P hs hW hS A gen hgen hA
  have hI : I ≠ ⊤ := hR.2.2.2.1.ne_top
  have := hR.1.1
  have hpr : IsProper (pullback.snd G.hom (jK R)) := by
    have := A.isAb.proper
    have e : pullback.snd G.hom (jK R) = gen.hom.left ≫ A.A.hom := (Over.w gen.hom).symm
    have : IsIso gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map gen.hom))
    rw [e]; infer_instance
  obtain ⟨X, _, _, _, ⟨T⟩⟩ := GlobalTheory.T.nonempty_formalUniformisationTower hL hL2 R I hR G P hs hW hpr hS
  have hf := hF hL hL2 hL3 hU R I hR G P hs hW A gen hgen hA X T
  have := isLocalRing_quot hI 0
  have e : I ^ (0 + 1) = I := pow_one I
  have : (I ^ (0 + 1)).IsPrime := e.symm ▸ hR.2.2.2.1
  have : IsPrincipalIdealRing (R ⧸ I ^ (0 + 1)) := e.symm ▸ hP
  have amp : RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.cubical_bundle_relAmple_of_ample_fibres hL hL2 (R ⧸ I ^ (0 + 1)) (isAdicComplete_quot hR.2.1 _) _ (T.l 0).Q.isAb (T.l 0).D.M
      fun k _ x => (hf k x).1
  obtain ⟨a⟩ := GlobalTheory.T.nonempty_algebraisation_formal_tower_ample hL hL2 hE R I hR G P X T amp
  have k₀ : KTriv (T.l 0).Q.B (T.l 0).D.M.L.L :=
    GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 (R ⧸ I ^ (0 + 1)) _ (T.l 0).Q.isAb _ (T.l 0).D.M.L.isLB amp (hf _ _).2
  obtain ⟨hb, v, hv⟩ := a.b_pb 0
  have hK : KTriv a.B a.M.L.L := GlobalTheory.T.kTriv_of_closed_fibre_localRing hL hL2 R _ a.isAb _ a.M.L.isLB a.ample
    (kTriv_closedFibre (e.symm ▸ hI) hb a.M.L.isLB (T.l 0).D.M.L.isLB hv.gen k₀)
  obtain ⟨c, hadd, hw⟩ := GlobalTheory.T.exists_additive_weightPoints_of_torusTower hL hL2 hE R I hR G P X T a hK
  exact exists_preU hL.globalFns (fun D e => GlobalTheory.T.torusCoordinates_compat_of_torus_compat hL.globalFns R I D e G) hI hs T a hK c hadd hw A gen hgen hA

end GlobalTheory.PreUnifLocal
end
