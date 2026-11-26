module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem cube_of_isLB :
    ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB →
      ∃ t : LB.Gen (Theta P.A M), t.IsGen :=
  GlobalTheory.AbLaw.CubeAssembly.cube_gen

end GlobalTheory.Moduli
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_cube_polAbelianScheme : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen := by
  first | exact @GlobalTheory.Moduli.cube_of_isLB | exact GlobalTheory.Moduli.cube_of_isLB | (intros; apply GlobalTheory.Moduli.cube_of_isLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaLocal

open Out ThetaPtExist

theorem exists_isThetaPtOver {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} {I : Type} (x : I → (T ⟶ P.A)) (th : LB.Sec (LPow P.A P.L 1 T))
    (hth : IsGenSec P.A P.L 1 th)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPtOver P k x v := by
  have hL := P.isLB
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T ⟶ P.A).left) (ε' := fun _ => (k : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T).left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) ((k : ℤ) ^ 2) 1 α hα th
  choose U hU using hU
  choose s₂ hs₂ using fun i => exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt) (lift_snd _ _)
    ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  choose w hw using fun i => exists_isValueAt hL (s₂ i) 1 τ hτ
  exact ⟨w, th, s₁, α, τ, U, s₂, w, 1, hth, hα, hτ, hs₁, hU, hs₂, hw, fun i => (_root_.one_mul _).symm⟩

theorem exists_isThetaPt {S : Scheme.{0}} (P : PolAV S) (k : ℕ) (hk : Odd k)
    (α₀ : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1]))
    (hα₀ : α₀.IsGen) {T : Over S} (hu : IsUnit (k : Γ(T.left, ⊤))) {I : Type} (x : I → (T ⟶ P.A))
    (t : SecM P.A P.L 1 T) (ht : ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s)
    (hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ) :
    ∃ v, IsThetaPt P k x v := by
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  obtain ⟨th, hth⟩ := exists_isGenSec_of_retract P.isLB (overResι (T := T) ⊤) h hi t ht
  obtain ⟨w, hw⟩ := exists_isThetaPtOver P k α₀ hα₀ (fun i => overResι (T := T) ⊤ ≫ x i) th hth fun i => by
    obtain ⟨θ, hθ⟩ := hU i
    exact GlobalLift.exists_symLift_pull P.isLB _ hθ
  refine ⟨fun i => h.left.appTop.hom (w i), hk, hu, fun _ => ⟨⊤, trivial, ?_⟩⟩
  convert hw using 2 with i
  have q := congrArg (fun q => q.left.appTop.hom (w i)) hi
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
    Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
  exact q

theorem exists_generator {R M K : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton K] (b : K → M)
    (hb : Submodule.span R (Set.range b) = ⊤) : ∃ t : M, ∀ s, ∃ r : R, r • t = s := by
  rcases isEmpty_or_nonempty K with h | ⟨⟨i⟩⟩
  · refine ⟨0, fun s => ⟨0, ?_⟩⟩
    have : s ∈ Submodule.span R (Set.range b) := hb ▸ Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    rw [this, zero_smul]
  · have e : Set.range b = {b i} := by
      ext m
      exact ⟨fun ⟨j, hj⟩ => by rw [← hj, Subsingleton.elim j i]; rfl, fun hm => ⟨i, hm.symm⟩⟩
    exact ⟨b i, fun s => Submodule.mem_span_singleton.1 (by rw [← e, hb]; exact Submodule.mem_top)⟩

theorem exists_affine_isThetaPt (hG : GlobalFnsSt) (hB : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ)
    (hk : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {I : Type} [Finite I] (y : I → (baseOver S ⟶ P.A))
    (hy : ∀ i, y i ^ (k ^ 2) = 1) (p : S) :
    ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S), IsOpenImmersion x ∧ p ∈ Set.range x ∧
      ∃ v, IsThetaPt P k (T := Over.mk x)
        (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ y a) v := by
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 S P k
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V₀, hV₀, b, hb⟩ := hB S P 1 le_rfl p
  choose V hV θ hθ using fun i => (sym S P (k ^ 2) hk.pow (baseOver S) (y i) (hy i)).1 p
  let O : S.Opens := V₀ ⊓ ⟨⋂ i, (V i).carrier, isOpen_iInter_of_finite fun i => (V i).2⟩
  have hO : p ∈ O := ⟨hV₀, Set.mem_iInter.2 hV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWO⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hO O.2
  have hW' : IsAffineOpen W := hW
  let x₀ : Sp Γ(S, W) ⟶ S := hW'.fromSpec
  have hx₀ : Set.range x₀ = W := hW'.range_fromSpec
  have hl : ∀ U : S.Opens, O ≤ U → ∃ t : Sp Γ(S, W) ⟶ U.toScheme, t ≫ U.ι = x₀ := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι x₀ (by
      rw [hx₀, Scheme.Opens.range_ι]; exact hWO.trans hU), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨t, ht⟩ := hl V₀ inf_le_left
  have ex : t ≫ (overRes (T := baseOver S) V₀).hom = x₀ := (congrArg (t ≫ ·) (Category.comp_id _)).trans ht
  refine ⟨Γ(S, W), inferInstance, t ≫ (overRes (T := baseOver S) V₀).hom, ?_, ?_, ?_⟩
  · rw [ex]; exact inferInstanceAs (IsOpenImmersion hW'.fromSpec)
  · rw [ex, hx₀]; exact hpW
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th, hth⟩ := exists_generator _ hsp
  refine exists_isThetaPt P k hk α₀ hα₀ (T := baseAt t) ?_ _ th hth fun i => ?_
  · simpa using hu.map (baseAt t).hom.appTop.hom
  · obtain ⟨u, hu'⟩ := hl (V i) (inf_le_right.trans fun q hq => Set.mem_iInter.1 hq i)
    let r : baseAt t ⟶ overRes (T := baseOver S) (V i) := Over.homMk u
      (((congrArg (u ≫ ·) (Category.comp_id _)).trans hu').trans ex.symm)
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB r (hθ i)
    have e : r ≫ overResι (V i) = (Over.homMk (baseAt t).hom (by simp) : baseAt t ⟶ baseOver S) :=
      Over.OverMorphism.ext (hu'.trans ex.symm)
    rw [← Category.assoc, e] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩

theorem linComb_pow_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r n : ℕ}
    {y : Fin r → (T ⟶ A)} (hy : ∀ i, y i ^ n = 1) (a : Fin r → ℕ) : linComb y a ^ n = 1 := by
  rw [linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]

theorem exists_hasTh : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s), Odd N' → ∀ p : S, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.HasTh x v := by
  intro h₁ h₂ o _ g N' J b S s t hN p
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN.pos.ne'⟩
  have hu : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).map s.appTop.hom
    rw [map_natCast, map_natCast, Nat.cast_pow] at this
    exact (isUnit_pow_iff two_ne_zero).1 this
  haveI := t.ab.comm
  obtain ⟨R, _, x, hx, hp, v, hv⟩ := exists_affine_isThetaPt h₁.globalFns h₂.secBaseChangeAny t.pol N' hN hu t.lab
    (fun a => linComb_pow_eq_one t.torsion _) p
  refine ⟨R, inferInstance, x, fun a => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (v a), hx, hp, ?_⟩
  unfold TObj.HasTh
  convert hv using 2 with a
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (v a)

end GlobalTheory.ThetaLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstants_locally_on_base : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s), Odd N' → ∀ p : S, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ t.HasTh x v := by
  first | exact @GlobalTheory.ThetaLocal.exists_hasTh | exact GlobalTheory.ThetaLocal.exists_hasTh | (intros; apply GlobalTheory.ThetaLocal.exists_hasTh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_clopen_weilIs_iff : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), 0 < n → IsUnit (n : Γ(T.left, ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 → ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T), Out.WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U :=
  fun hL => PairingLocus.exists_clopen_of_lift hL.globalFns
    (kerPow_of_square (AbSquare.square_of_cube T.cube_theorem_and_sections_finite_growth_abelianVariety.1).1).2.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaDvr

theorem app_eq_zero_of_not_mem {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [Smooth G.hom]
    {U : G.left.Opens} (a : Γ(G.left, U))
    (h : ∀ x ∈ G.left.basicOpen a, G.hom x ≠ IsLocalRing.closedPoint V) :
    ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom a = 0 := by

  have hk : _root_.IsReduced (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := by
    rw [zero_add, pow_one]
    infer_instance
  have : IsReduced (pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0))

  have hpt : ∀ y : ↥(pullback G.hom (thick V (IsLocalRing.maximalIdeal V) 0)),
      G.hom (pullback.fst G.hom (thick V (IsLocalRing.maximalIdeal V) 0) y) = IsLocalRing.closedPoint V := by
    intro y
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    apply PrimeSpectrum.ext
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · exact (Ideal.ne_top_iff_one _).mpr (PrimeSpectrum.isPrime _).one_notMem
    · intro r hr
      have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [zero_add, pow_one]; exact hr)
      change Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1)) r ∈
        ((pullback.snd G.hom (thick V (IsLocalRing.maximalIdeal V) 0)) y).asIdeal
      rw [h0]
      exact Ideal.zero_mem _

  have hbot : (fstG (IsLocalRing.maximalIdeal V) 0 G).left ⁻¹ᵁ G.left.basicOpen a = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => (h _ hy (hpt y)).elim
  rw [Scheme.preimage_basicOpen] at hbot
  exact (@basicOpen_eq_bot_iff _ this _ _).mp hbot

private lemma secIsMul_trans' {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB Y} {a b : R} {σ τ τ' : LB.Sec L} (h : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ)
    (h' : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p b τ τ') : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p (a * b) σ τ' := by
  intro k
  rw [h k, h' k, ← _root_.mul_assoc]
  congr 1
  simp only [resTop, scal, map_mul]

private lemma gs_id_eq_germ_moduli {X : Scheme.{0}} (U : X.Opens) (a : Γ(X, U)) (z : X) (hz : z ∈ U) :
    gs (𝟙 X) z U a = (X.presheaf.germ U z hz).hom a := by
  unfold gs
  rw [dite_eq_left (show (𝟙 X) z ∈ U from hz)]
  rfl

theorem exists_sec_unit_closed_fibre (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left)
    (hN : N.IsLB) (s : LB.Sec (N.pull (pullback.fst G.hom (jK V)))) (j) (hj : s.f j ≠ 0) :
    ∃ (θ : LB.Sec N) (k : N.ι), ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hflat : (algebraMap V (FractionRing V)).Flat := by
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (FractionRing V) (nonZeroDivisors V))
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  have hpb : IsPullback (pullback.fst G.hom (jK V)) (pullback.snd G.hom (jK V)) G.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) := IsPullback.of_hasPullback _ _

  obtain ⟨n, c, u, hu⟩ := GlobalTheory.FlatSec.exists_comb_of_flat V (FractionRing V) _ hflat G.left G.hom _
    (pullback.fst G.hom (jK V)) _ hpb N hN s
  have hne : ∃ i k, (u i).f k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hj
    apply TopCat.Presheaf.section_ext (pullback G.hom (jK V)).sheaf
    intro z hz
    have hj' : j = fun _ => j PUnit.unit := funext fun x => by cases x; rfl
    have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := by
      rw [hj'] at hz
      simpa [LB.pull, LB.LinComb, LB.wchart] using hz
    have h1 := hu z (j PUnit.unit) hz'
    rw [← hj'] at h1
    rw [gs_id_eq_germ_moduli _ _ z hz] at h1
    refine Eq.trans ?_ (map_zero _).symm
    change ((pullback G.hom (jK V)).presheaf.germ _ z hz).hom (s.f j) = 0
    rw [h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hcon i (j PUnit.unit)]
    simp [gs]
  obtain ⟨i, k₀, hk₀⟩ := hne
  set θ₀ := u i

  have hjac : IsLocalRing.maximalIdeal V ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hex : ∃ m, ∃ k, ((fstG (IsLocalRing.maximalIdeal V) m G).left.app _).hom (θ₀.f k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk₀ ((GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings V _ hjac G).1 N hN θ₀ hcon k₀)
  classical

  have hunit : ∀ (θ : LB.Sec N) (k : N.ι), ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (θ.f k) ≠ 0 →
      ∃ x ∈ G.left.basicOpen (θ.f k), G.hom x = IsLocalRing.closedPoint V := by
    intro θ k hθ
    by_contra hcon
    push Not at hcon
    exact hθ (app_eq_zero_of_not_mem G (θ.f k) hcon)

  obtain ⟨k₁, hk₁⟩ := Nat.find_spec hex
  rcases hm : Nat.find hex with _ | e
  · rw [hm] at hk₁
    obtain ⟨x, hx, hxc⟩ := hunit θ₀ k₁ hk₁
    exact ⟨θ₀, k₁, x, hx, hxc⟩
  · have hlt : ¬ ∃ k, ((fstG (IsLocalRing.maximalIdeal V) e G).left.app _).hom (θ₀.f k) ≠ 0 :=
      Nat.find_min hex (by omega)
    push Not at hlt
    obtain ⟨τ, hτ⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ e).1 hlt
    have hτ0 : ∃ k, ((fstG (IsLocalRing.maximalIdeal V) 0 G).left.app _).hom (τ.f k) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨τ', hτ'⟩ := (GlobalTheory.ThickDiv.main V ϖ hϖ G N τ 0).1 hcon
      have h2 := secIsMul_trans' G.hom hτ hτ'
      rw [← pow_add] at h2
      have h3 := (GlobalTheory.ThickDiv.main V ϖ hϖ G N θ₀ (e + 1)).2 ⟨τ', h2⟩
      rw [hm] at hk₁
      exact hk₁ (h3 k₁)
    obtain ⟨k, hk⟩ := hτ0
    obtain ⟨x, hx, hxc⟩ := hunit τ k hk
    exact ⟨τ, k, x, hx, hxc⟩

theorem thetaNZ_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (t : SAB H (Sp V)), GlobalTheory.LN.PolAt t (jK V) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro hL hL2 E _ _ _ H V _ _ _ t ht
  obtain ⟨A, oA, gen, -, hiso, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt hL hL2 E H V t ht
  have hsa := t.4
  have : Smooth t.G.hom := hsa.2
  have : IsSeparated t.G.hom := hsa.3
  have : QuasiCompact t.G.hom := hsa.4
  have : GeometricallyConnected t.G.hom := hsa.5
  have hLt : t.PP.L.IsLB := t.PP.3

  have hP := GlobalTheory.PushInv.pushInvertible_any hL2.1 hL.1 _ A
  obtain ⟨W, hxW, θ, hθ, -, hnz⟩ := hP (IsLocalRing.closedPoint (FractionRing V))
  obtain ⟨g, i, -, hg⟩ := hnz _ hxW
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  have hO : ⊤ ≤ gen.hom.left ⁻¹ᵁ (A.A.hom ⁻¹ᵁ W) := by
    intro y _
    change A.A.hom (gen.hom.left y) ∈ W
    rwa [Subsingleton.elim (A.A.hom (gen.hom.left y)) (IsLocalRing.closedPoint (FractionRing V))]
  obtain ⟨θ', hθ'⟩ := GlobalTheory.ThetaLocal.exists_sec_pull A.isLB (LB.isLB_pull hLt _) gen.hom.left w hw hO θ hθ
  have hgy : gen.hom.left (gen.inv.left g) = g := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, gen.inv_hom_id, Over.id_left]
    rfl
  obtain ⟨k, hk⟩ := hθ' (gen.inv.left g) i (by rwa [hgy])
  have hk0 : θ'.f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk

  obtain ⟨σ, l, x, hx, hxc⟩ := exists_sec_unit_closed_fibre V t.G t.PP.L hLt θ' k hk0

  refine ⟨σ, fun y => ?_⟩
  have hy : y ⤳ t.G.hom x := hxc ▸ IsLocalRing.specializes_closedPoint y
  obtain ⟨x', hx', hx'y⟩ := Flat.generalizingMap t.G.hom hy
  exact ⟨x', l, hx'y, hx'.mem_open (t.G.left.basicOpen (σ.f l)).isOpen hx⟩

end GlobalTheory.ThetaDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HermAdjoint

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact (u.ker 0).2 u.Λ.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem exists_period_of_pow_eq_one {n : ℕ} (hn : 0 < n) {x : 𝟙_ (Over (Sp ℂ)) ⟶ A} (hx : x ^ n = 1) :
    ∃ a : u.Λ, u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) = x := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 ((ex_nsmul u n z).trans hx)⟩, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]

theorem ex_period_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
  exact (u.ker _).2 a.2

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) :=
  Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective

theorem int_eq_of_exp {p q : ℤ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ) / n)) : p = q := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((q - p).natAbs + 1) (Nat.succ_pos _))
  have hn : (((q - p).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h₁ : ((q - p : ℤ) : ℂ) = ((m * (((q - p).natAbs + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((q - p).natAbs + 1 : ℕ) : ℂ) = N at hm hn
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    field_simp at hm ⊢
    linear_combination hm
  have h₂ : (((q - p).natAbs + 1 : ℕ) : ℤ) ∣ q - p := ⟨m, by rw [mul_comm]; exact Int.cast_injective h₁⟩
  have h₃ := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h₂ (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem adjoint_of_im (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ a ∈ s, ∀ b ∈ s, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im)
    (z w : Fin g → ℂ) : hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have sl : ∀ (t : ℂ) a b, hermForm Hm (t • a) b = t * hermForm Hm a b := fun t a b => by
    simp [hermForm, smul_dotProduct]
  have sr : ∀ (t : ℝ) a b, hermForm Hm a ((t : ℂ) • b) = t * hermForm Hm a b := fun t a b => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  have al : ∀ a a' b, hermForm Hm (a + a') b = hermForm Hm a b + hermForm Hm a' b := fun a a' b => by
    simp [hermForm, add_dotProduct]
  have ar : ∀ a b b', hermForm Hm a (b + b') = hermForm Hm a b + hermForm Hm a b' := fun a b b' => by
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have all : ∀ a b, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im := fun a b => by
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    have hb : b ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha, hb using Submodule.span_induction₂ with
    | mem_mem a b ha hb => exact h a ha b hb
    | zero_left b _ => simp [hermForm]
    | zero_right a _ => simp [hermForm]
    | add_left a a' b _ _ _ h₁ h₂ => rw [map_add (f := _), al, al, Complex.add_im, Complex.add_im, h₁, h₂]
    | add_right a b b' _ _ _ h₁ h₂ => rw [map_add (f := _), ar, ar, Complex.add_im, Complex.add_im, h₁, h₂]
    | smul_left t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sl, sl, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
    | smul_right t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sr, sr, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
  refine Complex.ext ?_ (all z w)
  have := all (Complex.I • z) w
  rwa [map_smul, sl, sl, Complex.I_mul_im, Complex.I_mul_im] at this

theorem lbIso_cubeLB_iff_hermForm : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f f' : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) ↔ ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) := by
  intro hl hl₂ hc hU P u Hm χ f f' F F' hAH hf hf' e e'
  have := P.isAb.comm
  obtain ⟨Ef, hE, -, -, -, -, -, -, hW⟩ := GlobalTheory.AnyAppellHumbert.isAH_properties hl hl₂ hc hU P u Hm χ hAH
  have hF : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF' : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  let c : ℤ → ℕ → ℂˣ := fun p n => Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (p : ℂ) / n))
  have w₁ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ≫ f)
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn (c (Ef ⟨_, hF a⟩ b) n)) := fun n a b hn => by
    rw [← e, map_smul]
    exact hW n ⟨_, hF a⟩ b _ hn rfl
  have w₂ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)))
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ)) ≫ f') (unitOn (c (Ef a ⟨_, hF' b⟩) n)) := fun n a b hn => by
    rw [← e', map_smul]
    exact hW n a ⟨_, hF' b⟩ _ hn rfl
  have uq : ∀ (n : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (d d' : Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ), x ^ n = 1 → y ^ n = 1 →
      Out.WeilIs P.A P.L n (x ≫ f) y d → Out.WeilIs P.A P.L n (x ≫ f) y d' → d = d' := fun n x y d d' hx hy h h' =>
    ((hl.weil _ P n _).1 _ _ (by rw [← MonObj.pow_comp, hx, MonObj.one_comp]) hy).unique h h'
  constructor
  · intro hiso
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB _ _ hiso
    have hR : Out.RosatiAdj P.A P.L f f' := fun _ =>
      ⟨⊤, trivial, LB.pullGen _ _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩
    refine adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
    have : Ef ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩ = Ef ⟨a, ha⟩ ⟨_, hF' ⟨b, hb⟩⟩ := int_eq_of_exp fun n hn => by
      have hx := ex_period_pow u hn ⟨a, ha⟩
      have hy := ex_period_pow u hn ⟨b, hb⟩
      exact congrArg Units.val (unitOn_injective (uq n _ _ _ _ hx hy (w₁ n ⟨a, ha⟩ ⟨b, hb⟩ hn)
        ((GlobalTheory.weilIs_rosati_iff hl.globalFns hl.cube P f f' hR n _ _ hx hy _).2 (w₂ n ⟨a, ha⟩ ⟨b, hb⟩ hn))))
    exact (hE ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩).symm.trans ((congrArg Int.cast this).trans (hE _ _))
  · intro H
    refine GlobalTheory.lbIso_cubeLB_of_pairing_adjoint hl ℂ P f f' hf hf' fun n x y d hn hx hy hd => ?_
    obtain ⟨a, rfl⟩ := exists_period_of_pow_eq_one u hn hx
    obtain ⟨b, rfl⟩ := exists_period_of_pow_eq_one u hn hy
    have hab : Ef ⟨_, hF a⟩ b = Ef a ⟨_, hF' b⟩ := by
      apply Int.cast_injective (α := ℝ)
      rw [hE, hE]
      exact congrArg Complex.im (H a b)
    rw [uq n _ _ _ _ hx hy hd (w₁ n a b hn), hab]
    exact w₂ n a b hn

end GlobalTheory.HermAdjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f f' : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) ↔ ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) := by
  first | exact @GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm | exact GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm | (intros; apply GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegDesc

theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem spMap_subtype_inclusion {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem siegPre_descends : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  intro h M o _ ζ K _ K₀ s₀ s c hs hc
  classical
  obtain ⟨sA, hA⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K K₀ c.A.left c.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple hc.1)
  let K' : Subfield K := K₀ ⊔ Subfield.closure (sA : Set K)
  obtain ⟨X', p', φ', hproj, hpb⟩ := hA K' le_sup_left
    (Subfield.subset_closure.trans (SetLike.coe_subset_coe.2 le_sup_right))
  have : IsProper p' := by
    obtain ⟨N, i, _, rfl⟩ := hproj
    have := isProper_str K' N
    infer_instance
  have : LocallyOfFinitePresentation p' :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let A' : Over (Sp K') := Over.mk p'
  have : IsProper A'.hom := ‹IsProper p'›
  have : LocallyOfFinitePresentation A'.hom := ‹LocallyOfFinitePresentation p'›
  have hpb' : IsPullback (φ' : c.A.left ⟶ A'.left) c.A.hom A'.hom (spMap K'.subtype) := hpb
  obtain ⟨sG, hG⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K' A' c.A φ' hpb'
  obtain ⟨φ₂', hsq'⟩ := exists_isSquare hpb'.w
  have : IsProper (A' ⊗ A').hom := by
    change IsProper (pullback.fst A'.hom A'.hom ≫ A'.hom)
    infer_instance
  obtain ⟨sL, hL⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K K' (A' ⊗ A').left (c.A ⊗ c.A).left (A' ⊗ A').hom (c.A ⊗ c.A).hom φ₂'
    c.P c.isLB (isPullback_of_isSquare hpb' hsq')
  obtain ⟨lv, hlv⟩ : ∃ lv : Fin h ⊕ Fin h → (Sp K ⟶ c.A.left), ∀ u, lv u = (c.lev (Pi.single u 1)).left :=
    ⟨_, fun _ => rfl⟩
  have hlev : ∀ u, lv u ≫ c.A.hom = 𝟙 (Sp K) := fun u =>
    (congrArg (· ≫ c.A.hom) (hlv u)).trans (Over.w (c.lev (Pi.single u 1)))
  obtain ⟨sP, hP⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K' (Sp K') (Sp K) (𝟙 _) (𝟙 _) (spMap K'.subtype) X' p' (Fin h ⊕ Fin h)
    (fun u => lv u ≫ φ') IsPullback.of_id_snd
    (fun u => by
      have e := hlev u
      rw [Category.comp_id, Category.assoc, hpb.w, reassoc_of% e])
  refine ⟨sA ∪ sG ∪ sL ∪ sP, fun K₁ hK hF => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hsA, hsG⟩, hsL⟩, hsP⟩ := hF
  have h' : K' ≤ K₁ := sup_le hK (Subfield.closure_le.2 hsA)
  let j := spMap (Subfield.inclusion h')
  have hj : spMap K₁.subtype ≫ j = spMap K'.subtype := spMap_subtype_inclusion h'
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p' j)
  let φ₁ : A₁.left ⟶ A'.left := pullback.fst p' j
  have hpb₁ : IsPullback φ₁ A₁.hom A'.hom j := IsPullback.of_hasPullback p' j
  let ψ : c.A.left ⟶ A₁.left := hpb₁.lift φ' (c.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, hj]; exact hpb.w)
  have hψ₁ : ψ ≫ φ₁ = φ' := hpb₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap K₁.subtype := hpb₁.lift_snd _ _ _
  obtain ⟨grp, hgrp⟩ := hG K₁ h' hsG A₁ φ₁ ψ hpb₁ hψ₁ hψ₂
  obtain ⟨φ₂, hsq₁⟩ := exists_isSquare hpb₁.w
  obtain ⟨ψ₂, hsqψ⟩ := exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hL K₁ h' hsL (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂ ψ₂
    (isPullback_of_isSquare hpb₁ hsq₁) (isSquare_comp hψ₁ hsqψ hsq₁ hsq') (isSquare_w hψ₂ hsqψ)
  obtain ⟨f₁, hf₁⟩ := hP K₁ h' hsP (Sp K₁) (𝟙 _) j (spMap K₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Fin h ⊕ Fin h → (Sp K₁ ⟶ A₁.left) := fun u => hpb₁.lift (f₁ u) (𝟙 _)
    (by rw [Category.id_comp]; exact (hf₁ u).2.trans (Category.comp_id _))
  have hl₁ : ∀ u, l u ≫ φ₁ = f₁ u := fun u => hpb₁.lift_fst _ _ _
  have hl₂ : ∀ u, l u ≫ A₁.hom = 𝟙 _ := fun u => hpb₁.lift_snd _ _ _
  let lev₁ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun u => Over.homMk (l u) (hl₂ u)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_siegelObject_of_descended_data h M o ζ K₁ K K₁.subtype (spMap (Subfield.inclusion hK) ≫ s₀) s c A₁ ψ ψ₂ P₁
    lev₁ (by rw [hs, ← Category.assoc, spMap_subtype_inclusion]) hgrp hsqψ hP₁ hiso (fun u => by
      have e := hlev u
      have key : lv u ≫ ψ = spMap K₁.subtype ≫ l u := by
        apply hpb₁.hom_ext
        · rw [Category.assoc, Category.assoc, hψ₁, hl₁]
          exact (hf₁ u).1.symm
        · rw [Category.assoc, Category.assoc, hψ₂, hl₂, reassoc_of% e, Category.comp_id]
      exact (congrArg (· ≫ ψ) (hlv u)).symm.trans key)
  exact ⟨c₁, GlobalTheory.SiegelDescent.principal_of_fieldExtension h M o ζ K₁ K K₁.subtype _ s c₁ c hc₁ hc, hc₁⟩

end GlobalTheory.SiegDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_principal_object_descends_large_subfield : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  first | exact @GlobalTheory.SiegDesc.siegPre_descends | exact GlobalTheory.SiegDesc.siegPre_descends | (intros; apply GlobalTheory.SiegDesc.siegPre_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EmbLocal

open ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

theorem exists_isGenSec_near (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∀ (R : Type) [CommRing R] (q : Sp R ⟶ S), Set.range q ⊆ V →
      ∃ th, IsGenSec P.A P.L 1 (T := Over.mk q) th := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  refine ⟨V, hV, fun R _ q hqV => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
    ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose b' hb' using fun i =>
    PushInv.exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
  obtain ⟨-, hsp⟩ := hb R t b' hb'
  refine ⟨b' hq.default, fun s => ?_⟩
  rw [Set.range_unique] at hsp
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem exists_mulPull (hG : GlobalFnsSt) (P : PolAV S) (k : ℕ) (T : Over S) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![(k : ℤ) ^ 2, -1]),
      α.IsGen := by
  obtain ⟨α₀, hα₀⟩ := (MulPull.mulPull_of_cube_of_symm AbLaw.CubeAssembly.cube_gen (exists_gen_negLB hG)).1 S P k
  have e₁ : (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen P.isLB (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left])
    (ε' := ![(k : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((k : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  exact ⟨α, hα⟩

theorem exists_symLift_near (hG : GlobalFnsSt) (P : PolAV S) {k : ℕ} (hk : Odd k) {T : Over S} (y : T ⟶ P.A)
    (hy : y ^ k = 1) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∀ (T' : Over S) (h : T' ⟶ T), Set.range h.left ⊆ V →
      ∃ θ : ThetaGrp P.A P.L k T', SymLift P.A P.L k k (h ≫ y) θ := by
  obtain ⟨V, hV, θ, hθ⟩ := ((symLift_odd hG
    (kerPow_of_square (AbSquare.square_of_cube AbLaw.CubeAssembly.cube_gen).1).2.2 (exists_gen_negLB hG)).1
      S P k hk T y hy).1 p
  refine ⟨V, hV, fun T' h hh => ?_⟩
  have hr : Set.range h.left ⊆ Set.range V.ι := hh.trans (Scheme.Opens.range_ι V).ge
  let l : T' ⟶ overRes V := Over.homMk (IsOpenImmersion.lift V.ι h.left hr) (by
    show IsOpenImmersion.lift V.ι h.left hr ≫ V.ι ≫ T.hom = T'.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w h])
  have e : l ≫ overResι V = h := Over.OverMorphism.ext (IsOpenImmersion.lift_fac V.ι h.left hr)
  obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB l hθ
  exact ⟨θ', by rw [← e, Category.assoc]; exact hθ'⟩

theorem exists_affine_nhds {R : Type} [CommRing R] (W : (Sp R).Opens) (p : Sp R) (hp : p ∈ W) :
    ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧
      Set.range (spMap φ) ⊆ W := by
  obtain ⟨_, ⟨r, rfl⟩, hr, hW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := W.1) hp W.isOpen
  have e : Set.range (spMap (algebraMap R (Localization.Away r))) = (PrimeSpectrum.basicOpen r).1 :=
    PrimeSpectrum.localization_away_comap_range (R := R) (Localization.Away r) r
  refine ⟨Localization.Away r, inferInstance, algebraMap _ _, ?_, e.ge hr, e.le.trans hW⟩
  exact inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))

theorem lab_pow {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} (t : TObj g k J b s)
    (a : Ix g k) : t.lab a ^ k = 1 := by
  have := t.ab.comm
  rw [TObj.lab, linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]

end GlobalTheory.EmbLocal

namespace GlobalTheory

open EmbLocal

theorem exists_emb_locally : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S), Odd N' → m ∣ N' → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ := by
  intro hL hL2 o _ g N' J b S s t m R _ x hN hm p
  have hmo : Odd m := hN.of_dvd_nat hm
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN.pos.ne'⟩
  let u : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have hy : ∀ a, ((u ≫ t.lab a) ^ ((N' / m) ^ 2)) ^ (m ^ 2) = 1 := fun a => by
    rw [← pow_mul, ← mul_pow, Nat.div_mul_cancel hm, ← MonObj.comp_pow, lab_pow, MonObj.comp_one]
  obtain ⟨V, hV, hth⟩ := exists_isGenSec_near hL2.secBaseChangeAny t.pol (x p)
  choose W hW hU using fun a => exists_symLift_near hL.globalFns t.pol (k := m ^ 2) hmo.pow
    (T := Over.mk x) _ (hy a) p
  obtain ⟨R', _, φ, hφ, hp, hsub⟩ := exists_affine_nhds
    (x ⁻¹ᵁ V ⊓ ⟨⋂ a, (W a).1, isOpen_iInter_of_finite fun a => (W a).isOpen⟩) p
    ⟨hV, Set.mem_iInter.2 hW⟩
  let T : Over S := Over.mk (spMap φ ≫ x)
  let h : T ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  obtain ⟨th, hth⟩ := hth R' (spMap φ ≫ x) (by
    rintro _ ⟨z, rfl⟩
    exact (hsub ⟨z, rfl⟩).1)
  obtain ⟨α, hα⟩ := exists_mulPull hL.globalFns t.pol m T
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull t.isLB (Out.mulT t.A T m) (snd T t.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 α hα th
  have hU' : ∀ a, ∃ θ : Out.ThetaGrp t.A t.L ((m : ℤ) ^ 2) T, Out.SymLift t.A t.L ((m : ℤ) ^ 2) (m ^ 2)
      (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2)) θ := fun a => by
    obtain ⟨θ, hθ⟩ := hU a T h fun z hz => Set.mem_iInter.1 (hsub hz).2 a
    rw [← Nat.cast_pow]
    refine ⟨θ, ?_⟩
    have e : h ≫ (u ≫ t.lab a) ^ ((N' / m) ^ 2) =
        ((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2) := by
      rw [MonObj.comp_pow, ← Category.assoc]; rfl
    rw [← e]
    exact hθ
  choose U hU' using hU'
  choose σ hσ using fun a => ThetaPtExist.exists_isTwistPull t.isLB (Out.translT t.A (U a).pt)
    (Out.translPt t.A (U a).pt) (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (U a).φ (U a).isGen s₁
  exact ⟨R', inferInstance, φ, σ, hφ, hp, th, s₁, α, U, hth, hα, hs₁, hU', hσ⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELFrom

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have hc : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem fromC_of_isPEL : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  intro hL _ E _ _ _ H D g J _ a w w' bas _ _ _ _ hcl N' o _ b em ρ _ hb S s t τ hτ K _ _ x
  obtain ⟨β', hβ'⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, x ≫ s = spMap β := ⟨β'.hom, hβ'.symm⟩
  obtain ⟨tx, htx⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b S (Sp K) s (spMap β) x t hβ
  obtain ⟨τx, hτx⟩ := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ S (Sp K) s (spMap β) x t tx τ hβ htx hτ
  obtain ⟨K₀, β₀, t₀, hβ₀, hcount, -, ht₀⟩ := GlobalTheory.T.thetaLevel_object_descends_fg_subfield o g (N' ^ 2) J b K β tx
  haveI : Countable K₀ := hcount (countable_of_finiteType o hb.2.1)
  have hcomp : spMap β = spMap K₀.subtype ≫ spMap β₀ := by
    rw [← hβ₀, ← Spec.map_comp]; rfl
  obtain ⟨τ₀, hτ₀⟩ := GlobalTheory.T.pelStructure_descends_field_extension hL E H D g (N' ^ 2) J a bas o b ρ K₀ K K₀.subtype β₀ (spMap β) t₀ tx τx
    hcl hcomp ht₀ hτx
  obtain ⟨-, j, hj⟩ := GlobalTheory.T.exists_ringHom_complex_comp_eq_of_countable_field o em K₀ β₀ hb.1 hb.2.1 hb.2.2
  have hjc : spMap j ≫ spMap β₀ = spMap em := by
    rw [← hj, ← Spec.map_comp]; rfl
  obtain ⟨tc, htc⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j) t₀ hjc
  have hc := GlobalTheory.PELPull.isPEL_pull E H D g (N' ^ 2) J a bas o b ρ (Sp K₀) (Sp ℂ) (spMap β₀) (spMap em) (spMap j)
    t₀ tc τ₀ hjc htc hτ₀
  unfold FromC
  rw [hβ]
  exact ⟨K₀, inferInstance, β₀, K₀.subtype, j, t₀, tx, tc, hj, hcomp, htx, ht₀, htc, hc⟩

end GlobalTheory.PELFrom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pelObject_fibre_from_complex_charZero : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (τ : SAB H S), IsPEL D a bas ρ t τ → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (PELClass (b := b) D a bas ρ em) t x := by
  first | exact @GlobalTheory.PELFrom.fromC_of_isPEL | exact GlobalTheory.PELFrom.fromC_of_isPEL | (intros; apply GlobalTheory.PELFrom.fromC_of_isPEL <;> assumption)
end
end
