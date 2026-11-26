module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelCoverField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam

theorem lbIso_pow_pull_square {B B' G G' : Scheme.{0}} {β : B' ⟶ B} {π : G' ⟶ G} {φ : B ⟶ G} {φ' : B' ⟶ G'}
    (h : φ' ≫ π = β ≫ φ) {P : LB G} {P' : LB G'} {M : LB B} {M' : LB B'} (hP : P.IsLB) (hP' : P'.IsLB)
    (hM : M.IsLB) (hM' : M'.IsLB) (eP : LBIso P' (P.pull π)) (eM : LBIso M' (M.pull β)) {n : ℕ}
    (hI : LBIso (lbPow M n) (P.pull φ)) : LBIso (lbPow M' n) (P'.pull φ') := by
  obtain ⟨w, hw⟩ := eP
  have e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π)) :=
    iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)
  have e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β) :=
    LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))
  have e₃ := LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂
  refine LBIso.trans (isLB_lbPow hM' _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _) ?_ e₃.symm
  exact LBIso.trans (isLB_lbPow hM' _) (isLB_lbPow (pull_isLB hM _) _) (pull_isLB (pull_isLB hP _) _)
    (lbIso_lbPow eM _) (LBIso.chartPull (chartPullPowPull M β _) (chartPullPull _ β) hI)

theorem KerSet.pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'} [GrpObj G] [GrpObj G']
    {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} (hβ : β ≫ B.hom = B'.hom ≫ f) (hπ : IsGrpPullback G' G f π)
    {ψ : B ⟶ G} {ψ' : B' ⟶ G'} (h : ψ'.left ≫ π = β ≫ ψ.left) {K : Set B.left} (hK : KerSet ψ K) :
    KerSet ψ' (β ⁻¹' K) := by
  intro k _ _ x z
  have e : pushHom hπ (Over.mk x) (z ≫ ψ') = pushPt hβ z ≫ ψ := Over.OverMorphism.ext (by
    show (z.left ≫ ψ'.left) ≫ π = (z.left ≫ β) ≫ ψ.left
    rw [Category.assoc, Category.assoc, h])
  have e₁ : z ≫ ψ' = 1 ↔ pushPt hβ z ≫ ψ = 1 := by
    rw [← e]
    refine ⟨fun q => by rw [q, map_one], fun q => PureType.eq_of_comp_eq hπ.1 ?_⟩
    exact congrArg (fun u => u.left) (q.trans (map_one (pushHom hπ (Over.mk x))).symm)
  refine e₁.trans ((hK k (x ≫ f) (pushPt hβ z)).trans ?_)
  show Set.range (z.left ≫ β) ⊆ K ↔ _
  simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]

theorem isog_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l p S S' s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ
  have c₁ := n₁.toSABMap.cart
  have c₂ := n₂.toSABMap.cart
  refine ⟨?_, fun ψ' h => ⟨?_, fun K _ hK => KerSet.pull c₁.1.w c₂ h hK⟩⟩
  · obtain ⟨ψ', h⟩ := PureType.exists_hom_over c₁.1.w c₂.1 ψ
    exact ⟨ψ', h, fun χ hχ => PureType.eq_of_comp_eq c₂.1 (hχ.trans h.symm)⟩
  rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩
  have sq : IsPullback n₁.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact c₁.1) h.symm c₂.1
  have lev : ∀ {u : 𝟙_ (Over S) ⟶ o₁.t.G} {v : 𝟙_ (Over S) ⟶ o₂.t.G} {u' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {v' : 𝟙_ (Over S') ⟶ o₂'.t.G}, u'.left ≫ n₁.toSABMap.φ = f ≫ u.left → v'.left ≫ n₂.toSABMap.φ = f ≫ v.left →
      u ≫ ψ = v → u' ≫ ψ' = v' := fun {u v u' v'} hu hv e => PureType.eq_of_comp_eq c₂.1 (by
    refine Eq.trans ?_ hv.symm
    rw [← e, Over.comp_left, Over.comp_left, Category.assoc]
    exact (congrArg (u'.left ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ψ.left) hu).trans (Category.assoc _ _ _))))
  refine ⟨⟨PureType.isMonHom_over c₁ c₂ h, MorphismProperty.of_isPullback (P := @IsFinite) sq h₂,
    MorphismProperty.of_isPullback (P := @Etale) sq h₃, MorphismProperty.of_isPullback (P := @Surjective) sq h₄,
    fun a => PureType.eq_of_comp_eq c₂.1 ?_, ?_⟩, fun p' hp a =>
    ⟨lev (n₁.eta _) (n₂.eta _) (h₇ p' hp a).1, lev (n₁.etaA _) (n₂.etaA _) (h₇ p' hp a).2⟩⟩
  · have e : (o₁.t.act.act a).left ≫ ψ.left = ψ.left ≫ (o₂.t.act.act a).left := congrArg (fun u => u.left) (h₅ a)
    have h' : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := h
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, n₂.act, h', reassoc_of% h',
      reassoc_of% (n₁.act a), e]
  · exact lbIso_pow_pull_square h o₂.t.PP.isLB o₂'.t.PP.isLB o₁.t.PP.isLB o₁'.t.PP.isLB
      (n₂.lin.imp fun _ q => q.1) (n₁.lin.imp fun _ q => q.1) h₆

end GlobalTheory.HkFam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.HkFam.isog_pull | exact GlobalTheory.HkFam.isog_pull | (intros; apply GlobalTheory.HkFam.isog_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemNonzeroLocusOfIsActOf
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoprimeTorsion

open CommutatorPairing

section General

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)

def chartPullLPow (n : ℕ) : ChartPull (LPow A L n T) (lbPow L n) (snd T A).left where
  idx j := fun _ => j 0
  le j y hy := mem_powChart.2 (Set.mem_iInter.1 hy 0)
  g y j j' hj hj' := by
    refine (gm_linComb L (fun _ : Fin 1 => (snd T A).left) (fun _ => (n : ℤ)) (𝟙 _) y j j' hj hj').trans
      (Eq.trans ?_ (gm_lbPow_g n (snd T A).left y _ _ (mem_powChart.2 (Set.mem_iInter.1 hj 0))
        (mem_powChart.2 (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fin.prod_univ_one, Category.id_comp, zpow_natCast]

theorem nonzeroLocus_chartPullLPow (n : ℕ) (s : (lbPow L n).Sec) :
    nonzeroLocus (chartSec (chartPullLPow A L T n) s) = (snd T A).left ⁻¹ᵁ nonzeroLocus s :=
  nonzeroLocus_chartSec _ s fun _ J hJ => ⟨fun _ => J PUnit.unit, Set.mem_iInter.2 fun _ => mem_powChart.1 hJ⟩

def vanishing (a : ℤ) (E : Set (T ⊗ A).left) : Submodule Γ(T.left, ⊤) (SecM A L a T) where
  carrier := {f | ∀ y ∈ E, y ∉ nonzeroLocus (SecM.toSec A f)}
  add_mem' := by
    intro f f' hf hf' y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    rcases Scheme.basicOpen_add_le _ (f.1 k) (f'.1 k) hk with h | h
    · exact hf y hy (Opens.mem_iSup.2 ⟨k, h⟩)
    · exact hf' y hy (Opens.mem_iSup.2 ⟨k, h⟩)
  zero_mem' := by
    intro y _ h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact (Scheme.basicOpen_zero _ _).le hk
  smul_mem' := by
    intro c f hf y hy h
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
    exact hf y hy (Opens.mem_iSup.2 ⟨k, ((Scheme.basicOpen_mul _ (liftHom A _ c) (f.1 k)).le hk).2⟩)

variable {A L T}

theorem mem_nonzeroLocus_of_isActOf (hL : L.IsLB) {a : ℤ} {θ : ThetaGrp A L a T} {s s' : LB.Sec (LPow A L a T)}
    (h : IsActOf A L a θ s s') {y : (T ⊗ A).left} (hy : y ∈ nonzeroLocus s') :
    (translT A θ.pt).left y ∈ nonzeroLocus s := by
  obtain ⟨k, hk, hu⟩ := (mem_nonzeroLocus s' y).1 hy
  obtain ⟨i, hi⟩ := exists_chart hL ((translPt A θ.pt).left y)
  obtain ⟨i₀, rfl⟩ : ∃ i₀ : L.ι, k = fun _ => i₀ := ⟨k 0, funext fun b => congrArg k (Subsingleton.elim _ _)⟩
  have hm : y ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] ![i₀, i] := Set.mem_iInter.2 fun b => by
    fin_cases b
    exacts [Set.mem_iInter.1 hk 0, hi]
  have hp := chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) ![i₀, i] hm
  have e := (gs_res (𝟙 _) y _ hm _).symm.trans ((congrArg (gs (𝟙 _) y _) (h ![i₀, i])).trans
    ((gs_mul (𝟙 _) y _ hm _ _).trans (congrArg (_ * ·) ((gs_res (𝟙 _) y _ hm _).trans
      (gs_pull (𝟙 _) (translT A θ.pt).left y _ hp _)))))
  have u := isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp hu)
  rw [Category.id_comp] at u
  exact (mem_nonzeroLocus_iff_pull s (translT A θ.pt).left y (k := fun _ => i) hp).2 u

end General

theorem dense_torsion (hA : AmpleSt) (hK : KerPowSt) (hI : IrredSt) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : PolAV (Sp k)) {p : ℕ} (hp : p.Prime) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1}, Set.range x.left) := by
  haveI : IsCommMonObj P.A := P.isAb.comm
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (U := ⟨U, hU⟩) hy₀
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA k P N hN
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, hmp⟩ : ∃ m : ℕ, 4 ≤ m ∧ m.Coprime p :=
    ⟨p * 2 + 1, by have := hp.two_le; omega, by simp⟩
  obtain ⟨t, ht⟩ := gen m hm y₀
  let n := a * p + m
  have hn : 4 ≤ n := le_add_left hm
  have hnp : n.Coprime p := by simpa [n] using hmp
  let σ : (lbPow P.L n).Sec := secMul (secPow s p) t
  have hσ : nonzeroLocus σ = nonzeroLocus s ⊓ nonzeroLocus t := by
    rw [nonzeroLocus_secMul, nonzeroLocus_secPow s hp.one_le]
  let B := baseOver (Sp k)
  let β : ∀ T : Over (Sp k), T ⟶ B := fun T => Over.homMk T.hom (Category.comp_id _)
  let E : Set (B ⊗ P.A).left := ⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ x ^ n = 1},
    Set.range (lift (β _) x).left
  have hsnd : ∀ {T : Over (Sp k)} (x : T ⟶ P.A) (z : T.left), (snd B P.A).left ((lift (β T) x).left z) = x.left z :=
    fun x z => congrArg (fun q => q.left z) (lift_snd (β _) x)
  rcases hI k P n (Or.inr hn) (Nat.cast_ne_zero.2 (by omega)) (vanishing P.A P.L B n E) (fun θ r r' hr h y hy hy' => by
      refine h _ ?_ (mem_nonzeroLocus_of_isActOf P.isLB hr hy')
      obtain ⟨x, ⟨l, hl, hlp, hx⟩, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have hθ : θ.pt ^ n = 1 := (hK _ P n (by omega) B θ.pt).1 fun q =>
        ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩
      refine Set.mem_iUnion₂.2 ⟨(β _ ≫ θ.pt) * x, ⟨n * l, by positivity, Nat.Coprime.mul_left hnp hlp, ?_⟩, z,
        (congrArg (fun q => q.left z) (lift_translT θ.pt (β _) x)).symm⟩
      rw [mul_pow, pow_mul, pow_mul', hx, ← MonObj.comp_pow, hθ, MonObj.comp_one, one_pow, one_pow,
        _root_.mul_one]) with h | h
  · have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n E := fun y hy hy' => by
      obtain ⟨x, hx, z, rfl⟩ := Set.mem_iUnion₂.1 hy
      have h₁ : (snd B P.A).left ((lift (β _) x).left z) ∈ nonzeroLocus σ :=
        (nonzeroLocus_chartPullLPow P.A P.L B n σ).le hy'
      rw [hsnd, hσ] at h₁
      exact hne ⟨_, hle h₁.1, Set.mem_iUnion₂.2 ⟨x, hx, z, rfl⟩⟩
    rw [h, Submodule.mem_bot] at hmem
    have h₂ : (lift (β _) (𝟙 P.A)).left y₀ ∈ nonzeroLocus (chartSec (chartPullLPow P.A P.L B n) σ) :=
      (nonzeroLocus_chartPullLPow P.A P.L B n σ).ge (show (snd B P.A).left _ ∈ nonzeroLocus σ by
        rw [hsnd, hσ]; exact ⟨hs, ht⟩)
    exact (hmem ▸ (vanishing P.A P.L B n Set.univ).zero_mem :
      SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) σ) ∈ vanishing P.A P.L B n Set.univ) _ trivial h₂
  · let z : (𝟙_ (Over (Sp k))).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
    obtain ⟨τ, hτ⟩ := gen n hn ((1 : 𝟙_ (Over (Sp k)) ⟶ P.A).left z)
    have hmem : SecM.ofSec P.A (chartSec (chartPullLPow P.A P.L B n) τ) ∈ vanishing P.A P.L B n E := by
      rw [h]; trivial
    refine hmem ((lift (β _) 1).left z) (Set.mem_iUnion₂.2 ⟨1, ⟨1, one_pos, by simp, one_pow _⟩, z, rfl⟩)
      ((nonzeroLocus_chartPullLPow P.A P.L B n τ).ge ?_)
    show (snd B P.A).left _ ∈ nonzeroLocus τ
    rw [hsnd]; exact hτ

end GlobalTheory.CoprimeTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyObjMapOfFiniteEtaleCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyObjMapOfFiniteEtaleCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjDescent

theorem isGrpPullback_id {S S₂ : Scheme.{0}} {G G' : Over S} {G₂ : Over S₂} [GrpObj G] [GrpObj G'] [GrpObj G₂]
    {q : S₂ ⟶ S} [Flat q] [Surjective q] {a : G₂.left ⟶ G.left} {c : G₂.left ⟶ G'.left}
    (h : IsGrpPullback G₂ G q a) (h' : IsGrpPullback G₂ G' q c) (φ : G.left ⟶ G'.left) [IsIso φ] (e : a ≫ φ = c)
    (w : φ ≫ G'.hom = G.hom ≫ 𝟙 S) : IsGrpPullback G G' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨w⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let r := pullback.fst T.hom q
  have : Epi r := Flat.epi_of_flat_of_surjective _
  let T' : Over S₂ := Over.mk (pullback.snd T.hom q)
  have up : ∀ z : T ⟶ G, ∃ z' : T' ⟶ G₂, r ≫ z.left = z'.left ≫ a := fun z =>
    ⟨Over.homMk (h.1.lift (r ≫ z.left) (pullback.snd T.hom q)
      (by rw [Category.assoc, Over.w z]; exact pullback.condition)) (h.1.lift_snd _ _ _),
      (h.1.lift_fst _ _ _).symm⟩
  obtain ⟨x', hx'⟩ := up x
  obtain ⟨y', hy'⟩ := up y
  let R : Over.mk (T'.hom ≫ q) ⟶ T := Over.homMk r pullback.condition
  let R' : Over.mk (T'.hom ≫ q) ⟶ Over.mk (T.hom ≫ 𝟙 S) :=
    Over.homMk r ((congrArg (r ≫ ·) (Category.comp_id T.hom)).trans pullback.condition)
  have e₁ := h.2 T' x' y' (R ≫ x) (R ≫ y) hx' hy'
  have e₂ := h'.2 T' x' y' (R' ≫ x₀) (R' ≫ y₀)
    (by show r ≫ x₀.left = _; rw [hx, ← Category.assoc, hx', Category.assoc, e])
    (by show r ≫ y₀.left = _; rw [hy, ← Category.assoc, hy', Category.assoc, e])
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← cancel_epi r, ← Category.assoc]
  refine e₂.trans ?_
  rw [← e, ← Category.assoc]
  exact congrArg (· ≫ φ) e₁.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S₂ : Scheme.{0}} {s : S ⟶ Sp B} {s' : S ⟶ Sp B'} {s'' : S₂ ⟶ Sp B''}
  {u : Obj D l b s} {ob : Obj D l b' s'} {ob₂ : Obj D l b'' s''} {q : S₂ ⟶ S}

theorem exists_congr {q' : S₂ ⟶ S} (e : q = q') (m : ObjMap ob₂ ob q) :
    ∃ m' : ObjMap ob₂ ob q', m'.toSABMap.φ = m.toSABMap.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem comp_eq_of_comp_eq (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ ob₂.t.G.left) (h : g₁ ≫ m.toSABMap.φ = g₂ ≫ m.toSABMap.φ) :
    g₁ ≫ n.toSABMap.φ = g₂ ≫ n.toSABMap.φ := by
  have hp : (g₁ ≫ ob₂.t.G.hom) ≫ q = (g₂ ≫ ob₂.t.G.hom) ≫ q := by
    rw [Category.assoc, Category.assoc, ← m.cart.1.w, ← Category.assoc, h, Category.assoc]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l B'' B'' b'' b'' (RingHom.id _) S₂ Z s'' ((g₁ ≫ ob₂.t.G.hom) ≫ s'')
    (g₁ ≫ ob₂.t.G.hom) rfl rfl ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) ob₂
  obtain ⟨k, hk⟩ := ObjComp.objMap_comp m m₁
  obtain ⟨k', hk'⟩ := exists_congr hp k
  obtain ⟨m₂, hm₂⟩ := ObjComp.objMap_cancel m k'
  obtain ⟨n₁, hn₁⟩ := ObjComp.objMap_comp n m₁
  obtain ⟨n₁', hn₁'⟩ := exists_congr hp n₁
  obtain ⟨n₂, hn₂⟩ := ObjComp.objMap_comp n m₂
  have e := obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ _ _ _ _ u o _
    n₁'.toSABMap n₂.toSABMap fun a => ⟨_, n₁'.eta a, n₂.eta a⟩
  rw [hn₁', hn₁, hn₂] at e
  rw [hk', hk] at hm₂
  let σ := m₁.cart.1.lift g₁ (𝟙 Z) (Category.id_comp _).symm
  have h₁ : σ ≫ m₁.toSABMap.φ = g₁ := m₁.cart.1.lift_fst _ _ _
  have h₀ : σ ≫ o.t.G.hom = 𝟙 Z := m₁.cart.1.lift_snd _ _ _
  have h₂ : σ ≫ m₂.toSABMap.φ = g₂ := by
    apply m.cart.1.hom_ext
    · rw [Category.assoc]
      refine (congrArg (σ ≫ ·) hm₂.symm).trans ?_
      rw [← Category.assoc, h₁, h]
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, h₀, Category.id_comp]
  refine (congrArg (· ≫ n.toSABMap.φ) h₁).symm.trans (Eq.trans ?_ (congrArg (· ≫ n.toSABMap.φ) h₂))
  exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) e).trans (Category.assoc _ _ _).symm)

variable [Flat q] [Surjective q] [QuasiCompact q]

theorem effectiveEpi (m : ObjMap ob₂ ob q) : EffectiveEpi m.toSABMap.φ := by
  have : Flat m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  infer_instance

theorem exists_fac (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    ∃ φ : ob.t.G.left ⟶ u.t.G.left, m.toSABMap.φ ≫ φ = n.toSABMap.φ :=
  have := effectiveEpi m
  ⟨EffectiveEpi.desc m.toSABMap.φ n.toSABMap.φ (comp_eq_of_comp_eq hL m n), EffectiveEpi.fac _ _ _⟩

theorem nonempty_objMap_id (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    Nonempty (ObjMap ob u (𝟙 S)) := by
  obtain ⟨φ, hφ⟩ := exists_fac hL m n
  obtain ⟨ψ, hψ⟩ := exists_fac hL n m
  have := effectiveEpi m
  have := effectiveEpi n
  have : Epi q := Flat.epi_of_flat_of_surjective _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, hψ, Category.comp_id],
    by rw [← cancel_epi n.toSABMap.φ, ← Category.assoc, hψ, hφ, Category.comp_id]⟩
  have w : φ ≫ u.t.G.hom = ob.t.G.hom ≫ 𝟙 S := by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, Category.comp_id, m.cart.1.w, n.cart.1.w]
  have gp : IsGrpPullback ob.t.G u.t.G (𝟙 S) φ := isGrpPullback_id m.cart n.cart φ hφ w
  have hact : ∀ a, (ob.t.act.act a).left ≫ φ = φ ≫ (u.t.act.act a).left := fun a => by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, ← m.act, Category.assoc, hφ, n.act, ← Category.assoc, hφ]
  have hiso : LBIso ob.t.PP.L (u.t.PP.L.pull φ) := by
    have h₁ := ob.t.PP.isLB
    have h₂ := pull_isLB u.t.PP.isLB φ
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ u.t.PP.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have cl : ∀ {t : SAB H S} (k : SABMap ob₂.t t q),
        CechPic.cls _ ob₂.t.PP.isLB = CechPic.pull k.φ (CechPic.cls _ t.PP.isLB) := fun {t} k => by
      obtain ⟨w, hw, -⟩ := k.lin
      exact (CechPic.cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    have z : ∀ t : SAB H S, CechPic.pull (eSec t.G) (CechPic.cls _ t.PP.isLB) = 0 := fun t =>
      (CechPic.cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange hL.globalFns S S₂ q ob.t.G _ (ObjDim.isAbelianScheme ob) hN inferInstance inferInstance
      inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · have he : eSec ob.t.G ≫ φ = 𝟙 S ≫ eSec u.t.G := (cubeMapOf gp).e_comm
      rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, z, he, Category.id_comp, z, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← m.cart.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp,
        hφ, ← cl, ← cl, sub_self, map_zero]
  obtain ⟨k, hk⟩ := exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S u.t ob.t (𝟙 S) φ u.proper gp hiso hact
  have key : ∀ (σ₂ : S₂ ⟶ ob₂.t.G.left) (σ : S ⟶ ob.t.G.left) (τ : S ⟶ u.t.G.left),
      σ₂ ≫ m.toSABMap.φ = q ≫ σ → σ₂ ≫ n.toSABMap.φ = q ≫ τ → σ ≫ k.φ = 𝟙 S ≫ τ := fun σ₂ σ τ h₁ h₂ => by
    rw [← cancel_epi q, hk, Category.id_comp, ← Category.assoc, ← h₁, ← h₂, Category.assoc, hφ]
  exact ⟨⟨k, fun a => key _ _ _ (m.eta a) (n.eta a), fun a => key _ _ _ (m.etaA a) (n.etaA a)⟩⟩

end GlobalTheory.ObjDescent

namespace GlobalTheory

theorem nonempty_objMap_of_finite_etale_cover : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (X S S₂ : Scheme.{0}) (s : X ⟶ Sp B) (s' : S ⟶ Sp B') (s'' : S₂ ⟶ Sp B'') (u : Obj D l b s) (ob : Obj D l b' s') (ob₂ : Obj D l b'' s'') (q : S₂ ⟶ S) (f : S ⟶ X), (IsReduced S ∨ IsLocallyNoetherian S) → IsFinite q → Etale q → Surjective q → Nonempty (ObjMap ob₂ ob q) → Nonempty (ObjMap ob₂ u (q ≫ f)) → Nonempty (ObjMap ob u f) := by
  intro hL _ E _ _ _ H D l B B' B'' _ _ _ b b' b'' X S S₂ s s' s'' u ob ob₂ q f _ _ _ _ ⟨m⟩ ⟨n⟩
  obtain ⟨u', ⟨p⟩⟩ := obj_pull E H D l B B b b (RingHom.id _) X S s (f ≫ s) f rfl rfl
    ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) u
  obtain ⟨n', -⟩ := ObjComp.objMap_cancel p n
  obtain ⟨k⟩ := ObjDescent.nonempty_objMap_id hL m n'
  obtain ⟨k', -⟩ := ObjComp.objMap_comp p k
  obtain ⟨k'', -⟩ := ObjDescent.exists_congr (Category.id_comp f) k'
  exact ⟨k''⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyObjMapOfFiniteEtaleCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_objMap_of_finite_etale_surjective_cover : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (X S S₂ : Scheme.{0}) (s : X ⟶ Sp B) (s' : S ⟶ Sp B') (s'' : S₂ ⟶ Sp B'') (u : Obj D l b s) (ob : Obj D l b' s') (ob₂ : Obj D l b'' s'') (q : S₂ ⟶ S) (f : S ⟶ X), (IsReduced S ∨ IsLocallyNoetherian S) → IsFinite q → Etale q → Surjective q → Nonempty (ObjMap ob₂ ob q) → Nonempty (ObjMap ob₂ u (q ≫ f)) → Nonempty (ObjMap ob u f) := by
  first | exact @GlobalTheory.nonempty_objMap_of_finite_etale_cover | exact GlobalTheory.nonempty_objMap_of_finite_etale_cover | (intros; apply GlobalTheory.nonempty_objMap_of_finite_etale_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjectiveOfLaws
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.LevelCover

namespace GlobalTheory.LevCover

private theorem levStrRep_lemma (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [Field B] {b : Base l B} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp B} (o : Obj D l b s) (hpq : 1 ≤ D.p + D.q) (l₂ : Level H) (b₂ : Base l₂ B) (hd : l.Dvd l₂)
    (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) :
    ∃ (V : Over S) (χ θ : D.La → (V ⟶ o.t.G)), IsFinite V.hom ∧ Etale V.hom ∧ Surjective V.hom ∧
      LevStr o b₂ V χ θ ∧
      (∀ (T : Over S) (u u' : T ⟶ V), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), LevStr o b₂ T χ' θ' →
        ∃ h : T ⟶ V, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  have hsim := SimAlg.sim_group E H D hpq
  obtain ⟨hfree, hfin⟩ := datum_free D
  refine exists_levStr_rep o l₂ b₂ hd hζ (fun g n k hn hk => hsim.1 g n k hn hk)
    (fun N f ν => exists_sim_lift E H D N f ν)
    (fun l' N ν => SimMult.exists_sim_trivial_of_mult SimAlg.sim_group exists_sim_lift E H D l' N ν) ?_ ?_
  · intro n hn
    have hu : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
      simpa using (b.unit n hn).map (fnOn s)
    obtain ⟨Z, et, hZ⟩ :=
      exists_finiteEtale_latticeTorsionHom S o.t.G n D.La (ObjDim.isAbelianScheme o) hu
    exact ⟨Z, et, hZ⟩
  · intro N _ T x y c hN hx hy hc
    exact PairingLocus.exists_clopen_of_isLocallyNoetherian hL S (GlobalTheory.Obj.toPolAV o) N T x y c hN hx hy hc

private theorem weilIs_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (T' : Over S') (k : ℤ) (x y : T' ⟶ t'.G)
    (x₀ y₀ : Over.mk (T'.hom ≫ f) ⟶ t.G) (c : Γ(T'.left, ⊤)ˣ) (h₁ : x₀.left = x.left ≫ m.φ)
    (h₂ : y₀.left = y.left ≫ m.φ) : Out.WeilIs t'.G t'.PP.L k x y c ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ c :=
  weilIs_grpPullback_of_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart (sabMap_lbIso m)
    T' k x y x₀ y₀ c h₁ h₂

private theorem lieMult_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (k : Type) [Field k] (x : Sp k ⟶ S')
    (τ : 𝓞 E →+* k) (n : ℕ) : LieMult t'.act x τ n ↔ LieMult t.act (x ≫ f) τ n :=
  LiePull.lieMult_pull (𝓞 E) S S' t.G t'.G f m.φ t.act t'.act m.cart m.act k x τ n

theorem levelCover_noetherian (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsLocallyNoetherian S → 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o hS hpq hd hρ hζ
  have := hS
  obtain ⟨V, χ, θ, hVf, hVe, hVs, hlev, hext, hex⟩ := levStrRep_lemma hL o hpq l₂ b₂ hd hζ
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l B B b b (RingHom.id B) S V.left s (V.hom ≫ s) V.hom rfl rfl
    (by rw [spMap_id', Category.comp_id]) o
  obtain ⟨o₂, m, hm, hχ, hθ⟩ := obj_of_levStr o hρ V o₁.t n₁.toSABMap (weilIs_iff_of_sabMap n₁.toSABMap)
    (fun k _ x τ n => lieMult_iff_of_sabMap n₁.toSABMap k x τ n) o₁.ample o₁.ktriv hlev
  refine ⟨V.left, V.hom, o₂, m, hVf, hVe, hVs, hm, ?_⟩
  intro T f o' m' hc
  obtain ⟨χ', θ', hlev', hχ', hθ'⟩ := levStr_of_obj o (Over.mk f) o' m' (weilIs_iff_of_sabMap m') hc.1 hc.2
  obtain ⟨g, hgχ, hgθ⟩ := hex (Over.mk f) χ' θ' hlev'
  have hg : g.left ≫ V.hom = f := by simpa using Over.w g
  obtain ⟨u, hu⟩ := sab_cancel m m' g.left hg

  have key : ∀ a, ((o'.eta a).left ≫ m'.φ = g.left ≫ (o₂.eta a).left ≫ m.φ) ∧
      ((o'.etaA a).left ≫ m'.φ = g.left ≫ (o₂.etaA a).left ≫ m.φ) := fun a => by
    constructor
    · rw [← hχ' a, ← hgχ a, Over.comp_left, hχ a]
    · rw [← hθ' a, ← hgθ a, Over.comp_left, hθ a]
  have hη : ∀ a, (o'.eta a).left ≫ u.φ = g.left ≫ (o₂.eta a).left := fun a =>
    sec_cancel u m (o'.eta a) (o₂.eta a) (by rw [hu]; exact (key a).1)
  have hηA : ∀ a, (o'.etaA a).left ≫ u.φ = g.left ≫ (o₂.etaA a).left := fun a =>
    sec_cancel u m (o'.etaA a) (o₂.etaA a) (by rw [hu]; exact (key a).2)
  refine ⟨g.left, ⟨hg, ⟨u, hη, hηA⟩, hu⟩, ?_⟩
  rintro h' ⟨hh', ⟨u', hu₁, hu₂⟩, hu'⟩
  have hu'' : u'.cm.F ≫ m.φ = m'.φ := hu'
  have hgg : (Over.homMk h' hh' : Over.mk f ⟶ V) = g := by
    apply hext
    · intro a
      ext1
      simp only [Over.comp_left, hχ a, Over.homMk_left]
      rw [← (key a).1, ← Category.assoc, ← hu₁ a, Category.assoc, hu'']
    · intro a
      ext1
      simp only [Over.comp_left, hθ a, Over.homMk_left]
      rw [← (key a).2, ← Category.assoc, ← hu₂ a, Category.assoc, hu'']
  rw [← hgg]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem levelMap_over_field_noetherian (hL : Out.Laws)
    (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm₁ : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hm₂ : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (F : Type) [Field F] (b : Base l F) (b₂ : Base l₂ F) (j : KA l →+* F) (j₂ : KA l₂ →+* F)
    (e₁ : j (baseKA l).ρ = b.ρ) (e₂ : j (baseKA l).ζ = b.ζ) (e₃ : j₂ (baseKA l₂).ρ = b₂.ρ)
    (e₄ : j₂ (baseKA l₂).ζ = b₂.ζ) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (rF : pullback Xo₂.s (spMap j₂) ⟶ pullback Xo.s (spMap j))
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r) (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  have hsm0 : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hsm0₂ : Smooth Xo₂.s := by
    have := Xo₂.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo₂.s
  have hsmX : Smooth (pullback.snd Xo.s (spMap j)) := inferInstance
  have hsmX₂ : Smooth (pullback.snd Xo₂.s (spMap j₂)) := inferInstance
  obtain ⟨rX, -, nX⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX
  obtain ⟨rX₂, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX₂

  obtain ⟨o, ⟨no⟩⟩ := obj_pull E H D l (KA l) F (baseKA l) b j Xo.X (pullback Xo.s (spMap j)) Xo.s
    (pullback.snd _ _) (pullback.fst _ _) e₁ e₂ pullback.condition Xo.univ
  obtain ⟨o₂, ⟨no₂⟩⟩ := obj_pull E H D l₂ (KA l₂) F (baseKA l₂) b₂ j₂ Xo₂.X (pullback Xo₂.s (spMap j₂)) Xo₂.s
    (rF ≫ pullback.snd _ _) (pullback.fst _ _) e₃ e₄ (by rw [h₂]; exact pullback.condition) Xo₂.univ
  have hno1 : ∀ a, (o.eta a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.eta a).left := no.2
  have hno2 : ∀ a, (o.etaA a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.etaA a).left := no.3
  have hno₂1 : ∀ a, (o₂.eta a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.eta a).left := no₂.2
  have hno₂2 : ∀ a, (o₂.etaA a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.etaA a).left := no₂.3
  have hRX : Represents o := represents_pullback ObjMaps.id_comp_cancel Xo j
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo F b j S s o' hS e₁ e₂) rfl o no
  have hRX₂ : Represents o₂ := represents_pullback ObjMaps.id_comp_cancel Xo₂ j₂
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo₂ F b₂ j₂ S s o' hS e₃ e₄) h₂ o₂ no₂

  obtain ⟨Y, π, oc, mc, hπf, hπe, hπs, hmc, huniv⟩ :=
    levelCover_noetherian hL E H D l l₂ F b b₂ _ (pullback.snd Xo.s (spMap j)) o nX hpq hd hρ hζ
  have hsmπ : Smooth π := inferInstance
  have hsmY : Smooth (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
  obtain ⟨rY, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmY
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l F F b b (RingHom.id F) _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) π
    rfl rfl (by rw [spMap_id', Category.comp_id]) o

  obtain ⟨mcomp, hmcomp⟩ := sab_comp no₂.toSABMap m h₁.symm
  obtain ⟨m₂, hm₂'⟩ := sab_cancel no.toSABMap mcomp rF rfl
  have hm₂c : (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m₂.φ = rF ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m₂.φ = rF ≫ (o.etaA a).left) := by
    constructor
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂1 a), Category.assoc, hm₁ a, ← Category.assoc,
        ← h₁, Category.assoc, hno1 a]
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂2 a), Category.assoc, hm₂ a, ← Category.assoc,
        ← h₁, Category.assoc, hno2 a]
  obtain ⟨h, hiso, hπ⟩ := iso_cover ObjMaps.id_comp_cancel (l₂.M / l.M) (l₂.A / l.A) o o₂ oc o₁ n₁ m₂ mc hm₂c hmc
    hRX hRX₂ rX₂ rY (obj_rigid_closed hL E H D l F F b b _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) o o₁ π
      (Or.inl rY)) huniv
  rw [← hπ]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end

theorem levelMap_finite_etale_surjective_of_laws (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  intro E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hr c c₂ hc rF h₁ h₂
  obtain ⟨-, -, hm₁, hm₂⟩ := hr
  obtain ⟨F, fin, conj, zm, le⟩ := c
  obtain ⟨F₂, fin₂, conj₂, zm₂, le₂⟩ := c₂
  dsimp only at hc
  subst hc
  rw [spMap_inclusion_self, Category.comp_id] at h₂
  exact levelMap_over_field_noetherian hL Xo Xo₂ hpq hd r m hm₁ hm₂ F (baseOf l F le) (baseOf l₂ F le₂)
    (IntermediateField.inclusion le).toRingHom (IntermediateField.inclusion le₂).toRingHom rfl rfl rfl rfl
    (baseOf_rho l l₂ F le le₂) (baseOf_zeta l l₂ F le le₂ hd.2.2) rF h₁ h₂

end GlobalTheory.LevCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpClassPrimitiveIsoClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpClassPrimitiveIsoClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpPrim

theorem matrix_identities {n : Type} [Fintype n] [DecidableEq n] {W m m' : Matrix n n ℤ}
    (hd : (W + W.transpose).det = 1) (h : (W + W.transpose) * m = W) (h' : (W + W.transpose) * m' = W.transpose) :
    m + m' = 1 ∧ m.transpose * (W + W.transpose) = (W + W.transpose) * m' := by
  set G := W + W.transpose with hG
  have hu : IsUnit G.det := by rw [hd]; exact isUnit_one
  have hT : G.transpose = G := by
    rw [hG, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  constructor
  · have key : G * (m + m') = G := by rw [Matrix.mul_add, h, h']
    calc m + m' = G⁻¹ * (G * (m + m')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hu, Matrix.one_mul]
      _ = 1 := by rw [key, Matrix.nonsing_inv_mul G hu]
  · have ht := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, hT] at ht
    rw [ht, h']

theorem prod_mul_prod {M : Type} [CommGroup M] {n : ℕ} (x : Fin n → M) {m m' : Matrix (Fin n) (Fin n) ℤ}
    (h : m + m' = 1) (u : Fin n) :
    (List.ofFn fun v => x v ^ m u v).prod * (List.ofFn fun v => x v ^ m' u v).prod = x u := by
  have hm : ∀ v, m u v + m' u v = if u = v then 1 else 0 := by
    intro v
    have e := congrFun (congrFun h u) v
    rwa [Matrix.add_apply, Matrix.one_apply] at e
  rw [List.prod_ofFn, List.prod_ofFn, ← Finset.prod_mul_distrib]
  simp_rw [← zpow_add, hm]
  rw [Finset.prod_eq_single u (fun v _ hv => by rw [if_neg (Ne.symm hv), zpow_zero])
    (fun hu => absurd (Finset.mem_univ u) hu), if_pos rfl, zpow_one]

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k h : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem isSharp_of_tmap {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t t' : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) (m : TMap t' t (𝟙 _)) : IsSharp W a bas t' c := by
  obtain ⟨φ, hpb, hLφ, hpt, hact⟩ := m
  obtain ⟨pr, hpr, huniv, hL, hpa, hlev⟩ := H
  have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 t.A))
  obtain ⟨e, he, heφ'⟩ := grpPullback_iso hpb (isGrpPullback_of_iso (Iso.refl t.A))
  have heφ : e.hom.left = φ := by simpa using heφ'
  have hcomm : ∀ j, t'.act j ≫ e.hom = e.hom ≫ t.act j := by
    intro j
    ext
    simp only [Over.comp_left, heφ, hact j]
  refine ⟨fun u => e.hom ≫ pr u, fun u => ?_, fun T y => ?_, ?_, fun j u => ?_, fun i u => ?_⟩
  · have := hpr u
    infer_instance
  · obtain ⟨x0, hx0, hu0⟩ := huniv T y
    refine ⟨x0 ≫ e.inv, fun u => by simpa using hx0 u, fun x hx => ?_⟩
    have hx' : x ≫ e.hom = x0 := hu0 _ fun u => by simpa using hx u
    rw [← hx']
    simp
  · have hfun : (fun uv : Fin 8 × Fin 8 => (lift (e.hom ≫ pr uv.1) (e.hom ≫ pr uv.2)).left) =
        fun uv => φ ≫ (lift (pr uv.1) (pr uv.2)).left := by
      funext uv
      rw [← comp_lift, Over.comp_left, heφ]
    rw [hfun]
    refine (CechPic.cls_eq_iff t'.isLB (LB.isLB_linComb c.isLB _ _)).1 ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(CechPic.cls_eq_iff t'.isLB (pull_isLB t.isLB φ)).2 hLφ, CechPic.cls_pull t.isLB,
      (CechPic.cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL,
      CechPic.cls_linComb c.isLB, CechPic.cls_linComb c.isLB, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← CechPic.pull_comp]
  · rw [← Category.assoc, hcomm j, Category.assoc, hpa j u, PowerAdjoint.comp_prod_zpow]
  · have hp := hpt i
    rw [Category.id_comp] at hp
    rw [← hlev i u, Over.comp_left, Over.comp_left, heφ, ← Category.assoc, hp, Over.comp_left]

end GlobalTheory.SharpPrim

theorem GlobalTheory.sharpClass_prim_and_iso : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b (spMap em)), SharpClass W a bas em t → (IsE8 W → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → SharpClass W a bas em t' := by
  intro hΘ o _ g k J b em w w' h W a bas t ht
  obtain ⟨c, hc, hs⟩ := ht
  refine ⟨fun hE hw hw' => ?_, fun t' m => ⟨c, hc, SharpPrim.isSharp_of_tmap hs m⟩⟩
  obtain ⟨pr, hpr, huniv, hL, hact, -⟩ := hs
  have hid := SharpPrim.matrix_identities hE.2 hw hw'
  have key := PowerAdjoint.matrix_primitive_adjoint hΘ W ℂ o (spMap em) h k (b.ζ : o) c t.pol pr hpr huniv hL
    (a w) (t.act w) (hact w)
  refine ⟨?_, key.2 (a w') (t.act w') (hact w') hid.2, key.1 hw⟩
  obtain ⟨x0, -, hu0⟩ := huniv t.A pr
  have h1 : ∀ u, (t.act w * t.act w') ≫ pr u = pr u := by
    intro u
    have := hpr u
    rw [MonObj.mul_comp, hact w u, hact w' u]
    exact SharpPrim.prod_mul_prod pr hid.1 u
  rw [hu0 _ h1, hu0 (𝟙 t.A) fun u => Category.id_comp _]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpClassPrimitiveIsoClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharpClass_prim_and_closed_under_tMap : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b (spMap em)), SharpClass W a bas em t → (IsE8 W → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → t.Prim w w') ∧ ∀ t' : TObj g k J b (spMap em), TMap t' t (𝟙 _) → SharpClass W a bas em t' := by
  first | exact @GlobalTheory.sharpClass_prim_and_iso | exact GlobalTheory.sharpClass_prim_and_iso | (intros; apply GlobalTheory.sharpClass_prim_and_iso <;> assumption)
end
end
