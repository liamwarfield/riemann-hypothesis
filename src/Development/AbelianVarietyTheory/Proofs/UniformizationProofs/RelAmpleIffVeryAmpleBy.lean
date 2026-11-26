module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem relAmple_of_veryAmpleBy {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    {L : LB A.left} (hL : L.IsLB) {N : ℕ} (hN : 1 ≤ N) {M : ℕ} (s : Fin (M + 1) → LB.Sec (pw L N))
    (hA : VeryAmpleBy A.hom (pw L N) s) : RelAmple A L := by
  intro U hU
  obtain ⟨hcov, hs⟩ := hA
  let ψ := (A.hom ⁻¹ᵁ U).ι
  have H : IsPullback ψ (A.hom ∣_ U) A.hom U.ι := (isPullback_morphismRestrict A.hom U).flip
  have : IsAffine U := hU
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have hP := isLB_pw hL N
  have hP' := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
  have h₀ : LBIso (LB.LinComb L (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1)) (pw L N) :=
    LBIso.chartPull (chartPullId _) (chartPullPw L N)
      ⟨_, idIso_isGen (linComb_isLB L hL (K := Fin N) (fun _ => 𝟙 A.left) (fun _ => 1))⟩
  obtain ⟨W, hW⟩ := LBIso.chartPull
    (chartPullSame L (fun _ : Fin N => (A.hom ⁻¹ᵁ U).ι) (fun _ => 𝟙 A.left) (fun _ => 1) ψ
      fun _ => (Category.comp_id _).symm) (chartPullPull (pw L N) ψ ψ rfl) h₀
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := powOver A L U N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (Geo.Tor.mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1
        ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (pw L N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := nonzeroLocus (s i)) le_top le_top
      (UY := nonzeroLocus (M := powOver A L U N) (s' i)) (by rw [loc]; simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) haff)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map ((U.ι.appLE ⊤ ⊤ le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom]
      have e : ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (M := powOver A L U N) (s' i)) le_top).hom.comp
          ((U.ι.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) =
          (ψ.appLE _ _ (loc i).le).hom.comp (cst A.hom (nonzeroLocus (s i))) := by
        ext x
        exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x)) po.w.symm
      exact (congrArg (fun q => MvPolynomial.eval₂Hom q _ p) e).trans
        (MvPolynomial.map_eval₂Hom _ _ _ p).symm
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

theorem relAmple_iff_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), L.IsLB → (RelAmple B L ↔ ∃ d : ℕ, 1 ≤ d ∧ ∃ (n : ℕ) (s : Fin (n + 1) → LB.Sec (pw L d)), VeryAmpleBy B.hom (pw L d) s) := by
  intro R _ B L hL
  refine ⟨fun h => ?_, fun ⟨d, hd, n, s, hs⟩ => relAmple_of_veryAmpleBy hL hd s hs⟩
  obtain ⟨d, hd, n, s, -, hs⟩ := veryAmpleBy_of_relAmple hL h (𝟙 _) (Category.id_comp _) hL
    (LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _) (𝟙 _) rfl) ⟨_, idIso_isGen hL⟩)
  exact ⟨d, hd, n, s, hs⟩

end GlobalTheory.Unif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericSectionBasis

section Calc

variable {F : Type} [CommRing F] {X Y Y' Z : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (scal p (c i)) * (b i).f j

def HasBasis (M : LB Y) (p : Y ⟶ Sp F) (n : ℕ) : Prop :=
  ∃ b : Fin n → LB.Sec M, ∀ s : LB.Sec M, ∃! c : Fin n → F, IsComb p b c s

theorem exists_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) :
    ∃ s : LB.Sec M, IsComb p b c s :=
  ⟨⟨fun j => ∑ i, resTop _ (scal p (c i)) * (b i).f j, fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (scal p (c i)) (b i)).compat j j'⟩, fun _ => rfl⟩

theorem gs_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (r : Z ⟶ Y) (z : Z) (j : M.ι)
    (hz : r z ∈ M.U j) :
    gs r z (M.U j) (∑ i, resTop _ (scal p (c i)) * (b i).f j) =
      ∑ i, cst (r ≫ p) z (c i) * gs r z (M.U j) ((b i).f j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r z _ hz, gs_mul r z _ hz, GlobalTheory.IndivisibleSection.gs_scal p r z _ hz]

theorem HasBasis.transfer {A : LB Y'} {B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (σ : Y' ⟶ Y) (τ : Y ⟶ Y')
    (h₁ : τ ≫ σ = 𝟙 Y) (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p')
    (u : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), A.ι → B.ι → (Z.presheaf.stalk z)ˣ)
    (Rel : LB.Sec A → LB.Sec B → Prop)
    (hRel : ∀ s t, Rel s t → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a →
      (r ≫ σ) z ∈ B.U b → gs r z (A.U a) (s.f a) = (u Z r z a b).val * gs (r ≫ σ) z (B.U b) (t.f b))
    (hl : ∀ t, ∃ s, Rel s t) (hr : ∀ s, ∃ t, Rel s t) (H : HasBasis B p n) : HasBasis A p' n := by
  obtain ⟨β, hβ⟩ := H
  choose β' hβ' using fun i => hl (β i)
  refine ⟨β', fun s => ?_⟩
  obtain ⟨t, ht⟩ := hr s
  have key : ∀ c, IsComb p' β' c s ↔ IsComb p β c t := fun c => by
    constructor
    · intro h j
      refine fn_ext fun y hy => ?_
      obtain ⟨a, ha⟩ := exists_chart hA (τ y)
      have hy' : (τ ≫ σ) y ∈ B.U j := by rw [h₁]; exact hy
      have e := hRel s t ht Y τ y a j ha hy'
      rw [h a, gs_comb p' β' c τ y a ha] at e
      simp only [fun i => hRel _ _ (hβ' i) Y τ y a j ha hy', h₁] at e
      rw [gs_comb p β c (𝟙 Y) y j hy, ← (u Y τ y a j).mul_right_inj, ← e, Finset.mul_sum, ← hp,
        ← Category.assoc, h₁]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    · intro h a
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hB (σ y)
      have hy' : (𝟙 Y' ≫ σ) y ∈ B.U j := hj
      rw [hRel s t ht Y' (𝟙 Y') y a j hy hy', h j, gs_comb p β c _ y j hy', gs_comb p' β' c (𝟙 Y') y a hy,
        Finset.mul_sum, ← hp, Category.assoc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hRel _ _ (hβ' i) Y' (𝟙 Y') y a j hy hy']
      exact mul_left_comm _ _ _
  simp only [key]
  exact hβ t

theorem exists_inv_iso {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : ∃ w' : LB.Iso B A, w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a ⊓ B.U b →
      gm r z ((LB.div A B).U (a, b)) (w'.s (a, b)) = (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹ := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_,
    fun Z r z a b hz => (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (le (a, b)) hz _))⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

theorem HasBasis.of_iso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) {p : Y ⟶ Sp F}
    (H : HasBasis B p n) : HasBasis A p n := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw', e⟩ := exists_inv_iso w hw
  refine H.transfer hA hB (𝟙 Y) (𝟙 Y) (Category.id_comp _) p p (Category.id_comp _)
    (fun Z r z a b => (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹) _ (fun _ _ h => h)
    (fun t => ⟨secOfIso t hw hA hB, fun Z r z a b ha hb => ?_⟩)
    (fun s => ⟨secOfIso s hw' hB hA, fun Z r z a b ha hb => ?_⟩)
  · rw [Category.comp_id] at hb ⊢
    exact GlobalTheory.GenericGenerated.gs_secOfIso w t hw hA hB a b r z ⟨ha, hb⟩
  · rw [Category.comp_id] at hb ⊢
    rw [GlobalTheory.GenericGenerated.gs_secOfIso w' s hw' hB hA b a r z ⟨hb, ha⟩, e Z r z a b ⟨ha, hb⟩, inv_inv,
      Units.inv_mul_cancel_left]

theorem exists_pull_gs {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j →
      gs r z (LB.wchart L φ' j) (s'.f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart s h φ' e
  refine ⟨s', fun Z r z j hz => ?_⟩
  have le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun y hy => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    rw [← e] at this
    exact this
  rw [hs' j le]
  exact (gs_res r z le hz _).trans (gs_pull r h z _ (le hz) _)

theorem HasBasis.pull {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (σ : Y' ⟶ Y) (τ : Y ⟶ Y') (h₁ : τ ≫ σ = 𝟙 Y) (h₂ : σ ≫ τ = 𝟙 Y') (e : ∀ k, σ ≫ φ k = φ' k)
    (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p') (H : HasBasis (LB.LinComb L φ ε) p n) :
    HasBasis (LB.LinComb L φ' ε) p' n := by
  have e' : ∀ k, τ ≫ φ' k = φ k := fun k => by rw [← e, ← Category.assoc, h₁, Category.id_comp]
  have mem : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (b : K → L.ι), (r ≫ σ) z ∈ LB.wchart L φ b →
      r z ∈ LB.wchart L φ' b := fun Z r z b hb => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hb k
    rw [← e]
    exact this
  refine H.transfer (linComb_isLB L hL _ _) (linComb_isLB L hL _ _) σ τ h₁ p p' hp
    (fun Z r z a b => trF φ' ε r z a b) _ (fun _ _ h => h) (fun t => ?_) (fun s => ?_)
  · obtain ⟨s, hs⟩ := exists_pull_gs t σ φ' e
    exact ⟨s, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans
      (congrArg _ (hs Z r z b (mem Z r z b hb)))⟩
  · obtain ⟨t, ht⟩ := exists_pull_gs s τ φ e'
    refine ⟨t, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans (congrArg _ ?_)⟩
    refine Eq.trans ?_ (ht Z (r ≫ σ) z b hb).symm
    rw [Category.assoc, h₂, Category.comp_id]

end Calc

section Field

variable {F : Type} [Field F] (P : PolAV (Spec (CommRingCat.of F))) (k : ℕ)

theorem hasBasis_of_basis (q : Sp F ⟶ Sp F) (hq : q = 𝟙 _) {n : ℕ}
    (β : Fin n → LB.Sec (LPow P.A P.L k (Over.mk q)))
    (hli : LinearIndependent Γ((Over.mk q).left, ⊤) (fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))))
    (hsp : Submodule.span Γ((Over.mk q).left, ⊤)
      (Set.range fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))) = ⊤) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom n := by
  subst hq
  let u : P.A ⟶ Over.mk (𝟙 (Sp F)) := Over.homMk P.A.hom (Category.comp_id _)
  have hw : (snd (Over.mk (𝟙 (Sp F))) P.A).left ≫ P.A.hom = (fst (Over.mk (𝟙 (Sp F))) P.A).left :=
    (Over.w (snd (Over.mk (𝟙 (Sp F))) P.A)).trans
      ((Over.w (fst (Over.mk (𝟙 (Sp F))) P.A)).symm.trans (Category.comp_id _))
  have hu : snd (Over.mk (𝟙 (Sp F))) P.A ≫ u = fst (Over.mk (𝟙 (Sp F))) P.A := Over.OverMorphism.ext hw
  have e₁ : lift u (𝟙 P.A) ≫ snd (Over.mk (𝟙 (Sp F))) P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd (Over.mk (𝟙 (Sp F))) P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  have e₃ : lift u (𝟙 P.A) ≫ fst (Over.mk (𝟙 (Sp F))) P.A = u := lift_fst _ _
  refine HasBasis.pull P.isLB (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 (Sp F))) P.A).left)
    (lift u (𝟙 P.A)).left (snd (Over.mk (𝟙 (Sp F))) P.A).left
    (congrArg CommaMorphism.left e₂) (congrArg CommaMorphism.left e₁) (fun _ => congrArg CommaMorphism.left e₁)
    (fst (Over.mk (𝟙 (Sp F))) P.A).left _ (congrArg CommaMorphism.left e₃) ⟨β, fun s => ?_⟩
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv
  have key : ∀ c : Fin n → F, IsComb (fst (Over.mk (𝟙 (Sp F))) P.A).left β c s ↔
      ∑ i, (show Γ((Over.mk (𝟙 (Sp F))).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) •
        (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk (𝟙 (Sp F)))) = SecM.ofSec P.A s := fun c => by
    rw [Subtype.ext_iff, Submodule.coe_sum, funext_iff]
    refine forall_congr' fun j => ?_
    rw [Finset.sum_apply]
    exact eq_comm
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) = r := funext hc
  refine ⟨c, (key c).2 hr, fun c' hc' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key c').1 hc').trans hr.symm) i

theorem hasBasis_field (hS : SecBaseChangeSt) (hk : 1 ≤ k) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom (k ^ P.g) := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of F)) P k hk (IsLocalRing.closedPoint F)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).left :=
    (Spec (CommRingCat.of F)).topIso.inv
  have ht : t ≫ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).hom = 𝟙 _ := by
    show (Spec (CommRingCat.of F)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of F)).topIso.inv_hom_id
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L k (baseAt t)),
      IsPullSec P.A P.L k (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, hsp⟩ := hb F t b' hb'
  exact hasBasis_of_basis P k _ ht b' hli hsp

end Field

theorem iso_pow {X X' Y : Scheme.{0}} {L : LB X} {M : LB X'}
    (g : Y ⟶ X) (gi : X ⟶ Y) (e₁ : gi ≫ g = 𝟙 X) (e₂ : g ≫ gi = 𝟙 Y) (p : Y ⟶ X')
    (H : LBIso (L.pull g) (M.pull p)) (k : ℤ) :
    LBIso (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => k))
      (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)) := by
  obtain ⟨w, hw⟩ : LBIso L (M.pull (gi ≫ p)) :=
    LBIso.chartPull (chartPullSec L g gi e₁)
      (chartPullSame M (fun _ : PUnit => gi ≫ p) (fun _ => p) (fun _ => 1) gi fun _ => rfl) H
  have H₂ := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => g) (fun _ => k)
  have ep : (fun _ : Fin 1 => g ≫ gi ≫ p) = fun _ => p := by
    funext _; rw [← Category.assoc, e₂, Category.id_comp]
  rw [ep] at H₂
  exact LBIso.symm H₂

theorem exists_secK_basis : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → U.SecK k, (∀ c : Fin (k ^ A.g) → FractionRing R, ∃ s : U.SecK k, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j)) ∧ ∀ s : U.SecK k, ∃! c : Fin (k ^ A.g) → FractionRing R, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) := by
  intro hS R _ _ I D A G _ _ U k hk
  have e₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  have e₂ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.hom_inv_id
  have H₁ := (hasBasis_field A k hS hk).pull A.isLB (φ' := fun _ => U.gen.hom.left) U.gen.hom.left U.gen.inv.left
    e₁ e₂ (fun _ => Category.comp_id _) _ (pullback.snd G.hom (jK R)) (Over.w U.gen.hom)
  obtain ⟨b, hb⟩ := H₁.of_iso (linComb_isLB _ U.LG.isLB _ _) (linComb_isLB _ A.isLB _ _)
    (iso_pow U.gen.hom.left U.gen.inv.left e₁ e₂ (pullback.fst G.hom (jK R)) U.ext k)
  exact ⟨b, fun c => exists_comb _ b c, hb⟩

end GlobalTheory.GenericSectionBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Balanced
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem stalkMap_inj {Y Z : Scheme.{0}} (r : Z ⟶ Y) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (r z)) (Z.presheaf.stalk z)) := inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (r z)) (B := Z.presheaf.stalk z)
  exact FaithfulSMul.algebraMap_injective _ _

theorem surjective_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Surjective (spMap β) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have := surjective_spMap β
  exact Flat.epi_of_flat_of_surjective _

theorem val_descend {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) (r : Z ⟶ Y) [Flat r] [Surjective r]
    (h : ∀ z J, Good L z J → val t r z J = val t' r z J) (y : Y) (J) (hJ : Good L y J) :
    val t (𝟙 Y) y J = val t' (𝟙 Y) y J := by
  have : Epi r := Flat.epi_of_flat_of_surjective r
  obtain ⟨z, rfl⟩ := r.surjective y
  obtain ⟨J', hJ', e⟩ := exists_good L hL z (fun ψ : Y ⟶ X => r ≫ ψ) J
    (fun a b e => congrArg J ((cancel_epi r).1 e)) (fun ψ => hJ ψ)
  have := h z J' hJ'
  rw [val_of t r z J' (fun k => J (𝟙 Y ≫ φ k)) (fun k => by rw [Category.id_comp]; exact e _),
    val_of t' r z J' (fun k => J (𝟙 Y ≫ φ' k)) (fun k => by rw [Category.id_comp]; exact e _)] at this
  have h₁ := hJ.mem φ (𝟙 Y)
  have h₂ := hJ.mem φ' (𝟙 Y)
  have k : ∀ (U : Y.Opens) (_ : r z ∈ U) (a : Γ(Y, U)ˣ),
      (gm r z U a).val = (r.stalkMap z).hom (gm (𝟙 Y) (r z) U a).val := fun U hU a => by
    rw [gm_val r z U hU, gm_val _ (r z) U hU]
    exact (Scheme.Hom.germ_stalkMap_apply r U z hU _).symm
  exact Units.ext (stalkMap_inj r z ((k _ h₁ _).symm.trans ((congrArg Units.val this).trans (k _ h₂ _))))

section Ext
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] (f : F →+* F')
  (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem gtExt_injective (D : DegPre R) : Function.Injective (gtExt D f hf) := fun g g' h => by
  have := epi_spMap f
  have := surjective_spMap f
  have : Flat (spMap f) := inferInstance
  refine gt_ext_val (Over.OverMorphism.ext ((cancel_epi (spMap f)).1 ?_)) fun χ y J hJ => ?_
  · exact ((eq_gtExt_iff f hf g _).1 rfl).1.symm.trans (((eq_gtExt_iff f hf g' _).1 h).1)
  · refine val_descend D.P.isLB (g.s χ) (g'.s χ) (spMap f) (fun z J hJ => ?_) y J hJ
    exact (gtExt_val f hf g χ hJ).symm.trans ((congrArg (fun q => charVal q χ z J) h).trans (gtExt_val f hf g' χ hJ))

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)

theorem act_unique {g g₁ g₂ : GtPtF D.toPre F} (h₁ : E.Act g g₁) (h₂ : E.Act g g₂) : g₁ = g₂ :=
  gt_ext_val (h₁.1.trans h₂.1.symm) fun χ y J hJ => (h₁.2 χ y J hJ).trans (h₂.2 χ y J hJ).symm

theorem act_gtExt {g g' : GtPtF D.toPre F} (h : E.Act g g') : E.Act (gtExt _ f hf g) (gtExt _ f hf g') := by
  refine ⟨by rw [gtExt_b, gtExt_b, h.1, Category.assoc], fun χ z J hJ => ?_⟩
  have c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (g'.s χ)
      (LB.mulGen D.toPre.P.L _ _ _ _ (g.s (E.h χ)) (LB.pullGen D.toPre.P.L _ _ (E.u χ) g.b.left)) :=
    corr_of_val D.toPre.P.isLB fun y J hJ => (h.2 χ y J hJ).trans (Eq.trans (congrArg₂ (· * ·) rfl (by
      rw [val_pull hJ, Category.id_comp])) (val_mul hJ _ _ _).symm)
  refine (gtExt_val f hf g' χ hJ).trans ((val_corr hJ c _).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (gtExt_val f hf g _ hJ).symm ((val_pull hJ _ _ _).trans ?_))))
  rw [gtExt_b]; rfl

end Ext

section Adjoint

theorem adj_add {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (a a' : G ⟶ G) (h : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ a'] L.L)) (m : ℕ) :
    LBIso (cubeLB G ![fst G G ≫ (a * 𝟙 G ^ m), snd G G] L.L) (cubeLB G ![fst G G, snd G G ≫ (a' * 𝟙 G ^ m)] L.L) := by
  have hc := PrimNorm.diff₃_ptCls (T := G ⊗ G) L.isLB ⟨c.t, c.isGen⟩
  have p : ∀ (x y : G ⊗ G ⟶ G) (m : ℕ), PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) (x ^ m) y =
      PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y ^ m := fun x y m =>
    map_pow (MonoidHom.mk' (fun x => PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) x y)
      fun u v => PrimNorm.diff₂_mul_left hc u v y) x m
  have q : ∀ (x : G ⊗ G ⟶ G) (b : G ⟶ G), x ≫ (b * 𝟙 G ^ m) = (x ≫ b) * x ^ m := fun x b =>
    (map_mul (preHom x) _ _).trans (congrArg _ ((map_pow (preHom x) _ _).trans
      (congrArg (· ^ m) (Category.comp_id x))))
  refine (PrimNorm.lbIso_iff L.isLB _ _ _ _).2 ((PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).trans
    (Eq.trans ?_ (PrimNorm.prod_square_id _ _ (PrimNorm.cls L.L)).symm))
  show PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _ = PrimNorm.diff₂ (PrimNorm.ptCls L.L (G ⊗ G)) _ _
  rw [q, q, PrimNorm.diff₂_mul_left hc, PrimNorm.diff₂_mul_right hc, PrimNorm.diff₂_ptCls_adj L.isLB h, p,
    PrimNorm.diff₂_comm (fst G G) (snd G G ^ m), p, PrimNorm.diff₂_comm (snd G G)]

theorem adj_pull {B B' : Scheme.{0}} (f : B' ⟶ B) (G : Over B) [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {L' : LB ((Over.pullback f).obj G).left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hb : LBIso L' (L.pull (pullback.fst G.hom f))) (a a' : G ⟶ G)
    (ha : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a'] L)) :
    LBIso (cubeLB ((Over.pullback f).obj G) ![fst _ _ ≫ (Over.pullback f).map a, snd _ _] L')
      (cubeLB ((Over.pullback f).obj G) ![fst _ _, snd _ _ ≫ (Over.pullback f).map a'] L') := by
  have h := isGrpPullback_pullback G f
  let G' := (Over.pullback f).obj G
  let φ : G'.left ⟶ G.left := pullback.fst G.hom f
  have pa : ∀ (w : G ⟶ G) {T : Over B'} (x : T ⟶ G'),
      pushPt h.1.w (x ≫ (Over.pullback f).map w) = pushPt h.1.w x ≫ w := fun w T x =>
    Over.OverMorphism.ext (by
      have hw : ((Over.pullback f).map w).left ≫ φ = φ ≫ w.left := pullback.lift_fst _ _ _
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have hB : (L.pull φ).IsLB := pull_isLB hL φ
  have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ (Over.pullback f).map a, snd G' G'] (L.pull φ))
      (cubeLB G' ![fst G' G', snd G' G' ≫ (Over.pullback f).map a'] (L.pull φ)) := by
    let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
    refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) ha
    · fin_cases i
      · exact (pa _ _).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
      (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end Adjoint

theorem exists_add_injective {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X) :
    ∃ m : ℕ, (Function.Injective fun x => h x + m • x) ∧ Function.Injective fun x => h' x + m • x := by
  have key : ∀ h : X →+ X, {m : ℕ | ¬ Function.Injective fun x => h x + m • x}.Finite := fun h => by
    let f : Module.End ℤ X := h.toIntLinearMap
    have fin : (f.charpoly.rootSet ℤ).Finite := Polynomial.rootSet_finite _ _
    refine Set.Finite.subset (fin.preimage (f := fun m : ℕ => -(m : ℤ)) (fun a _ b _ e => by simpa using e)) ?_
    intro m hm
    simp only [Function.Injective, Set.mem_setOf_eq, not_forall] at hm
    obtain ⟨x, y, e, hxy⟩ := hm
    have ev : f.HasEigenvector (-(m : ℤ)) (x - y) := by
      refine ⟨Module.End.mem_eigenspace_iff.2 ?_, sub_ne_zero.2 hxy⟩
      show h (x - y) = _
      rw [map_sub, neg_smul, natCast_zsmul, smul_sub]
      linear_combination (norm := abel) e
    have := Module.End.aeval_apply_of_hasEigenvector (p := f.charpoly) ev
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at this
    refine (Polynomial.mem_rootSet).2 ⟨f.charpoly_monic.ne_zero, ?_⟩
    simpa [sub_ne_zero.2 hxy] using this.symm
  obtain ⟨m, hm⟩ := ((key h).union (key h')).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hm
  exact ⟨m, hm⟩

end GlobalTheory.Balanced
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MapUniq

variable {X X' : Scheme.{0}}

theorem hom_ext_of_gs {I : Type} (D : I → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (φ ψ : X' ⟶ X) (hm : ∀ i z, φ z ∈ D i → ψ z ∈ D i)
    (h : ∀ i z, φ z ∈ D i → ∀ a : Γ(X, D i), gs φ z _ a = gs ψ z _ a) : φ = ψ := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ z ∈ ⨆ i, D i by rw [hc]; trivial)
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ (φ ⁻¹ᵁ D i : Set X') from hi) (φ ⁻¹ᵁ D i).isOpen
  have e₁ : V ≤ φ ⁻¹ᵁ D i := hle
  have e₂ : V ≤ ψ ⁻¹ᵁ D i := fun y hy => hm i y (e₁ hy)
  have e : φ.appLE (D i) V e₁ = ψ.appLE (D i) V e₂ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => fn_ext fun y hy => ?_)
    have k : ∀ (χ : X' ⟶ X) (e : V ≤ χ ⁻¹ᵁ D i), gs (𝟙 X') y V ((χ.appLE (D i) V e).hom a) = gs χ y _ a :=
      fun χ e => ((gs_res (𝟙 X') y e hy _).trans (gs_pull (𝟙 X') χ y _ (e hy) a)).trans (by rw [Category.id_comp])
    rw [k, k]
    exact h i y (e₁ hy) a
  refine ⟨V, hzV, ?_⟩
  have hV' : IsAffineOpen V := hV
  rw [← cancel_epi hV'.isoSpec.inv, ← Category.assoc, ← Category.assoc, hV'.isoSpec_inv_ι,
    ← (hD i).SpecMap_appLE_fromSpec φ hV' e₁, ← (hD i).SpecMap_appLE_fromSpec ψ hV' e₂, e]

theorem gs_cst {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (W : X.Opens)
    (h : φ z ∈ W) (c : R) :
    gs φ z W (AbLaw.cst f W c) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  (gs_res φ z le_top h _).trans (gs_pull φ f z ⊤ trivial _)

theorem hom_eq_of_pull_sections : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ ψ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)) (w' : LB.Iso H' (H.pull ψ)), H'.IsLB → φ ≫ f = ψ ≫ f → w.IsGen → w'.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (ψ) z ∈ (H).U k → z ∈ (H').U k' → gs (ψ) z _ ((s j).f k) = (Geo.Tor.gw (w') (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → φ = ψ := by
  intro R _ X f H n s hH hs X' H' s' φ ψ w w' hH' hf _ _ hφ hψ
  choose r hr hsurj using fun i => (hs.2 i).2
  have mem : ∀ (χ : X' ⟶ X) (u : LB.Iso H' (H.pull χ)),
      (∀ j z (k : H.ι) (k' : H'.ι), χ z ∈ H.U k → z ∈ H'.U k' →
        gs χ z _ ((s j).f k) = (Geo.Tor.gw u (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k')) →
      ∀ i z k', z ∈ H'.U k' → (χ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs (𝟙 X') z _ ((s' i).f k'))) ∧
        (χ z ∈ nonzeroLocus (s i) → ∀ j, gs (𝟙 X') z _ ((s' j).f k') =
          gs χ z _ (r i j) * gs (𝟙 X') z _ ((s' i).f k')) := by
    intro χ u hu i z k' hk'
    obtain ⟨k, hk⟩ := exists_chart hH (χ z)
    refine ⟨?_, fun hz j => ?_⟩
    · rw [AmpleSpan.mem_nonzeroLocus_iff_gs (s i) χ z hk, hu i z k k' hk hk', Units.isUnit_units_mul]
    · have e := AmpleSpan.IsRatio.gs (s := s j) (t := s i) (r := r i j) (hr i j) χ z hz hk
      rw [hu i z k k' hk hk', hu j z k k' hk hk', mul_left_comm] at e
      exact (Units.mul_right_inj _).1 e
  have hm : ∀ i z, φ z ∈ nonzeroLocus (s i) → ψ z ∈ nonzeroLocus (s i) := fun i z hz => by
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact (mem ψ w' hψ i z k' hk').1.2 ((mem φ w hφ i z k' hk').1.1 hz)
  refine hom_ext_of_gs (fun i => nonzeroLocus (s i)) (fun i => (hs.2 i).1) hs.1 φ ψ hm fun i z hz a => ?_
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have hz' := hm i z hz
  have hrr : ∀ j, gs φ z _ (r i j) = gs ψ z _ (r i j) := fun j =>
    ((mem φ w hφ i z k' hk').1.1 hz).mul_right_cancel
      (((mem φ w hφ i z k' hk').2 hz j).symm.trans ((mem ψ w' hψ i z k' hk').2 hz' j))
  obtain ⟨p, rfl⟩ := hsurj i a
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.eval₂Hom_C, gs_cst f φ z _ hz, gs_cst f ψ z _ hz', hf]
  | add p q hp hq => rw [map_add (f := _), gs_add φ z _ hz, gs_add ψ z _ hz', hp, hq]
  | mul_X p j hp => rw [map_mul, MvPolynomial.eval₂Hom_X', gs_mul φ z _ hz, gs_mul ψ z _ hz', hp, hrr]

end GlobalTheory.MapUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.CubicalPackage

theorem surjective_appTop_of_injective {X S P S' : Scheme.{0}} {p : X ⟶ S} {q : P ⟶ S'} {d : P ⟶ X} {f : S' ⟶ S}
    (w : d ≫ p = q ≫ f) {e : S ⟶ X} {e' : S' ⟶ P} (he' : e' ≫ q = 𝟙 _) (hee : e' ≫ d = f ≫ e)
    (hd : Function.Injective d.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective p.appTop.hom := by
  intro a
  obtain ⟨b, hb⟩ := hq (d.appTop.hom a)
  have c : ∀ {A B C : Scheme.{0}} (g : A ⟶ B) (h : B ⟶ C) (x : Γ(C, ⊤)),
      g.appTop.hom (h.appTop.hom x) = (g ≫ h).appTop.hom x := fun g h x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  refine ⟨e.appTop.hom a, hd ?_⟩
  rw [c, w, ← c, c f e, ← hee, ← c, ← hb, c e' q, he', Scheme.Hom.id_appTop]
  rfl

variable {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {A : Over (Spec (CommRingCat.of K))} [GrpObj A] [IsCommMonObj A] {F : A.left ⟶ G.left}

theorem surjective_cube_of_generic [Flat G.hom] (gp : IsGrpPullback A G (etaK V K) F)
    (h : Function.Surjective (G3 A).hom.appTop.hom) : Function.Surjective (G3 G).hom.appTop.hom := by
  have hp := gp.1
  have : Flat (G3 G).hom := by
    show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
    infer_instance
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd (G3 G).hom (etaK V K))
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
  have hx : ∀ i, (x i).left ≫ F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
  let l : P ⟶ G3 A := lift (x 0) (lift (x 1) (x 2))
  have lx : ∀ i, l ≫ x3 A i = x i := fun i => by fin_cases i <;> simp [l, x3]
  have f3 : ∀ i, (cubeMapOf gp).F3 ≫ (x3 G i).left = (x3 A i).left ≫ F := cubeMap_comp_proj_three (cubeMapOf gp)
  have hl : l.left ≫ (cubeMapOf gp).F3 = pullback.fst (G3 G).hom (etaK V K) := hom_ext_triple _ fun i => by
    rw [Category.assoc, f3, ← Category.assoc, ← Over.comp_left, lx, hx]
  have inj : Function.Injective (l.left ≫ (cubeMapOf gp).F3).appTop.hom := by
    rw [hl]
    exact Exist.CubicalExtension.app_injective_generic (IsPullback.of_hasPullback _ _) ⊤
  refine surjective_appTop_of_injective (d := (cubeMapOf gp).F3) (f := etaK V K)
    (Over.w (lift (pushPt hp.w (x3 A 0)) (lift (pushPt hp.w (x3 A 1)) (pushPt hp.w (x3 A 2)))))
    (e := eSec (G3 G)) (e' := eSec (G3 A)) (Over.w η[G3 A]) ?_ ?_ h
  · rw [CubeExtension.eSec_three, CubeExtension.eSec_three]
    refine hom_ext_triple _ fun i => ?_
    have a : ∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B],
        (lift (1 : 𝟙_ (Over S) ⟶ B) (lift (1 : 𝟙_ (Over S) ⟶ B) (1 : 𝟙_ (Over S) ⟶ B))).left ≫ (x3 B i).left =
          eSec B := fun B _ _ => by
      rw [← Over.comp_left, eSec]
      fin_cases i <;> simp [x3, Hom.one_def]
    rw [Category.assoc, f3, ← Category.assoc, a, Category.assoc, a]
    exact (cubeMapOf gp).e_comm
  · rw [Scheme.Hom.comp_appTop] at inj
    exact Function.Injective.of_comp (f := l.left.appTop.hom) inj

theorem exists_package : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (L : RigLB G), LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V))) → ∃ P : CP G, P.L = L) := by
  intro laws V _ _ _ hV A G _ _ hG eA hA L h₁
  have := hV.1
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := A.isAb.comm
  have : IsMonHom eA.symm.hom := inferInstanceAs (IsMonHom eA.inv)
  have gp : IsGrpPullback A.A G (jK V) (eA.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso eA.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  have hi : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, eA.inv_hom_id, Over.id_left]
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨w, hw⟩ : LBIso A.L (L.L.pull (eA.inv.left ≫ pullback.fst G.hom (jK V))) :=
    LBIso.chartPull (chartPullSec A.L _ eA.inv.left hi) (chartPullSame L.L _ _ _ eA.inv.left fun _ => rfl) h₁
  obtain ⟨c⟩ := (laws.cube _ A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  obtain ⟨c'⟩ := PolExtension.nonempty_cubical laws.cubicalExtends gp L c w hw
  obtain ⟨s, hs, hs'⟩ := PolExtension.exists_symmetry gp L.isLB A.isLB A.sym w hw
  exact ⟨CP.ofSurjective (surjective_cube_of_generic gp (surjective_cube laws.globalFns A.isAb)) L c' s hs hs', rfl⟩

end GlobalTheory.CubicalPackage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedSymBoxLB
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxSymLoc

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res)
open ReciprocityTheory.ChartRestriction.G.Out.LBxP

variable {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

lemma gU_pull_box_g (F : J → (X' ⟶ X)) (a : Y ⟶ X') (i j : J → L.ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.LinComb L F (fun _ => 1)).U i ⊓ (LB.LinComb L F (fun _ => 1)).U j))
    (hy' : ∀ m, y ∈ (a ≫ F m) ⁻¹ᵁ (L.U (i m) ⊓ L.U (j m))) :
    gU y hy (pullU a _ ((LB.LinComb L F (fun _ => 1)).g i j)) =
      ∏ m, gU y (hy' m) (pullU (a ≫ F m) _ (L.g (i m) (j m))) := by
  refine (gU_pullU a _ y hy _).trans ?_
  have e := gU_lcg L F (fun _ => 1) i j (a.base y) hy
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) e).trans ?_
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun m _ => ?_)
  refine (congrArg (Units.map (RingHom.toMonoidHom (a.stalkMap y).hom)) (zpow_one _)).trans ?_
  refine (gU_pullU a _ y _ _).symm.trans ?_
  exact gU_pullU_comp a (F m) _ _ y _ _

lemma isGen_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  intro i j
  apply unit_ext
  intro y hy
  have hm : ∀ m, y ∈ (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => i k m) ⊓
      (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => j k m) :=
    fun m => ⟨GeneratorPullback.box_le L F φ i m hy.1, GeneratorPullback.box_le L F φ j m hy.2⟩
  have hk : ∀ k m, y ∈ (φ k ≫ F m) ⁻¹ᵁ (L.U (i k m) ⊓ L.U (j k m)) := fun k m =>
    ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 k) m, Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 k) m⟩
  have hb : ∀ (c : K → J → L.ι) (hc : y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ c),
      gU y hc ((GeneratorPullback.boxGen L F φ ε t).s c) =
        ∏ m, gU y (GeneratorPullback.box_le L F φ c m hc) ((t m).s (fun k _ => c k m)) := fun c hc =>
    (map_prod (gU y hc) _ _).trans (Finset.prod_congr rfl fun m _ => gU_res _ _ _ _)
  have Ht : ∀ m, gU y (GeneratorPullback.box_le L F φ i m hy.1) ((t m).s (fun k _ => i k m)) =
      (∏ k, gU y (hk k m) (pullU (φ k ≫ F m) _ (L.g (i k m) (j k m))) ^ ε k) *
        gU y (GeneratorPullback.box_le L F φ j m hy.2) ((t m).s (fun k _ => j k m)) := by
    intro m
    refine (gU_res (inf_le_left : (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => i k m) ⊓
      (LB.LinComb (L.pull (F m)) φ ε).U (fun k _ => j k m) ≤ _) y (hm m) _).symm.trans ?_
    refine (congrArg (gU y (hm m)) (ht m (fun k _ => i k m) (fun k _ => j k m))).trans ?_
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gU_res _ _ _ _))
    refine (gU_lcg (L.pull (F m)) φ ε _ _ y (hm m)).trans ?_
    refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
    exact gU_pull_g L (F m) (φ k) _ _ y _ (hk k m)
  have hg : gU y hy ((LB.LinComb (LB.LinComb L F (fun _ => 1)) φ ε).g i j) =
      ∏ m, ∏ k, gU y (hk k m) (pullU (φ k ≫ F m) _ (L.g (i k m) (j k m))) ^ ε k := by
    refine (gU_lcg (LB.LinComb L F (fun _ => 1)) φ ε i j y hy).trans ?_
    refine Eq.trans ?_ Finset.prod_comm
    refine Finset.prod_congr rfl fun k _ => ?_
    refine Eq.trans ?_ (Finset.prod_zpow _ _ _).symm
    exact congrArg (· ^ ε k) (gU_pull_box_g L F (φ k) (i k) (j k) y _ (hk k))
  refine ((gU_res _ y hy _).trans (hb i hy.1)).trans ?_
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) hg
    ((gU_res _ y hy _).trans (hb j hy.2)))).symm
  exact (Finset.prod_congr rfl fun m _ => Ht m).trans Finset.prod_mul_distrib

lemma exists_restrict {S : Scheme.{0}} {A B : Over S} (f : A ⟶ B) (U : S.Opens) :
    ∃ ρ : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      ρ ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ f.left := by
  refine ⟨f.left.resLE _ _ ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  rw [← Scheme.Hom.comp_preimage, Over.w]

end GlobalTheory.BoxSymLoc

namespace GlobalTheory

open BoxSymLoc ReciprocityTheory.ChartRestriction.G.Out.LBxP

theorem rigidified_sym_boxLB (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (_hL : L.IsLB) :
    (Rigidified G L → Rigidified G' (boxLB L p.pr)) ∧
      (Out.Sym G L → Out.Sym G' (boxLB L p.pr)) := by
  constructor
  · rintro ⟨t, ht⟩
    have he : ∀ i : Fin j, ∀ _k : PUnit, eSec G' ≫ (p.pr i).left = 𝟙 _ ≫ eSec G := by
      intro i _
      have := p.hom i
      rw [Category.id_comp, eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) (fun _ => eSec G') (fun _ => 1)
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (𝟙 _) (fun _ => eSec G) _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩
  · intro h s
    obtain ⟨U, hs, t, ht⟩ := h s
    refine ⟨U, hs, ?_⟩
    choose ρ hρ using fun i => exists_restrict (p.pr i) U
    have he : ∀ i : Fin j, ∀ k : Fin 2,
        (![(G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left, (G'.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G'.hom ⁻¹ᵁ U).toScheme ⟶ G'.left)) k ≫ (p.pr i).left =
        ρ i ≫ (![(G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ U).ι] :
          Fin 2 → ((G.hom ⁻¹ᵁ U).toScheme ⟶ G.left)) k := by
      intro i k
      have := p.hom i
      fin_cases k
      · have h0 : (GrpObj.inv : G' ⟶ G').left ≫ (p.pr i).left =
            (p.pr i).left ≫ (GrpObj.inv : G ⟶ G).left := inv_pr p i 0
        show ((G'.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G' ⟶ G').left) ≫ (p.pr i).left =
          ρ i ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
        rw [Category.assoc, h0, ← Category.assoc, ← hρ i, Category.assoc]
      · exact (hρ i).symm
    exact ⟨GeneratorPullback.boxGen L (fun i => (p.pr i).left) _ _
      (fun i => GeneratorPullback.pullAlong L (p.pr i).left (ρ i) _ _ _ (he i) t),
      isGen_boxGen L _ _ _ _ fun i => isGen_pullAlong L _ _ _ _ _ (he i) t ht⟩

end GlobalTheory
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

variable {S : Scheme.{0}}

def powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) : PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : IsCommMonObj A' := PowGrp.comm_of_isPowGrp p P.isAb.comm
  { A := A'
    isAb := (PowGrp.powers S A' P.A j p).2.2.2.1 P.isAb
    g := j * P.g
    smoothDim := (PowGrp.powers S A' P.A j p).2.2.1 P.g P.smoothDim
    L := boxLB P.L p.pr
    isLB := LB.isLB_linComb P.isLB _ _
    rigid := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).1 P.rigid
    sym := (rigidified_sym_boxLB S A' P.A j p P.L P.isLB).2 P.sym
    ample := T.relAmple_externalTensorPower_groupPower S A' P.A j p P.L P.isLB P.ample
    ktriv := T.kTriv_external_tensor_power_lineBundle S A' P.A j p P.L P.isLB P.ktriv }

def isPowPolAV_powPolOf (P : PolAV S) {j : ℕ} (A' : Over S) [GrpObj A'] (p : IsPowGrp A' P.A j) :
    IsPowPolAV (powPolOf P A' p) P j where
  toIsPowGrp := p
  w := CubePf.idIsoL (boxLB P.L p.pr)
  w_gen := CubePf.idIsoL_isGen (LB.isLB_linComb P.isLB _ _)

def powPol (P : PolAV S) (j : ℕ) : PolAV S :=
  powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

def isPowPolAV_powPol (P : PolAV S) (j : ℕ) : IsPowPolAV (powPol P j) P j :=
  isPowPolAV_powPolOf P (powObj P.A j) (powIsPowGrp P.A j)

theorem exists_powPolAV : ∀ (S : Scheme.{0}) (P : PolAV S) (j : ℕ),
    ∃ (P' : PolAV S) (_ : IsPowPolAV P' P j), P'.g = j * P.g :=
  fun _ P j => ⟨powPol P j, isPowPolAV_powPol P j, rfl⟩

end GlobalTheory
end
end
