module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasTorusWeightIffTorusEquivariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPullbackMulGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPullbackMulGenerator
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_chartPull_g {Y Y' Z : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (r : Z ⟶ Y') (z : Z) (i j : A'.ι) (hi : r z ∈ A'.U i) (hj : r z ∈ A'.U j) :
    gm r z (A'.U i ⊓ A'.U j) (A'.g i j) =
      gm (r ≫ h) z (A.U (a.idx i) ⊓ A.U (a.idx j)) (A.g (a.idx i) (a.idx j)) := by
  have le : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (a.idx i) ⊓ A.U (a.idx j)) := fun y hy => ⟨a.le i hy.1, a.le j hy.2⟩
  have e : A'.g i j = res le (pullU h _ (A.g (a.idx i) (a.idx j))) := unit_ext fun y hy =>
    (a.g y i j hy.1 hy.2).trans ((gm_res (𝟙 Y') y le hy _).trans
      ((gm_pull (𝟙 Y') h y _ (le hy) _).trans (by rw [Category.id_comp]))).symm
  have hm : r z ∈ A'.U i ⊓ A'.U j := ⟨hi, hj⟩
  rw [e]
  exact (gm_res r z le hm _).trans (gm_pull r h z _ (le hm) _)

theorem exists_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF b
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec b Φ.D.q.left t ht)
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l y hy => Set.mem_iInter.2 fun _ => c.le l hy
  refine ⟨⟨fun l => (Φ.G.left.presheaf.map (homOfLE (le l)).op).hom (s.f (fun _ => c.idx l)),
    fun l l' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ l hl e => ?_⟩
  · refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l) hy.1 _)).trans
      ((sec_trans s (𝟙 _) y (le l hy.1) (le l' hy.2)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l') hy.2 _)))).symm))
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
    have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hy.1 hy.2
    have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hy.1, hy.2⟩ (Φ.N₀.g l l')
    refine Eq.trans ?_ (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).symm
    refine Eq.trans ?_ (map_pow _ _ _).symm
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rw [Category.assoc]
    rfl
  · refine (gs_res r z (le l) hl _).trans ?_
    rw [← sval_pullMulSec b Φ.D.q.left t ht r z hJ, ← hs Z r z J hJ]
    exact (sval_of s r z J (fun _ => c.idx l) (fun _ => e)).symm

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPullbackMulGeneratorStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullback_mul_generator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  first | exact @GlobalTheory.ZH.UFib.exists_red | exact GlobalTheory.ZH.UFib.exists_red | (intros; apply GlobalTheory.ZH.UFib.exists_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrincipalPolarisationAbelianFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrincipalPolarisationAbelianFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

theorem lbIso_of_refines {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K']
    [Fintype K''] {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') {ψ : K'' → (Y ⟶ X)} {δ : K'' → ℤ}
    (t : LB.Gen (LB.LinComb L ψ δ)) (ht : t.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (ψ k) ^ δ k) * ∏ k, f (φ k) ^ ε k = ∏ k, f (φ' k) ^ ε' k) : LBIso M M' := by
  refine (h'.div h).exists_gen hL (fun U _ f => ?_) t ht
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [← hF U f, mul_inv_cancel_right]

theorem refines_npw {X : Scheme.{0}} (L : LB X) (N : ℕ) :
    Refines (npw L N) L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ)) := by
  refine ⟨fun i _ => i, fun i y hy => Set.mem_iInter.2 fun _ => hy, fun Z r z i j _ _ => ?_⟩
  refine (map_pow _ _ _).trans (Eq.symm ((Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)))
  rw [Category.comp_id]
  rfl

theorem npw_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (N : ℕ) :
    LBIso (npw L N) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ))) :=
  lbIso_of_refines hL (refines_npw L N) (refines_self _ _) _ isGen_one fun U _ f => by
    rw [Fintype.prod_empty, _root_.one_mul]

theorem lbIso_drop {k : Type} [Field k] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ Sp k) (a b : Sp k ⟶ X)
    (u v : Y ⟶ X) (φ : Fin 4 → (Y ⟶ X)) (h₀ : φ 0 = u) (h₁ : φ 1 = p ≫ a) (h₂ : φ 2 = v) (h₃ : φ 3 = p ≫ b) :
    LBIso (LB.LinComb L φ Oε) (LB.LinComb L (K := Fin 2) ![u, v] ![1, -1]) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := k) L hL (K := Fin 2) ![a, b] ![1, -1]
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ (DVR.pullGen_isGen _ _ _ e he p) fun U _ f => ?_
  rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, h₀, h₁, h₂, h₃]
  change f (p ≫ a) ^ (1 : ℤ) * f (p ≫ b) ^ (-1 : ℤ) *
    (f u ^ (1 : ℤ) * f (p ≫ a) ^ (-1 : ℤ) * f v ^ (-1 : ℤ) * f (p ≫ b) ^ (1 : ℤ)) = f u ^ (1 : ℤ) * f v ^ (-1 : ℤ)
  simp only [zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_pol : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  rintro hB k _ Φ R _ _ D s π hπ xe hO N ⟨cp⟩
  obtain ⟨P', g, hg, hdim, hm, t, ht⟩ := hB _ _ s D.P
  have gp : IsGrpPullback P'.A D.P.A s g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨β, hβ, hβπ⟩ := grpPullback_iso hπ gp
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  have hL := D.P.isLB
  have hL' := P'.isLB
  have key : ∀ {K : Type} [Fintype K] (φ' : K → (Φ.E.B.left ⟶ P'.A.left)) (φ : K → (Φ.E.B.left ⟶ D.P.A.left))
      (ε : K → ℤ), (∀ a, φ a = φ' a ≫ g) → LBIso (LB.LinComb D.P.L φ ε) (LB.LinComb P'.L φ' ε) := by
    intro K _ φ' φ ε h
    obtain rfl : φ = fun a => φ' a ≫ g := funext h
    exact (iso_linComb ((isGen_iff w).1 hw) φ' ε).symm
  have hc : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, (s ≫ x.left) ≫ D.P.A.hom = 𝟙 _ ≫ s := fun x => by
    rw [Category.assoc, Over.w x, Category.id_comp]
    exact Category.comp_id _
  let c : Φ.E.X → (baseOver (Sp k) ⟶ P'.A) := fun χ =>
    Over.homMk (hg.lift (s ≫ (D.c (xe χ)).left) (𝟙 _) (hc _)) (hg.lift_snd _ _ _)
  have hcg : ∀ χ, (c χ).left ≫ g = s ≫ (D.c (xe χ)).left := fun χ => hg.lift_fst _ _ _
  have hu : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, π ≫ (toUnit D.P.A ≫ x).left = Φ.E.B.hom ≫ s ≫ x.left := fun x => by
    rw [← Category.assoc, ← hπ.1.w, Category.assoc]
    rfl
  refine ⟨⟨P', β, hβ, c, ?_, fun χ => ?_⟩, hdim⟩
  · have h₁ : LBIso Φ.N₀ (LB.LinComb D.P.L (K := PUnit) (fun _ => π) (fun _ => (N : ℤ))) :=
      LBIso.chartPull cp (chartPullSame _ _ _ _ π fun _ => (Category.comp_id _).symm) (npw_iso hL N)
    have h₂ := key (K := PUnit) (fun _ => β.hom.left) (fun _ => π) (fun _ => (N : ℤ)) fun _ => hβπ.symm
    have h₃ : LBIso (LB.LinComb P'.L (K := PUnit) (fun _ => β.hom.left) (fun _ => (N : ℤ)))
        ((lbPow P'.L N).pull β.hom.left) :=
      LBIso.chartPull (chartPullId _) (chartPullOut P'.L _ _ β.hom.left _ fun _ => (Category.comp_id _).symm)
        (exists_iso hL' rfl _)
    exact LBIso.trans Φ.isLB (DVR.linComb_isLB _ hL _ _) (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₁
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
        (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₂ h₃)
  · let q : Φ.E.B ⟶ baseOver (Sp k) := Over.homMk Φ.E.B.hom (Category.comp_id _)
    have e₀ : π ≫ D.Oφ (𝟙 D.P.A) (xe χ) 0 = (β.hom * (q ≫ c χ)).left ≫ g := by
      let ρ : Over.mk (Φ.E.B.hom ≫ s) ⟶ D.P.A := Over.homMk π hπ.1.w
      refine Eq.trans ?_ (gp.2 Φ.E.B β.hom (q ≫ c χ) (ρ ≫ 𝟙 _) (ρ ≫ toUnit _ ≫ D.c (xe χ))
        ((Category.comp_id _).trans hβπ.symm) ?_)
      · exact congrArg (fun f => f.left) (MonObj.comp_mul ρ (𝟙 _) (toUnit _ ≫ D.c (xe χ)))
      · refine (hu _).trans ?_
        rw [← hcg]
        exact (Category.assoc _ _ _).symm
    have h₁ := lbIso_drop hL Φ.E.B.hom (s ≫ (D.c (xe χ)).left) (s ≫ (η[D.P.A]).left) _ π
      (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) e₀ (hu _) (Category.comp_id _) (hu _)
    have h₂ := key (K := Fin 2) ![(β.hom * (q ≫ c χ)).left, β.hom.left] ![(β.hom * (q ≫ c χ)).left ≫ g, π] ![1, -1]
      (fun a => by
        fin_cases a
        · rfl
        · exact hβπ.symm)
    exact LBIso.trans (Φ.E.O χ).isLB (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) (hO χ)
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) h₁ h₂)

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrincipalPolarisationAbelianFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarisation_abelianFibre : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  first | exact @GlobalTheory.ZH.UFib.exists_pol | exact GlobalTheory.ZH.UFib.exists_pol | (intros; apply GlobalTheory.ZH.UFib.exists_pol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPurePullbackSectionMulWeightGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPurePullbackSectionMulWeightGenerator
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem pure_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ (b : LB.Sec (LB.LinComb L ψ ε)) (φ : (Φ.H 1).Sec), UFib.Red Φ c t b φ → Φ.Pure α φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ α hw b φ hr
  rintro χ ⟨l, hl⟩
  by_contra hne
  refine hl ((GlobalTheory.T.hasTorusWeight_iff_torusEquivariant k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).1 ?_ χ hne)
  intro Z τ g z hz
  have := Φ.D.q_hom
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
    (fun _ _ _ => rfl) (fun _ => c.le l hz)
  have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
    congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
  have h₁ := hr _ g.left z J hJ l hz (e ())
  have h₂ := hr _ ((τ ≫ Φ.D.i) * g).left z J hJ l
    (GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz)
    (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
  rw [hq, hw Z τ g z J hJ, Units.val_mul, mul_left_comm, ← h₁] at h₂
  exact h₂

end GlobalTheory.ZH.UFib
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPurePullbackSectionMulWeightGeneratorStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPure_pullbackSection_mul_weightGenerator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ (b : LB.Sec (LB.LinComb L ψ ε)) (φ : (Φ.H 1).Sec), UFib.Red Φ c t b φ → Φ.Pure α φ := by
  first | exact @GlobalTheory.ZH.UFib.pure_of_red | exact GlobalTheory.ZH.UFib.pure_of_red | (intros; apply GlobalTheory.ZH.UFib.pure_of_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOfRefine
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_sec_compat {Y Z : Scheme.{0}} {M : LB Y} (φ : M.Sec) (r : Z ⟶ Y) (z : Z) {l l' : M.ι}
    (hl : r z ∈ M.U l) (hl' : r z ∈ M.U l') :
    gs r z (M.U l) (φ.f l) = (gm r z (M.U l ⊓ M.U l') (M.g l l')).val * gs r z (M.U l') (φ.f l') := by
  have hm : r z ∈ M.U l ⊓ M.U l' := ⟨hl, hl'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (φ.compat l l')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem exists_sec_of_refine : ∀ (Y : Scheme.{0}) (M A : LB Y), M.IsLB → A.IsLB →
    ∀ (c : ChartPull M A (𝟙 Y)) (φ : M.Sec), ∃ s : A.Sec, ∀ (l : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ M.U l → gs r z (M.U l) (φ.f l) = gs r z (A.U (c.idx l)) (s.f (c.idx l)) := by
  intro Y M A hM hA c φ
  have cle : ∀ l (y : Y), y ∈ M.U l → y ∈ A.U (c.idx l) := fun l y hy => c.le l hy
  have glue : ∀ i : A.ι, ∃ a : Γ(Y, A.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : M.ι),
      r z ∈ A.U i → r z ∈ M.U l →
      gs r z _ a = (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) := by
    intro i
    let W : M.ι → Y.Opens := fun l => A.U i ⊓ M.U l
    have hW : ∀ l, W l ≤ A.U i ⊓ A.U (c.idx l) := fun l y hy => ⟨hy.1, cle l y hy.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) l, r z ∈ W l →
        gs r z (W l) (u l) =
          (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) :=
      ⟨fun l => (Y.presheaf.map (homOfLE (hW l)).op).hom (A.g i (c.idx l)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W l ≤ M.U l)).op).hom (φ.f l), fun Z r z l hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (hW l hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (A.U i)
      (fun l => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨l, hl⟩ := exists_chart hM y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hy, hl⟩) u
      (fun l l' => fn_ext (V := W l ⊓ W l') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y l hy.1, hu _ _ y l' hy.2, gs_sec_compat φ (𝟙 Y) y hy.1.2 hy.2.2, c.g y l l' hy.1.2 hy.2.2,
          ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hA (𝟙 Y) y hy.1.1 (cle l y hy.1.2) (cle l' y hy.2.2)])
    refine ⟨a, fun Z r z l h₁ h₂ => ?_⟩
    have hz : r z ∈ W l := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W l)) (ha l)).trans (hu Z r z l hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun l Z r z hl => ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
    rw [ha j _ (𝟙 Y) y l hy.1 hl, ha j' _ (𝟙 Y) y l hy.2 hl,
      ← gm_cocycle hA (𝟙 Y) y hy.1 hy.2 (cle l y hl), Units.val_mul, _root_.mul_assoc]
  · have m := cle l _ hl
    refine Eq.symm ((ha _ Z r z l m hl).trans ?_)
    rw [gm_self hA r z m, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAppEqOfHasWtZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val S X Z τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

theorem gs_id_appLE {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (z : Z) (f : Γ(X, U)) :
    gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom f) = gs r z U f := by
  have e := gs_pull (𝟙 Z) r z U (h trivial) f
  rw [Category.id_comp] at e
  exact (gs_res (𝟙 Z) z h trivial _).trans e

theorem exists_app_eq_of_hasWt_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (E : SplitExt (Sp k)) (G : Over (Sp k)) [GrpObj G] (D : E.GtDatum G) (W : E.B.left.Opens) (f : Γ(G.left, D.q.left ⁻¹ᵁ W)), UFib.HasWt D.i (D.q.left ⁻¹ᵁ W) f 0 → ∃ a : Γ(E.B.left, W), (D.q.left.app W).hom a = f := by
  intro k _ _ E G _ D W f hf
  have := D.q_affine
  refine (invariant_functions_descend _ G E.B _ D.q D.i D.q_hom D.i_hom D.q_flat D.q_surjective inferInstance
    D.isKernel W).2.2 f fun Z t g h₁ h₂ => fn_ext fun z _ => ?_
  rw [gs_id_appLE, gs_id_appLE, hf Z t g z (h₂ trivial), gm_charUnit_zero, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReduction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_charUnit_zero_eq_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S} (τ : Z ⟶ splitTorus S X)
    (z : Z.left) : gm τ.left z ⊤ (charUnit S X 0) = 1 := by
  have a : splitTorusPointsEquiv S X Z τ (Multiplicative.ofAdd 0) = pullU τ.left ⊤ (charUnit S X 0) :=
    Units.ext (splitTorusPointsEquiv_val _ _ _ τ 0)
  have b : pullU τ.left ⊤ (charUnit S X 0) = 1 := a.symm.trans (map_one _)
  have c := gm_pull (𝟙 Z.left) τ.left z ⊤ trivial (charUnit S X 0)
  rw [b, map_one, Category.id_comp] at c
  exact c.symm

def chartPullH {k : Type} [Field k] (Φ : FibPre k) {Y : Scheme.{0}} {L : LB Y} {π : Φ.E.B.left ⟶ Y} {N : ℕ}
    (c : ChartPull Φ.N₀ (npw L N) π) :
    ChartPull (Φ.H 1) (LB.LinComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ))) (𝟙 _) :=
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l _ hy => Set.mem_iInter.2 fun _ => c.le l hy
  { idx := fun l _ => c.idx l
    le := le
    g := fun y l l' hl hl' => by
      refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) (𝟙 _) y _ _
        (le l hl) (le l' hl')).symm
      have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hl hl'
      have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hl, hl'⟩ (Φ.N₀.g l l')
      refine (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).trans (Eq.symm ?_)
      refine Eq.trans ?_ (map_pow _ _ _).symm
      refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
      rw [Category.assoc]
      rfl }

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_red_of_pure : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF α hw φ hp
  have := Φ.D.q_hom
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  obtain ⟨s, hs⟩ := exists_sec_of_refine _ _ _ (Φ.H_isLB 1) (DVR.linComb_isLB L hL _ _) (chartPullH Φ c) φ
  have hF' : FormEq (Sum.elim (fun _ : Fin 1 => 𝟙 _ ≫ Φ.D.q.left ≫ π) φt)
      (Sum.elim (fun _ => (N : ℤ)) (fun a => - εt a)) (fun a => Φ.D.q.left ≫ ψ a) ε := by
    intro U _ h
    have e := hF U h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp, zpow_neg,
      Finset.prod_inv_distrib] at e ⊢
    rw [← e, mul_inv_cancel_right]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF' (pullMulSec s (𝟙 _) (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have vσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) (J : (Z ⟶ Y) → L.ι), Good L z J → ∀ l : Φ.N₀.ι,
      r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J (r ≫ Φ.D.q.left ≫ π) = c.idx l →
      gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) (φ.f l) = sval σ r z J * (val t r z J).val := by
    intro Z r z J hJ l hl e
    rw [hσ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_inv, Category.comp_id, Units.inv_mul_cancel_right,
      sval_of s r z J (fun _ => c.idx l) (fun _ => e)]
    exact hs l Z r z hl
  have le : ∀ j : K → L.ι, Φ.D.q.left ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Φ.E.B.left, LB.wchart L ψ j),
      (Φ.D.q.left.app _).hom a = (Φ.G.left.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine exists_app_eq_of_hasWt_zero k Φ.E Φ.G Φ.D _ _ fun Z τ g z hz => ?_
    have hq : ((τ ≫ Φ.D.i) * g).left ≫ Φ.D.q.left = g.left ≫ Φ.D.q.left :=
      congrArg (fun x => x.left) (GtBaseChange.translate_comp Φ.D.q Φ.D.i Φ.D.isKernel τ g)
    have hz' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hz
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left (g.left z))
    have hl' := GtBaseChange.translate_mem Φ.D.q Φ.D.i Φ.D.isKernel τ g _ z hl
    obtain ⟨J, hJ, e⟩ := exists_good L hL z (K := Unit) (fun _ => g.left ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hl)
    have hwt : HasWt Φ.D.i _ (φ.f l) α :=
      (PureWt.hasWt_iff_weight k Φ.E Φ.G Φ.D (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) (φ.f l) α).2 fun χ hne => by
        by_contra h
        exact hne (hp ⟨l, h⟩)
    have h₀ := hwt Z τ g z hl
    have h₁ := vσ _ g.left z J hJ l hl (e ())
    have h₂ := vσ _ ((τ ≫ Φ.D.i) * g).left z J hJ l hl' (by rw [← Category.assoc, hq, Category.assoc]; exact e ())
    have h₃ : sval σ ((τ ≫ Φ.D.i) * g).left z J = sval σ g.left z J := by
      have h₄ := h₂.symm.trans (h₀.trans (congrArg _ h₁))
      rw [hw Z τ g z J hJ, mul_left_comm, ← Units.val_mul] at h₄
      exact (Units.mul_left_inj _).1 h₄
    rw [gm_charUnit_zero_eq_one, Units.val_one, _root_.one_mul]
    refine (gs_res _ z (le j) hz' _).trans (Eq.trans ?_ (gs_res _ z (le j) hz _).symm)
    refine (sec_trans σ _ z (le j hz') (hJ.mem _ _)).trans (Eq.trans ?_ (sec_trans σ _ z (le j hz) (hJ.mem _ _)).symm)
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) h₃
    simp only [trF_comp, ← Category.assoc, hq]
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z), Φ.D.q.left (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ Φ.D.q.left) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => Φ.D.q.left ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective Φ.D.q.left (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ l hl e => ?_⟩
  · have hy' : Φ.D.q.left y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ Φ.D.q.left) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ Φ.D.q.left) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ Φ.D.q.left) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine (vσ Z r z J hJ l hl e).trans (congrArg₂ (· * ·) (Eq.symm ?_) rfl)
    rw [sval_of _ (r ≫ Φ.D.q.left) z J (fun a => J (r ≫ Φ.D.q.left ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ Φ.D.q.left ≫ ψ a))

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReductionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pureWeight_section_reduction : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  first | exact @GlobalTheory.ZH.UFib.exists_red_of_pure | exact GlobalTheory.ZH.UFib.exists_red_of_pure | (intros; apply GlobalTheory.ZH.UFib.exists_red_of_pure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLinCombIffPullbackMulGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLinCombIffPullbackMulGenerator
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_linSum {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (r : Z ⟶ Y) (z : Z) (W : Y.Opens) (hm : r z ∈ W) (f : I → Γ(Y, W)) :
    gs r z W (∑ i, constFn p W (a i) * f i) = ∑ i, cst (r ≫ p) z (a i) * gs r z W (f i) := by
  have e : ∀ (b : I → Γ(Y, W)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gs_eq r z _ hm, map_sum]
  rw [e]
  exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)

theorem isLin_iff_of_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t _ I _ b φ b₀ φ₀ a hb hb₀
  have pick : ∀ (y : Φ.G.left) (l : Φ.N₀.ι), y ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l →
      ∃ J, Good L y J ∧ J (𝟙 _ ≫ Φ.D.q.left ≫ π) = c.idx l := fun y l hy => by
    obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun _ : PUnit => 𝟙 _ ≫ Φ.D.q.left ≫ π) (fun _ => c.idx l)
      (fun _ _ _ => rfl) (fun _ => c.le l hy)
    exact ⟨J, hJ, e PUnit.unit⟩
  have hw : (𝟙 _ ≫ Φ.D.q.left) ≫ Φ.E.B.hom = 𝟙 _ ≫ Φ.G.hom := by
    rw [Category.assoc, Over.w]
  constructor
  · intro h l
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := pick y l hy
    refine (hb₀ _ (𝟙 _) y J hJ l hy e).trans (Eq.trans ?_ (gs_linSum Φ.G.hom a (𝟙 _) y _ hy _).symm)
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      rw [← hw]
      exact (congrArg (gs _ y _) (h _)).trans (gs_linSum Φ.E.B.hom a _ y _ m _)
    rw [e₁, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_assoc _ _ _).trans (congrArg _ (hb i _ (𝟙 _) y J hJ l hy e).symm)
  · intro h j
    have := Φ.D.q_flat
    have := Φ.D.q_surjective
    apply GlobalTheory.FunDescent.app_injective Φ.D.q.left
    refine fn_ext fun y hy => ?_
    refine (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) Φ.D.q.left y _ hy _).symm)
    refine Eq.trans ?_ (gs_linSum Φ.E.B.hom a (𝟙 _ ≫ Φ.D.q.left) y _ hy _).symm
    obtain ⟨l, hl⟩ := exists_chart Φ.isLB (Φ.D.q.left y)
    obtain ⟨J, hJ, e⟩ := pick y l hl
    have m := hJ.mem ψ (𝟙 _ ≫ Φ.D.q.left)
    have e₁ : sval b₀ (𝟙 _ ≫ Φ.D.q.left) y J =
        ∑ i, cst (𝟙 _ ≫ Φ.G.hom) y (a i) * sval (b i) (𝟙 _ ≫ Φ.D.q.left) y J := by
      refine (Units.mul_left_inj (val t (𝟙 _) y J)).1 ?_
      refine (hb₀ _ (𝟙 _) y J hJ l hl e).symm.trans ((congrArg (gs _ y _) (h l)).trans
        ((gs_linSum Φ.G.hom a (𝟙 _) y _ hl _).trans ?_))
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (congrArg _ (hb i _ (𝟙 _) y J hJ l hl e)).trans (mul_assoc _ _ _).symm
    refine (sec_trans b₀ (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).trans ((congrArg _ e₁).trans ?_)
    rw [Finset.mul_sum, hw]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (mul_left_comm _ _ _).trans (congrArg _ (sec_trans (b i) (𝟙 _ ≫ Φ.D.q.left) y (j := j) hy m).symm)

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLinCombIffPullbackMulGeneratorStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLinComb_iff_pullback_mul_generator : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → ∀ (I : Type) [Fintype I] (b : I → LB.Sec (LB.LinComb L ψ ε)) (φ : I → (Φ.H 1).Sec) (b₀ : LB.Sec (LB.LinComb L ψ ε)) (φ₀ : (Φ.H 1).Sec) (a : I → k), (∀ i, UFib.Red Φ c t (b i) (φ i)) → UFib.Red Φ c t b₀ φ₀ → (IsLin Φ.E.B.hom b a b₀ ↔ IsLin Φ.G.hom φ a φ₀) := by
  first | exact @GlobalTheory.ZH.UFib.isLin_iff_of_red | exact GlobalTheory.ZH.UFib.isLin_iff_of_red | (intros; apply GlobalTheory.ZH.UFib.isLin_iff_of_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SameCoordsOfGermsCommonUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SameCoordsOfGermsCommonUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem toStk_valR_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)) : toStk z (valR x U a) = gs x z U a := by
  rw [valR, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem toStk_surjective {F : Type} [Field F] (y : Sp F) : Function.Surjective (toStk y) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp F).presheaf.exists_germ_eq s
  obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_mem (𝟙 (Sp F)) U y).2 hU)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom a, by simp [toStk]⟩

theorem crd_of_germs_unit : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (H : LB X) (H' : LB Y), H'.IsLB → ∀ (J : Type) (F : J → H.Sec) (σ : J → H'.Sec) (x : Sp k ⟶ X) (y : Sp k ⟶ Y), (∀ (z : Sp k) (l : H.ι) (l' : H'.ι), x z ∈ H.U l → y z ∈ H'.U l' → ∃ u : ((Sp k).presheaf.stalk z)ˣ, ∀ i, gs x z (H.U l) ((F i).f l) = u.val * gs y z (H'.U l') ((σ i).f l')) → ∀ v : J → k, GlobalTheory.ZH.Crd H F x v → GlobalTheory.ZH.Crd H' σ y v := by
  intro k _ X Y H H' hH' J F σ x y h v ⟨l, c, hl, hv⟩
  let z : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨l', hl'⟩ := exists_chart hH' (y z)
  have hx := (top_le_iff_mem x _ z).1 hl
  obtain ⟨u, hu⟩ := h z l l' hx hl'
  obtain ⟨f, hf⟩ := toStk_surjective z u.val
  have f0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact u.ne_zero hf.symm
  refine ⟨l', c * Units.mk0 f f0, (top_le_iff_mem y _ z).2 hl', fun j => ?_⟩
  rw [hv j, Units.val_mul, Units.val_mk0, _root_.mul_assoc]
  congr 1
  apply (toStk z).injective
  rw [map_mul, toStk_valR_gs x _ z hx, toStk_valR_gs y _ z hl', hf, hu j]

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SameCoordsOfGermsCommonUnitStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameCoords_of_germs_common_unit : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (H : LB X) (H' : LB Y), H'.IsLB → ∀ (J : Type) (F : J → H.Sec) (σ : J → H'.Sec) (x : Sp k ⟶ X) (y : Sp k ⟶ Y), (∀ (z : Sp k) (l : H.ι) (l' : H'.ι), x z ∈ H.U l → y z ∈ H'.U l' → ∃ u : ((Sp k).presheaf.stalk z)ˣ, ∀ i, gs x z (H.U l) ((F i).f l) = u.val * gs y z (H'.U l') ((σ i).f l')) → ∀ v : J → k, GlobalTheory.ZH.Crd H F x v → GlobalTheory.ZH.Crd H' σ y v := by
  first | exact @GlobalTheory.ZH.UFib.crd_of_germs_unit | exact GlobalTheory.ZH.UFib.crd_of_germs_unit | (intros; apply GlobalTheory.ZH.UFib.crd_of_germs_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyGeometricSpecialFibreUniformised
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem exists_fibre {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (k : Type) [Field k]
    (f : Sp k ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (N : ℕ) :
    ∃ (Φ : FibPre k) (r₀ : Φ.G.left ⟶ (thickObj R I e G).left) (xe : Φ.E.X ≃+ D.X) (π : Φ.E.B.left ⟶ D.P.A.left),
      IsGrpPullback Φ.G (thickObj R I e G) f r₀ ∧ IsGrpPullback Φ.E.B D.P.A (f ≫ thick R I e) π ∧
      Φ.D.q.left ≫ π = r₀ ≫ g.pG.left ∧
      (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧
      (∀ χ, GenWt Φ.D.i (LB.pullGen D.P.L _ _ (g.t (xe χ)) r₀) χ) ∧ Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) := by
  obtain ⟨E, xe, d, π, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_gtDatum_of_torusCoords R I D e G g
  obtain ⟨E', xe', d', π', k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.exists_gtDatum_baseChange_maps' _ _ f E _ d
  obtain ⟨N₀, n₁, n₂, n₃, n₄⟩ := GlobalTheory.T.exists_affine_refinement_splitExtCharts _ E' _ (npw D.P.L N) (npw_isLB D.P.isLB N) (π' ≫ π)
  choose ch hch using n₃
  have : IsCommMonObj (thickObj R I e G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback f).obj (thickObj R I e G)) := Functor.isCommMonObj_obj
  have hp := isGrpPullback_pullback (thickObj R I e G) f
  refine ⟨{ E := E', G := (Over.pullback f).obj (thickObj R I e G), D := d', N₀ := N₀, isLB := n₁, aff := n₂,
            ch := ch, le := hch }, pullback.fst _ f, xe'.trans xe, π' ≫ π, hp, k₁.comp h₁, ?_, fun χ => ?_,
    fun χ Z τ y z J hJ => ?_, n₄⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂)))
  · exact (k₃ χ).trans (E'.O χ).isLB (pull_isLB (E.O _).isLB _) (DVR.linComb_isLB _ D.P.isLB _ _)
      ((h₃ (xe' χ)).chartPull (Geo.Tor.chartPullPull _ π' π' rfl)
        (chartPullSame D.P.L _ _ Oε π' fun a => Category.assoc _ _ _))
  · obtain ⟨τ₀, t₁, t₂⟩ := k₄ Z τ
    have e₁ := hp.2 Z (τ ≫ d'.i) y (τ₀ ≫ d.i) (pushPt hp.1.w y) t₁ rfl
    have e₂ := h₄ (xe' χ) _ τ₀ (pushPt hp.1.w y) z J hJ
    rw [e₁] at e₂
    exact (val_pull hJ _ _ _).trans (e₂.trans (congrArg₂ (· * ·) (t₂ χ z) (val_pull hJ _ _ _).symm))

theorem formEq_fam {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (p : T ⟶ D.P.A) (α : D.X) (N : ℕ) {Y B : Scheme.{0}} (r : Y ⟶ T.left) (q : Y ⟶ B) (π : B ⟶ D.P.A.left)
    (h : q ≫ π = r ≫ p.left) :
    FormEq (Sum.elim (fun a => q ≫ π ≫ D.famφB α a) (fun a => r ≫ D.Oφ p α a)) (Sum.elim (DegPre.famε N) Oinvε)
      (fun _ : Fin 1 => q ≫ π) (fun _ => (N : ℤ)) := by
  intro U _ F
  have a₀ : q ≫ π ≫ D.famφB α 0 = q ≫ π := congrArg (q ≫ ·) (Category.comp_id _)
  have a₁ : q ≫ π ≫ D.famφB α 1 = r ≫ D.Oφ p α 0 := by
    rw [← Category.assoc, h, Category.assoc]
    refine congrArg (r ≫ ·) ?_
    change (p ≫ (𝟙 D.P.A * (toUnit _ ≫ D.c α))).left = (p * (toUnit _ ≫ D.c α)).left
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  have a₂ : q ≫ π ≫ D.famφB α 2 = r ≫ D.Oφ p α 1 := by
    rw [← Category.assoc, h, Category.assoc]
    refine congrArg (r ≫ ·) ?_
    change (p ≫ toUnit _ ≫ D.c α).left = (toUnit _ ≫ D.c α).left
    rw [← Category.assoc, comp_toUnit]
  have a₃ : q ≫ π ≫ D.famφB α 3 = r ≫ D.Oφ p α 3 := by
    rw [← Category.assoc, h, Category.assoc]
    refine congrArg (r ≫ ·) ?_
    change (p ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [← Category.assoc, comp_toUnit]
  have a₄ : r ≫ D.Oφ p α 2 = q ≫ π := h.symm
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [a₀, a₁, a₂, a₃, a₄]
  change F _ ^ ((N : ℤ) - 1) * F _ ^ (1 : ℤ) * F _ ^ (-1 : ℤ) * F _ ^ (1 : ℤ) *
    (F _ ^ (-1 : ℤ) * F _ ^ (1 : ℤ) * F _ ^ (1 : ℤ) * F _ ^ (-1 : ℤ)) = _
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem cst_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {Z : Scheme.{0}} (q : Z ⟶ Sp R') (z : Z)
    (a : R) : cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  refine (gs_pull q (spMap φ) z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem isLin_pullSec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X Y Y' : Scheme.{0}} (L : LB X)
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ Sp R) (p' : Y' ⟶ Sp R') (π : Y' ⟶ Y)
    (w : π ≫ p = p' ≫ spMap φ) {I : Type} [Fintype I] (β : I → LB.Sec (LB.LinComb L ψ ε)) (a : I → R)
    (s : LB.Sec (LB.LinComb L ψ ε)) (h : IsLin p β a s) :
    IsLin p' (fun i => DVR.pullSec L ψ ε (β i) π) (fun i => φ (a i)) (DVR.pullSec L ψ ε s π) := by
  intro j
  refine fn_ext fun y hy => ?_
  have hm : (𝟙 Y' ≫ π) y ∈ LB.wchart L ψ j := DVR.wchart_comp_le ψ π j hy
  have v : ∀ s : LB.Sec (LB.LinComb L ψ ε), gs (𝟙 Y') y _ ((DVR.pullSec L ψ ε s π).f j) =
      gs (𝟙 Y' ≫ π) y (LB.wchart L ψ j) (s.f j) := fun s =>
    (gs_res (𝟙 Y') y (DVR.wchart_comp_le ψ π j) hy _).trans (gs_pull (𝟙 Y') π y _ hm _)
  refine (v s).trans ((congrArg _ (h j)).trans ((DVR.gs_fsum _ y _ hm _ _).trans
    (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (DVR.gs_fsum (𝟙 Y') y _ hy _ _).symm)))
  refine (gs_mul _ y _ hm _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ (v _).symm) (gs_mul (𝟙 Y') y _ hy _ _).symm)
  refine (gs_constFn p _ _ y hm _).trans (Eq.trans ?_ (gs_constFn p' _ (𝟙 Y') y hy _).symm)
  rw [Category.assoc, w, ← Category.assoc, cst_spMap]

def sumSec {X : Scheme.{0}} {M : LB X} {A : Type} (S : Finset A) (φ : A → M.Sec) : M.Sec where
  f l := ∑ α ∈ S, (φ α).f l
  compat i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => (φ α).compat i j

theorem isPart_sumSec {k : Type} [Field k] (Φ : FibPre k) {A : Type} (e : A → Φ.E.X) (he : Function.Injective e)
    (S : Finset A) (φ : A → (Φ.H 1).Sec) (hφ : ∀ α, Φ.Pure (e α) (φ α)) (h₀ : ∀ α ∉ S, ∀ l, (φ α).f l = 0) (α : A) :
    Φ.IsPart (e α) (sumSec S φ) (φ α) := by
  refine ⟨hφ α, fun l => Eq.symm ?_⟩
  refine (WtPart.cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (e α) S _).trans ?_
  change ∑ β ∈ S, Φ.wt (φ β) (e α) l = _
  refine Finset.sum_eq_single α (fun β _ hne => ?_) (fun hα => ?_)
  · by_contra h
    exact hne (he (hφ β ⟨l, h⟩)).symm
  · rw [FibPre.wt, h₀ α hα l]
    exact WtPart.cf_zero (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) _

theorem exists_good_at {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) (ψ : Z ⟶ X) (j : L.ι) (h : ψ z ∈ L.U j) :
    ∃ J, Good L z J ∧ J ψ = j := by
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun _ : Unit => ψ) (fun _ => j) (fun _ _ _ => rfl) (fun _ => h)
  exact ⟨J, hJ, e ()⟩

theorem nonempty_fibOf : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (N : ℕ), 1 ≤ N → Nonempty (u.FibOf N) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u N hN
  have hloc : IsLocalHom u.j := (GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u).2.1
  have : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hL := u.D.toPre.P.isLB
  let φ : u.V →+* kb p := (IsLocalRing.residue (OO p)).comp u.j
  let f₀ : u.V ⧸ IsLocalRing.maximalIdeal u.V ^ (0 + 1) →+* kb p := Ideal.Quotient.lift _ φ fun a ha => by
    rw [zero_add, pow_one] at ha
    exact (IsLocalRing.residue_eq_zero_iff _).2 (map_nonunit u.j a ha)
  have hf : spMap f₀ ≫ thick u.V (IsLocalRing.maximalIdeal u.V) 0 = spMap φ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hf' : spMap φ = rPt p ≫ spMap u.j := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨Φ, r₀, xe, π, h₁, h₂, h₃, h₄, h₅, ⟨c⟩⟩ :=
    exists_fibre (IsLocalRing.maximalIdeal u.V) u.D.toPre 0 u.G (u.U.gt 0) (kb p) (spMap f₀) N
  rw [hf] at h₂
  obtain ⟨pol, hpol⟩ := GlobalTheory.T.exists_principalPolarisation_abelianFibre hLL.1.polBaseChange _ Φ _ u.D.toPre _ π h₂ xe h₄ N ⟨c⟩
  let t := fun α : u.D.toPre.X => LB.pullGen u.D.toPre.P.L _ _ ((u.U.gt 0).t α) r₀
  have ht : ∀ α, (t α).IsGen := fun α => DVR.pullGen_isGen _ _ _ _ ((u.U.gt 0).t_gen α) r₀
  have hw : ∀ α, GenWt Φ.D.i (t α) (xe.symm α) := fun α => by
    obtain ⟨χ, rfl⟩ := xe.surjective α
    rw [xe.symm_apply_apply]
    exact h₅ χ
  have hF := fun α => formEq_fam u.D.toPre (u.U.gt 0).pG α N r₀ Φ.D.q.left π h₃
  let pb := fun α (β : u.D.toPre.SecB N α) => DVR.pullSec u.D.toPre.P.L (u.D.toPre.famφB α) (DegPre.famε N) β π
  choose red hred using fun α (β : u.D.toPre.SecB N α) =>
    GlobalTheory.T.exists_section_pullback_mul_generator _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) (hF α) (pb α β)
  have hpure : ∀ α β, Φ.Pure (xe.symm α) (red α β) := fun α β =>
    GlobalTheory.T.isPure_pullbackSection_mul_weightGenerator _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) _ (hw α) _ _ (hred α β)
  refine ⟨{
    Φ := Φ
    r := r₀ ≫ pullback.fst _ _
    cart := (h₁.comp (isGrpPullback_pullback u.G _)).congr (hf.trans hf') rfl
    xe := xe
    pol := pol
    dim := hpol
    red := red
    pure := hpure
    lin := fun α I _ β a gm₀ h => ?_
    basis := fun α I _ β hβ ψ hψ => ?_
    exp := fun J σ f hσ => ?_ }⟩
  · exact (GlobalTheory.T.isLinComb_iff_pullback_mul_generator _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) I _ _ _ _ _ (fun i => hred α (β i)) (hred α gm₀)).1
      (isLin_pullSec φ _ _ _ _ _ π h₂.1.w β a gm₀ h)
  · obtain ⟨b, hb⟩ := GlobalTheory.T.exists_pureWeight_section_reduction _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) (hF α) _ (hw α) ψ hψ
    exact (existsUnique_congr fun a => GlobalTheory.T.isLinComb_iff_pullback_mul_generator _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) I _ _ _ _ a
      (fun i => hred α (β i)) hb).1
      (GlobalTheory.T.twistedPower_sectionBasis_baseChange GlobalTheory.twistBaseChange u.V u.D.toPre N hN α _ φ _ _ π h₂.1 I β hβ b)
  · choose T hT using fun i => DVR.expandsAt_val u.U.toUnifPre 0 N (σ i) (f i) (hσ i)
    have hv : ∀ α (β : u.D.toPre.SecB N α) (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) J', Good u.D.toPre.P.L z J' →
        ∀ l, r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J' (r ≫ Φ.D.q.left ≫ π) = c.idx l →
        gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) ((red α β).f l) =
          sval β ((r ≫ r₀) ≫ DVR.pGl u.U.toUnifPre 0) z J' * (val (DVR.tG u.U.toUnifPre 0 α) (r ≫ r₀) z J').val := by
      intro α β Z r z J' hJ l hl e
      refine (hred α β Z r z J' hJ l hl e).trans (congrArg₂ (· * ·) ?_ (congrArg Units.val (val_pull hJ _ _ _)))
      refine (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ).trans ?_
      rw [Category.assoc, h₃, ← Category.assoc]
    refine ⟨fun i => sumSec (T i) (fun α => red α (f i α)), fun i α =>
      isPart_sumSec Φ xe.symm xe.symm.injective (T i) _ (fun α => hpure α _) (fun α hα l => ?_) α, fun x v => ?_⟩
    · refine fn_ext fun y hy => ?_
      obtain ⟨J', hJ, e⟩ := exists_good_at hL y (𝟙 _ ≫ Φ.D.q.left ≫ π) (c.idx l) (c.le l hy)
      refine (hv α _ _ (𝟙 _) y J' hJ l hy e).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
      rw [(hT i _ _ y J' hJ).1 α hα, zero_mul]
    · refine GlobalTheory.T.sameCoords_of_germs_common_unit _ _ _ _ _ (DVR.linComb_isLB _ u.U.LG.isLB _ _) J _ σ x.left _ (fun z l l' hl hl' => ?_) v
      obtain ⟨J', hJ, e⟩ := exists_good_at hL z (x.left ≫ Φ.D.q.left ≫ π) (c.idx l) (c.le l hl)
      obtain ⟨jL, rfl⟩ : ∃ jL, l' = fun _ => jL := ⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim i 0)⟩
      refine ⟨DVR.wv u.U.toUnifPre 0 (x.left ≫ r₀) z (J' ((x.left ≫ r₀) ≫ DVR.pGl u.U.toUnifPre 0)) jL ^ N,
        fun i => Eq.trans ?_ (((hT i _ (x.left ≫ r₀) z J' hJ).2 jL (Set.mem_iInter.1 hl' 0)).symm.trans ?_)⟩
      · exact (DVR.gs_fsum x.left z _ hl _ _).trans (Finset.sum_congr rfl fun α _ => hv α _ _ _ z J' hJ l hl e)
      · exact congrArg (fun q => _ * DVR.sv u.U.toUnifPre N (σ i) q z jL) (Category.assoc _ _ _)

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyGeometricSpecialFibreUniformisedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_geometric_special_fibre_uniformised : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (N : ℕ), 1 ≤ N → Nonempty (u.FibOf N) := by
  first | exact @GlobalTheory.ZH.UFib.nonempty_fibOf | exact GlobalTheory.ZH.UFib.nonempty_fibOf | (intros; apply GlobalTheory.ZH.UFib.nonempty_fibOf <;> assumption)
end
