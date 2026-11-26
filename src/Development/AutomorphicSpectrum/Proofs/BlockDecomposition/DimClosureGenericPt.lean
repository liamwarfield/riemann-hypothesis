module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianLineBundleSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArithmeticVarietyPointDimension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvProdBlockUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.UnderExists

theorem exists_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z :=
  fun m n z hz => (GlobalTheory.CompanionTheory.MPDict.Under.existsUnique_isUnder m n z hz).exists

end GlobalTheory.CompanionTheory.MPDict.UnderExists
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdZpowSingle
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TwUnits

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (h'' : W ≤ U) (x : Γ(X, U)ˣ) :
    Semi.res h' (Semi.res h x) = Semi.res h'' x := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom x.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_div_g {X : Scheme.{0}} (T L : LB X) (p q : T.ι × L.ι) {W : X.Opens}
    (h : W ≤ (T.U p.1 ⊓ L.U p.2) ⊓ (T.U q.1 ⊓ L.U q.2)) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res h ((LB.div T L).g p q) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul (Semi.res h) _ _).trans (congrArg₂ (· * ·) (res_res' _ _ h₁ _)
    ((map_inv (Semi.res h) _).trans (congrArg (·⁻¹) (res_res' _ _ h₂ _))))

theorem iso_law {X : Scheme.{0}} {L T : LB X} {w : LB.Iso L T} (hw : w.IsGen) (p q : T.ι × L.ι) {W : X.Opens}
    (hp : W ≤ T.U p.1 ⊓ L.U p.2) (hq : W ≤ T.U q.1 ⊓ L.U q.2) (h₁ : W ≤ T.U p.1 ⊓ T.U q.1)
    (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    Semi.res hp (w.s p) = Semi.res h₁ (T.g p.1 q.1) * (Semi.res h₂ (L.g p.2 q.2))⁻¹ * Semi.res hq (w.s q) := by
  have e := congrArg (Semi.res (le_inf hp hq)) (hw p q)
  exact ((res_res' _ _ hp _).symm.trans e).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (res_div_g T L p q (le_inf hp hq) h₁ h₂) (res_res' _ _ hq _)))

theorem res_pull_g (k : Fin (m + 1)) (j j' : PUnit → Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j ⊓ ((O1 ℤ (n k)).pull (pr ℤ m n k)).U j')
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (j PUnit.unit) ⊓ chart ℤ (n k) (j' PUnit.unit))) :
    Semi.res h (((O1 ℤ (n k)).pull (pr ℤ m n k)).g j j') = blockUnit (j PUnit.unit) (j' PUnit.unit) h' := by
  have e := linComb_punit_g (O1 ℤ (n k)) (pr ℤ m n k) 1 j j'
  rw [zpow_one] at e
  exact (congrArg (Semi.res h) e).trans (res_res' _ _ h' _)

def twIdx (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : (twB m n b t).ι :=
  Prod.mk (fun _ => c b.succ) (fun _ => c 0)

theorem mchart_le_U (b : Fin m) (t : ℤ) (c : ∀ k, Bk n k) : mchart c ≤ (twB m n b t).U (twIdx b t c) :=
  fun _ hx => ⟨Set.mem_iInter.2 fun _ => mchart_le c _ hx, Set.mem_iInter.2 fun _ => mchart_le c _ hx⟩

theorem blk_le {c c' : ∀ k, Bk n k} {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c') (k : Fin (m + 1)) :
    W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)) :=
  fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩

theorem res_twB_g (b : Fin m) (t : ℤ) (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens} (hW : W ≤ mchart c ⊓ mchart c')
    (h : W ≤ (twB m n b t).U (twIdx b t c) ⊓ (twB m n b t).U (twIdx b t c')) :
    Semi.res h ((twB m n b t).g (twIdx b t c) (twIdx b t c')) =
      blockUnit (c b.succ) (c' b.succ) (blk_le hW b.succ) * blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
  have h₁ : W ≤ ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c b.succ) ⊓
      ((O1 ℤ (n b.succ)).pull (pr ℤ m n b.succ)).U (fun _ => c' b.succ) :=
    le_inf (fun _ hx => h hx |>.1.1) (fun _ hx => h hx |>.2.1)
  have h₂ : W ≤ ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c 0) ⊓
      ((O1 ℤ (n 0)).pull (pr ℤ m n 0)).U (fun _ => c' 0) :=
    le_inf (fun _ hx => h hx |>.1.2) (fun _ hx => h hx |>.2.2)
  have e₁ := res_pull_g b.succ (fun _ => c b.succ) (fun _ => c' b.succ) h₁ (blk_le hW b.succ)
  have e₂ := res_pull_g 0 (fun _ => c 0) (fun _ => c' 0) h₂ (blk_le hW 0)
  have e₃ : (Semi.res h₂ (((O1 ℤ (n 0)).pull (pr ℤ m n 0)).g (fun _ => c 0) (fun _ => c' 0)) ^ (-t))⁻¹ =
      blockUnit (c 0) (c' 0) (blk_le hW 0) ^ t := by
    rw [zpow_neg, inv_inv]
    exact congrArg (· ^ t) e₂
  exact (res_div_g _ _ (twIdx b t c) (twIdx b t c') h h₁ h₂).trans (congrArg₂ (· * ·) e₁
    ((congrArg (·⁻¹) (map_zpow (Semi.res h₂) _ (-t))).trans e₃))

theorem blockUnit_self {k : Fin (m + 1)} (i : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) i)) : blockUnit i i h = 1 := by
  rw [blockUnit, ratioUnit_self, map_one, map_one]

theorem prod_zpow_single {G : Type*} [CommGroup G] (f : Fin (m + 1) → G) (p q : Fin (m + 1)) (t : ℤ) :
    ∏ k, f k ^ ((Pi.single p 1 + t • Pi.single q 1 : Fin (m + 1) → ℤ) k) = f p * f q ^ t := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zpow_add, Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_eq_single p (fun k _ hk => by simp [hk]) (by simp)]
    simp
  · rw [Finset.prod_eq_single q (fun k _ hk => by simp [hk]) (by simp)]
    simp

variable {B : LB (MP ℤ m n)} {b : Fin m} {t : ℤ}

def uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) : Γ(MP ℤ m n, B.U i ⊓ mchart c)ˣ :=
  Semi.res (le_inf (inf_le_right.trans (mchart_le_U b t c)) inf_le_left) (w.s (twIdx b t c, i))

theorem res_uOf (w : LB.Iso B (twB m n b t)) (i : B.ι) (c : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ B.U i ⊓ mchart c) (h' : W ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i) :
    Semi.res h (uOf w i c) = Semi.res h' (w.s (twIdx b t c, i)) :=
  res_res' _ _ h' _

theorem frame_uOf {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i j : B.ι) (c : ∀ k, Bk n k) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        B.U i ⊓ B.U j ⊓ mchart c ≤ B.U j ⊓ mchart c) (uOf w j c) =
      Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ B.U j) (B.g i j) *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c ≤ B.U i ⊓ mchart c) (uOf w i c) := by
  have hc : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c ⊓ mchart c := le_inf inf_le_right inf_le_right
  have hU := (inf_le_right : B.U i ⊓ B.U j ⊓ mchart c ≤ mchart c).trans (mchart_le_U b t c)
  have hi : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i :=
    le_inf hU (inf_le_left.trans inf_le_left)
  have hj : B.U i ⊓ B.U j ⊓ mchart c ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U j :=
    le_inf hU (inf_le_left.trans inf_le_right)
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c, j) hi hj (le_inf hU hU) inf_le_left
  rw [res_twB_g b t c c hc, blockUnit_self, blockUnit_self, one_zpow, one_mul, one_mul] at e
  rw [res_uOf w j c _ hj, res_uOf w i c _ hi]
  exact (eq_inv_mul_iff_mul_eq.1 e).symm

theorem mono_uOf (hB : B.IsLB) {w : LB.Iso B (twB m n b t)} (hw : w.IsGen) (i : B.ι) (c c' : ∀ k, Bk n k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c) (uOf w i c) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ mchart c') (uOf w i c') *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^
        (Pi.single b.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k := by
  have hc : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c ⊓ mchart c' := inf_le_right
  have hU := (inf_le_right.trans inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c).trans (mchart_le_U b t c)
  have hU' := (inf_le_right.trans inf_le_right : B.U i ⊓ (mchart c ⊓ mchart c') ≤ mchart c').trans (mchart_le_U b t c')
  have hs : Semi.res (le_inf inf_le_left inf_le_left : B.U i ⊓ (mchart c ⊓ mchart c') ≤ B.U i ⊓ B.U i) (B.g i i) = 1 :=
    Units.ext (LB.resG_g_self hB i _)
  have hi : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c) ⊓ B.U i := le_inf hU inf_le_left
  have hi' : B.U i ⊓ (mchart c ⊓ mchart c') ≤ (twB m n b t).U (twIdx b t c') ⊓ B.U i := le_inf hU' inf_le_left
  have e := iso_law hw (twIdx b t c, i) (twIdx b t c', i) hi hi' (le_inf hU hU') (le_inf inf_le_left inf_le_left)
  rw [res_twB_g b t c c' hc] at e
  change _ = _ * (Semi.res _ (B.g i i))⁻¹ * _ at e
  rw [hs, inv_one, mul_one] at e
  rw [res_uOf w i c _ hi, res_uOf w i c' _ hi',
    prod_zpow_single (fun k => blockUnit (c k) (c' k) (blk_le hc k)) b.succ 0 t]
  exact e.trans (mul_comm _ _)

theorem exists_units : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (B : LB (MP ℤ m n)) (c : Fin m) (t : ℤ), B.IsLB → LBIso B (twB m n c t) →
  ∃ u : ∀ (i : B.ι) (c' : ∀ k, Bk n k), Γ(MP ℤ m n, B.U i ⊓ mchart c')ˣ,
    (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ B.U j) (B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ mchart c' ≤ B.U i ⊓ mchart c') (u i c')) ∧
    (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ (Pi.single c.succ 1 + t • Pi.single 0 1 : Fin (m + 1) → ℤ) k) := by
  rintro m n B c t hB ⟨w, hw⟩
  exact ⟨uOf w, frame_uOf hw, mono_uOf hB hw⟩

end GlobalTheory.CompanionTheory.MPDict.TwUnits
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Unique

theorem pullRatio_top_eq {N : ℕ} {x x' : Sp ℂ ⟶ PSpace ℤ N} (i j : Fin (N + 1))
    (h : ⊤ ≤ x ⁻¹ᵁ chart ℤ N i) (h' : ⊤ ≤ x' ⁻¹ᵁ chart ℤ N i)
    (e : valR x (chart ℤ N i) (ratio ℤ N i j) = valR x' (chart ℤ N i) (ratio ℤ N i j)) :
    pullRatio x ⊤ i h j = pullRatio x' ⊤ i h' j := by
  rw [valR, valR, dite_eq_left h, dite_eq_left h'] at e
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e

theorem valR_comp_prB {m : ℕ} {n : Fin (m + 1) → ℕ} (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) =
      valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dite_eq_left h, dite_eq_left h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

end GlobalTheory.CompanionTheory.MPDict.Unique


open GlobalTheory.CompanionTheory.MPDict.Unique in
theorem GlobalTheory.CompanionTheory.MPDict.isUnder_unique : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y' := by
  intro m n z y y' h h'
  refine Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_)
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k)) :=
    mem_ptsIn.2 (mem_ptChart _ k)
  obtain ⟨i, hi⟩ : ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ⟨_, hy⟩
  have hz : z ⟨k, i⟩ ≠ 0 := ((h k i).1).1 hi
  have hi' : y' ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((h' k i).1).2 hz
  refine GlobalTheory.ProjSpace.hom_ext ?_ fun t => ⟨⊤, trivial, i, hi, hi', fun j => ?_⟩
  · have s : pr ℤ m n k ≫ PSpace.str ℤ (n k) = mpStr ℤ m n := pr_toSpecBase ℤ m n k
    rw [Category.assoc, Category.assoc, s, y.2, y'.2]
  · have a : ⊤ ≤ y.1 ⁻¹ᵁ blockChart n k i := hi
    have a' : ⊤ ≤ y'.1 ⁻¹ᵁ blockChart n k i := hi'
    refine pullRatio_top_eq (x := y.1 ≫ prB n k) (x' := y'.1 ≫ prB n k) i j a a' ?_
    rw [valR_comp_prB y.1 i j a, valR_comp_prB y'.1 i j a']
    exact ((h k i).2 j hi).trans ((h' k i).2 j hi').symm
end
end

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.MPDict.HermRep

section Main
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ev_resU {U W : (MP ℤ m n).Opens} (e : W ≤ U) {y : CxPts (mpStr ℤ m n) σ₀}
    (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) (u : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((res e u : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      CxPts.ev (mpStr ℤ m n) σ₀ U (u : Γ(MP ℤ m n, U)) y :=
  CxPts.ev_res e h _

theorem ev_prod_zpow {W : (MP ℤ m n).Opens} {y : CxPts (mpStr ℤ m n) σ₀}
    (h : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) {ι : Type} [Fintype ι] (b : ι → Γ(MP ℤ m n, W)ˣ) (e : ι → ℤ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((∏ k, b k ^ e k : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      ∏ k, (CxPts.ev (mpStr ℤ m n) σ₀ W (b k : Γ(MP ℤ m n, W)) y) ^ e k := by
  have key : ∀ x : Γ(MP ℤ m n, W)ˣ, CxPts.ev (mpStr ℤ m n) σ₀ W (x : Γ(MP ℤ m n, W)) y =
      ((Units.map (evHom h).toMonoidHom x : ℂˣ) : ℂ) := fun x => ev_eq h _
  rw [key, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, key]

theorem ev_blockUnit {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (k : Fin (m + 1)) (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) :
    CxPts.ev (mpStr ℤ m n) σ₀ W (blockUnit i j h : Γ(MP ℤ m n, W)) y = z ⟨k, j⟩ / z ⟨k, i⟩ := by
  have hi : W ≤ blockChart n k i := h.trans ((prB n k).preimage_mono inf_le_left)
  have e1 : (blockUnit i j h : Γ(MP ℤ m n, W)) = pullRatio (prB n k) W i hi j :=
    appLE_ratioOn (φ := prB n k) (i := i) (j := j)
      (inf_le_left : chart ℤ (n k) i ⊓ chart ℤ (n k) j ≤ chart ℤ (n k) i) h
  rw [e1, ← resG_pullRatio (W := blockChart n k i) (hi := le_rfl) hi, CxPts.ev_res hi hW]
  exact (hy k i).2 j (ptsIn_mono hi hW)

theorem ev_prod_blockUnit {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (c c' : ∀ k, Bk n k) {W : (MP ℤ m n).Opens}
    (h : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hW : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) (a : Fin (m + 1) → ℤ) :
    CxPts.ev (mpStr ℤ m n) σ₀ W ((∏ k, blockUnit (c k) (c' k) (h k) ^ a k : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      ∏ k, (z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k := by
  rw [ev_prod_zpow hW]
  exact Finset.prod_congr rfl fun k _ => by rw [ev_blockUnit hy k _ _ (h k) hW]

theorem isUnder_smul {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z)
    (l : Fin (m + 1) → ℂ) (hl : ∀ k, l k ≠ 0) : IsUnder y (fun p => l p.1 * z p) := by
  intro k i
  obtain ⟨h1, h2⟩ := hy k i
  refine ⟨h1.trans ⟨fun h => mul_ne_zero (hl k) h, fun h => right_ne_zero_of_mul h⟩, fun j hj => ?_⟩
  rw [h2 j hj, mul_div_mul_left _ _ (hl k)]

theorem isUnder_of_smul {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (l : Fin (m + 1) → ℂ)
    (hl : ∀ k, l k ≠ 0) (hy : IsUnder y (fun p => l p.1 * z p)) : IsUnder y z := by
  have := isUnder_smul hy (fun k => (l k)⁻¹) fun k => inv_ne_zero (hl k)
  simpa only [inv_mul_cancel_left₀ (hl _)] using this

variable (M : HermLB (mpStr ℤ m n)) (a : Fin (m + 1) → ℤ)
  (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ)

def hval (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) (i : M.B.ι) (c : ∀ k, Bk n k) : ℝ :=
  (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) *
    ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
      Real.exp ((M.φ σ₀).φ i y / 2)

theorem hval_chart (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ)
    (i j : M.B.ι) (c : ∀ k, Bk n k) (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    (hj : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U j ⊓ mchart c)) :
    hval M a u y z i c = hval M a u y z j c := by
  rw [mem_ptsIn_inf] at hi hj
  have hij : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ M.B.U j ⊓ mchart c) :=
    mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨hi.1, hj.1⟩, hi.2⟩
  have e := congrArg (fun w : Γ(MP ℤ m n, M.B.U i ⊓ M.B.U j ⊓ mchart c)ˣ =>
    CxPts.ev (mpStr ℤ m n) σ₀ _ w.val y) (h1 i j c)
  simp only [Units.val_mul, ev_mul, ev_resU _ hij] at e
  have hg : gv (mpStr ℤ m n) σ₀ M.B i j y ≠ 0 := gv_ne_zero hi.1 hj.1
  have hpos : 0 < ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ := norm_pos_iff.2 hg
  have ht := (M.φ σ₀).trans i j y hi.1 hj.1
  unfold hval
  rw [e, ht, norm_mul]
  change _ = _ * (‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ * _) * _
  have ex : Real.exp (((M.φ σ₀).φ i y - Real.log (‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ ^ 2)) / 2) =
      Real.exp ((M.φ σ₀).φ i y / 2) / ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ := by
    rw [Real.log_pow, sub_div, Real.exp_sub]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ / 2 =
      Real.log ‖gv (mpStr ℤ m n) σ₀ M.B i j y‖ by push_cast; ring, Real.exp_log hpos]
  rw [ex]
  field_simp

theorem hval_multi (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k)) {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ}
    (hy : IsUnder y z) (i : M.B.ι) (c c' : ∀ k, Bk n k)
    (hc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c))
    (hc' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c')) :
    hval M a u y z i c = hval M a u y z i c' := by
  rw [mem_ptsIn_inf] at hc hc'
  have hcc : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ (mchart c ⊓ mchart c')) :=
    mem_ptsIn_inf.2 ⟨hc.1, mem_ptsIn_inf.2 ⟨hc.2, hc'.2⟩⟩
  have e := congrArg (fun w : Γ(MP ℤ m n, M.B.U i ⊓ (mchart c ⊓ mchart c'))ˣ =>
    CxPts.ev (mpStr ℤ m n) σ₀ _ w.val y) (h2 i c c')
  simp only [Units.val_mul, ev_mul, ev_resU _ hcc] at e
  rw [ev_prod_blockUnit hy c c' (fun k => (fun _ hx => ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
    M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))) hcc a] at e
  have hz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => ((hy k (c k)).1).1 (ptsIn_mono (mchart_le c k) hc.2)
  unfold hval
  rw [e, norm_mul, norm_prod]
  have hk : ∀ k, ‖z ⟨k, c k⟩‖ ^ a k * ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖ = ‖z ⟨k, c' k⟩‖ ^ a k := by
    intro k
    rw [norm_zpow, norm_div, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ (norm_ne_zero_iff.2 (hz k)))]
  calc (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) * (‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c') (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c')) y‖ * ∏ k, ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖) * Real.exp ((M.φ σ₀).φ i y / 2)
      = (∏ k, (‖z ⟨k, c k⟩‖ ^ a k * ‖(z ⟨k, c' k⟩ / z ⟨k, c k⟩) ^ a k‖)) * ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c') (u i c' : Γ(MP ℤ m n, M.B.U i ⊓ mchart c')) y‖ * Real.exp ((M.φ σ₀).φ i y / 2) := by
        rw [Finset.prod_mul_distrib]; ring
    _ = _ := by simp only [hk]

end Main

section Metric
variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def ptC (y : CxPts (mpStr ℤ m n) σ₀) : ∀ k, Bk n k := fun k => ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k

theorem mem_ptC (y : CxPts (mpStr ℤ m n) σ₀) : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart (ptC y)) :=
  mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptChart _ k)

variable (M : HermLB (mpStr ℤ m n)) (a : Fin (m + 1) → ℤ)
  (u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ)

theorem mem_pick_ptC (y : CxPts (mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U (pick M.isLB y) ⊓ mchart (ptC y)) :=
  mem_ptsIn_inf.2 ⟨mem_pick M.isLB y, mem_ptC y⟩


open Classical in
def hOf (z : (Σ k, Bk n k) → ℂ) : ℝ :=
  if hz : ∃ y, IsUnder y z then hval M a u hz.choose z (pick M.isLB hz.choose) (ptC hz.choose) else 0

theorem hOf_eq (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y')
    {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z) (i : M.B.ι) (c : ∀ k, Bk n k)
    (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)) : hOf M a u z = hval M a u y z i c := by
  have hz : ∃ y, IsUnder y z := ⟨y, hy⟩
  rw [hOf, dite_eq_left hz, uniq z _ _ hz.choose_spec hy]
  have h0 := mem_pick_ptC M y
  rw [mem_ptsIn_inf] at h0 hi
  rw [hval_chart M a u h1 z (pick M.isLB y) i (ptC y) (mem_ptsIn_inf.2 h0) (mem_ptsIn_inf.2 ⟨hi.1, h0.2⟩),
    hval_multi M a u h2 hy i (ptC y) c (mem_ptsIn_inf.2 ⟨hi.1, h0.2⟩) (mem_ptsIn_inf.2 hi)]

theorem hval_pos {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (hy : IsUnder y z) (i : M.B.ι)
    (c : ∀ k, Bk n k) (hi : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)) : 0 < hval M a u y z i c := by
  have hz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k =>
    ((hy k (c k)).1).1 (ptsIn_mono (mchart_le c k) (mem_ptsIn_inf.1 hi).2)
  refine mul_pos (mul_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hz k)) _)
    (norm_pos_iff.2 (ev_ne_zero hi (u i c).isUnit))) (Real.exp_pos _)

theorem hval_smul {y : CxPts (mpStr ℤ m n) σ₀} (z : (Σ k, Bk n k) → ℂ) (l : Fin (m + 1) → ℂ) (i : M.B.ι)
    (c : ∀ k, Bk n k) : hval M a u y (fun p => l p.1 * z p) i c = (∏ k, ‖l k‖ ^ a k) * hval M a u y z i c := by
  unfold hval
  simp only [norm_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

def lineOf (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (ex : ∀ (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z)
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y') :
    Geo.HermLine (Bk n) where
  a := a
  h := hOf M a u
  pos z hz := by
    obtain ⟨y, hy⟩ := ex z hz
    rw [hOf_eq M a u h1 h2 uniq hy _ _ (mem_pick_ptC M y)]
    exact hval_pos M a u hy _ _ (mem_pick_ptC M y)
  smul l z hl := by
    by_cases hz : ∃ y, IsUnder y z
    · obtain ⟨y, hy⟩ := hz
      rw [hOf_eq M a u h1 h2 uniq (isUnder_smul hy l hl) _ _ (mem_pick_ptC M y),
        hOf_eq M a u h1 h2 uniq hy _ _ (mem_pick_ptC M y), hval_smul]
    · have hz' : ¬ ∃ y, IsUnder y (fun p => l p.1 * z p) := fun ⟨y, hy⟩ => hz ⟨y, isUnder_of_smul l hl hy⟩
      rw [hOf, dite_eq_right hz', hOf, dite_eq_right hz, mul_zero]

theorem isHermRep_lineOf (h1 : (∀ i j c',
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U j ⊓ mchart c') (u j c') =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c' ≤ M.B.U i ⊓ mchart c') (u i c'))) (h2 : (∀ i (c' c'' : ∀ k, Bk n k),
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c') (u i c') =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ M.B.U i ⊓ mchart c'') (u i c'') *
        ∏ k, blockUnit (c' k) (c'' k) (fun _ hx =>
          ⟨mchart_le c' k hx.2.1, mchart_le c'' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c' ⊓ mchart c'') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c' k) ⊓ chart ℤ (n k) (c'' k))) ^ a k))
    (ex : ∀ (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z)
    (uniq : ∀ (z : (Σ k, Bk n k) → ℂ) (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y') :
    IsHermRep M (lineOf M a u h1 h2 ex uniq) :=
  ⟨u, h1, h2, fun i c _ _ hy hi => hOf_eq M a u h1 h2 uniq hy i c hi⟩

end Metric

theorem exists_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)), IsTwB M →
    ∃ A : Geo.HermLine (Bk n), IsHermRep M A := by
  intro m n M hM
  obtain ⟨c, t, ⟨hw⟩⟩ := hM
  obtain ⟨u, h1, h2⟩ := GlobalTheory.CompanionTheory.MPDict.TwUnits.exists_units m n M.B c t M.isLB hw
  exact ⟨_, isHermRep_lineOf M _ u h1 h2 (GlobalTheory.CompanionTheory.MPDict.UnderExists.exists_isUnder m n) (GlobalTheory.CompanionTheory.MPDict.isUnder_unique m n)⟩

end GlobalTheory.CompanionTheory.MPDict.HermRep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdNormPull
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PullRep

def plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ := (res h).comp (pullU f U)

theorem res_plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W V : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (l : V ≤ W) (x : Γ(X, U)ˣ) : res l (plU f h x) = plU f (l.trans h) x :=
  Units.ext (resG_appLE f h l (x : Γ(X, U)))

theorem plU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (l : U' ≤ U)
    (h : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) : plU f h (res l x) = plU f (h.trans (f.preimage_mono l)) x :=
  Units.ext (appLE_resG f l h (x : Γ(X, U)))

theorem plU_plU {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    plU g h' (plU f h x) = plU (g ≫ f) (h'.trans (g.preimage_mono h)) x :=
  Units.ext (appLE_appLE g f h h' (x : Γ(X, U)))

theorem lbPull_g {X Y : Scheme.{0}} (B : LB X) (f : Y ⟶ X) (i j : PUnit → B.ι) :
    (B.pull f).g i j = plU f (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => f) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le B (fun _ => f) j PUnit.unit)) :
        (B.pull f).U i ⊓ (B.pull f).U j ≤ f ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (j PUnit.unit)))
      (B.g (i PUnit.unit) (j PUnit.unit)) := by
  show ∏ k : PUnit, (plU f _ (B.g (i k) (j k))) ^ ((fun _ => (1 : ℤ)) k) = _
  rw [Fintype.prod_unique]
  exact zpow_one _

variable {n' m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev qq (n' m : ℕ) (n : Fin (m + 1) → ℕ) : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n

theorem qq_str (n' m : ℕ) (n : Fin (m + 1) → ℕ) : qq n' m n ≫ mpStr ℤ m n = mpStr ℤ (m + 1) (consN n' n) :=
  qpSnd_str n' m n

def tl (c : ∀ k, Bk (consN n' n) k) : ∀ k, Bk n k := fun k => c k.succ

theorem mchart_le_pull (c : ∀ k, Bk (consN n' n) k) :
    mchart c ≤ qq n' m n ⁻¹ᵁ mchart (tl c) :=
  fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ

theorem pullDeg_zero (a : Fin (m + 1) → ℤ) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a 0 = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨k, hk⟩
    exact Fin.succ_ne_zero k hk

theorem pullDeg_succ (a : Fin (m + 1) → ℤ) (k : Fin (m + 1)) :
    pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k.succ = a k :=
  (Fin.succ_injective _).extend_apply _ _ _

theorem blockUnit_succ {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {W₀ : (MP ℤ m n).Opens} (h : W ≤ prB (consN n' n) k.succ ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (H : W ≤ qq n' m n ⁻¹ᵁ W₀) (h₀ : W₀ ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    blockUnit (n := consN n' n) (k := k.succ) i j h = plU (qq n' m n) H (blockUnit i j h₀) :=
  (plU_plU (qq n' m n) (prB n k) h₀ H _).symm

theorem prod_blockUnit (c c' : ∀ k, Bk (consN n' n) k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {V : (MP ℤ m n).Opens} (HV : W ≤ qq n' m n ⁻¹ᵁ V) (hW : W ≤ mchart c ⊓ mchart c')
    (hV : V ≤ mchart (tl c) ⊓ mchart (tl c')) (a : Fin (m + 1) → ℤ) :
    ∏ k, blockUnit (c k) (c' k) (fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩ :
        W ≤ prB (consN n' n) k ⁻¹ᵁ (chart ℤ (consN n' n k) (c k) ⊓ chart ℤ (consN n' n k) (c' k))) ^
          pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      plU (qq n' m n) HV (∏ k, blockUnit (tl c k) (tl c' k)
        (fun _ hx => ⟨mchart_le (tl c) k (hV hx).1, mchart_le (tl c') k (hV hx).2⟩ :
          V ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (tl c k) ⊓ chart ℤ (n k) (tl c' k))) ^ a k) := by
  rw [map_prod, Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, pullDeg_succ]
  exact congrArg (· ^ a k) (blockUnit_succ _ _ _ HV _)

theorem prod_norm_pull (z : (Σ k, Bk (consN n' n) k) → ℂ) (c : ∀ k, Bk (consN n' n) k) (a : Fin (m + 1) → ℤ) :
    ∏ k, ‖z ⟨k, c k⟩‖ ^ pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      ∏ k, ‖z (sv n' n ⟨k, tl c k⟩)‖ ^ a k := by
  rw [Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  simp only [pullDeg_succ]
  rfl

theorem isUnder_map {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {z' : (Σ k, Bk (consN n' n) k) → ℂ}
    (h : IsUnder y' z') :
    IsUnder (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') (fun p => z' (sv n' n p)) := by
  intro k i
  refine ⟨(h k.succ i).1, fun j hy => ?_⟩
  have e := (h k.succ i).2 j hy
  calc CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j)
        (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y')
      = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          ((qq n' m n).app _ (pullRatio (prB n k) _ i le_rfl j)) y' :=
        (ev_app (qq n' m n) (qq_str n' m n) _ _ y').symm
    _ = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          (pullRatio (qq n' m n ≫ prB n k) _ i le_rfl j) y' := by
        rw [Scheme.Hom.app_eq_appLE, appLE_pullRatio]
    _ = _ := e

theorem ev_plU {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {U : (MP ℤ m n).Opens}
    {W : (MP ℤ (m + 1) (consN n' n)).Opens} (H : W ≤ qq n' m n ⁻¹ᵁ U)
    (hy : y' ∈ ptsIn (mpStr ℤ (m + 1) (consN n' n)) σ₀ W) (x : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ W (plU (qq n' m n) H x : Γ(MP ℤ (m + 1) (consN n' n), W)) y' =
      CxPts.ev (mpStr ℤ m n) σ₀ U (x : Γ(MP ℤ m n, U)) (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') :=
  (ev_res H hy _).trans (ev_app (qq n' m n) (qq_str n' m n) U _ y')

end GlobalTheory.CompanionTheory.MPDict.PullRep

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.CompanionTheory.MPDict.PullRep

theorem isHermRep_pull (n' m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n))
    (hM : IsHermRep M A) :
    IsHermRep (m := m + 1) (n := consN n' n) (M.pull (qpSnd n' m n) (qpSnd_str n' m n)) (pullLine n' A) := by
  show IsHermRep (M.pull (qq n' m n) (qq_str n' m n)) (pullLine n' A)
  obtain ⟨u, h1, h2, h3⟩ := hM
  have Hu : ∀ (i : PUnit → M.B.ι) (c : ∀ k, Bk (consN n' n) k),
      (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓ mchart c ≤
        qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) := fun i c x hx =>
    ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2⟩
  refine ⟨fun i c => plU (qq n' m n) (Hu i c) (u (i PUnit.unit) (tl c)), ?_, ?_, ?_⟩
  · intro i j c
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (M.pull (qq n' m n) (qq_str n' m n)).B.U j ⊓ mchart c ≤
          qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ M.B.U (j PUnit.unit) ⊓ mchart (tl c)) := fun x hx =>
      ⟨⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1.1,
        LB.wchart_le M.B (fun _ => qq n' m n) j PUnit.unit hx.1.2⟩, mchart_le_pull c hx.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h1 (i PUnit.unit) (j PUnit.unit) (tl c))
    rw [map_mul, plU_res, plU_res, plU_res] at e
    exact (res_plU _ _ _ _).trans (e.trans (congrArg₂ (· * ·)
      ((congrArg (Semi.res _) (lbPull_g M.B (qq n' m n) i j)).trans (res_plU _ _ _ _)).symm
      (res_plU _ _ _ _).symm))
  · intro i c c'
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (mchart c ⊓ mchart c') ≤ qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ (mchart (tl c) ⊓ mchart (tl c'))) :=
      fun x hx => ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2.1,
        mchart_le_pull c' hx.2.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h2 (i PUnit.unit) (tl c) (tl c'))
    rw [map_mul, plU_res, plU_res] at e
    rw [res_plU, res_plU]
    refine e.trans (congrArg₂ (· * ·) rfl ?_)
    exact (prod_blockUnit c c' HV (fun _ hx => hx.2) (fun _ hx => hx.2) A.a).symm
  · intro i c y z hz hy
    have hy0 : Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y ∈
        ptsIn (mpStr ℤ m n) σ₀ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) :=
      Points.le_preimage_comp y.1 (qq n' m n) (Hu i c) hy
    have e := h3 (i PUnit.unit) (tl c) _ _ (isUnder_map hz) hy0
    have ev_e := ev_plU (Hu i c) hy (u (i PUnit.unit) (tl c))
    have φ_e := (M.φ σ₀).pull_φ (qq n' m n) (qq_str n' m n) i y
    show A.h (fun p => z (sv n' n p)) = _
    rw [e]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_norm_pull z c A.a).symm ?_) ?_
    · exact congrArg (‖·‖) ev_e.symm
    · exact congrArg (fun t => Real.exp (t / 2)) φ_e.symm

end GlobalTheory.CompanionTheory.MPDict
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict
open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem charZero_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} {e : ℕ} (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    CharZero ((MP ℤ (m + 1) (consN n' n)).residueField (j (genericPoint Y))) := by
  haveI h0 : CharZero Γ(Y, ⊤) := hvar.charZero
  have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
      (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
    (Y.residue (genericPoint Y)).hom.injective.comp (germ_injective_of_isIntegral Y _ _)
  haveI h1 : CharZero (Y.residueField (genericPoint Y)) := charZero_of_injective_ringHom hinj
  exact (RingHom.charZero_iff (j.residueFieldMap (genericPoint Y)).hom.injective).2 h1

theorem charZero_image (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [hx : CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)] :
    CharZero ((MP ℤ m n).residueField (qpSnd n' m n x)) := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  exact (RingHom.charZero_iff (F.residueFieldMap x).hom.injective).2 hx

theorem dim_closure_genericPt {n' m : ℕ} {n : Fin (m + 1) → ℕ} {Y : Scheme.{0}} [IsIntegral Y]
    {j : Y ⟶ MP ℤ (m + 1) (consN n' n)} [IsClosedImmersion j] {e : ℕ}
    (hvar : GlobalTheory.IsArithVar (j ≫ qpStr n' m n) e) :
    topologicalKrullDim (closure ({j (genericPoint Y)} : Set (MP ℤ (m + 1) (consN n' n)))) = ((e + 1 : ℕ) : _) := by
  have hrange : Set.range j = closure {j (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Y).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact (topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange).trans hvar.dim_eq

end GlobalTheory.CompanionTheory.MPDict
