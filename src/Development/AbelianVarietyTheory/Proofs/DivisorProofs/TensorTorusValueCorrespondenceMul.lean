module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem cube_corr {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (xi xj yi yj ui uj : A) (sji sij tji tij : U) :
    sji * tji / θ xi yj uj * (sij * tij / θ xj yi ui) /
        (θ xj (yj * uj) xi * θ xj (yj * uj) (yi * ui) * θ xi (yi * ui) (xj * (yj * uj))) *
      (θ (xi * xj) (yi * yj) (ui * uj) / (θ xi yi ui * θ xj yj uj)) =
    sji * sij / (θ xj yj xi * θ xj yj yi * θ xi yi (xj * yj)) *
      (tji * tij / (θ xj uj xi * θ xj uj ui * θ xi ui (xj * uj))) := by
  have hp : ∀ x y z, θ x y z = θ y x z ∧ θ x y z = θ x z y ∧ θ x y z = θ z x y ∧ θ x y z = θ y z x ∧
      θ x y z = θ z y x := fun x y z =>
    ⟨h.s01 x y z, h.s12 x y z, (h.s12 x y z).trans (h.s01 x z y), (h.s01 x y z).trans (h.s12 y x z),
      ((h.s01 x y z).trans (h.s12 y x z)).trans (h.s01 y z x)⟩
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have c0 := E (show θ (xi * xj) (yi * yj) (ui * uj) * θ xi xj (ui * uj) = θ xi (xj * yi * yj) (ui * uj) * θ xj (yi * yj) (ui * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * yj) (ui * uj))
  have c1 := E (show θ (xj * ui) uj (yi * yj) * θ xj ui (yi * yj) = θ xj (ui * uj) (yi * yj) * θ ui uj (yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui uj (yi * yj))
  have c2 := E (show θ (xj * ui) (yi * yj) uj * θ xj ui uj = θ xj (yi * yj * ui) uj * θ ui (yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj ui (yi * yj) uj)
  have c3 := E (show θ (xj * yj) uj (yi * ui) * θ xj yj (yi * ui) = θ xj (yj * uj) (yi * ui) * θ yj uj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj uj (yi * ui))
  have c4 := E (show θ (xj * yj) (yi * ui) uj * θ xj yj uj = θ xj (yi * yj * ui) uj * θ yj (yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yj (yi * ui) uj)
  have c5 := E (show θ (xj * yi) ui yj * θ xj yi yj = θ xj (yi * ui) yj * θ yi ui yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi ui yj)
  have c6 := E (show θ (xj * yi) yj ui * θ xj yi ui = θ xj (yi * yj) ui * θ yi yj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xj yi yj ui)
  have c7 := E (show θ (xi * xj) (yj * uj) (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj * uj) (yi * ui) * θ xj (yj * uj) (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yj * uj) (yi * ui))
  have c8 := E (show θ (xi * xj) (yi * ui) (yj * uj) * θ xi xj (yj * uj) = θ xi (xj * yi * ui) (yj * uj) * θ xj (yi * ui) (yj * uj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) (yj * uj))
  have c9 := E (show θ (xi * ui) uj (xj * yi * yj) * θ xi ui (xj * yi * yj) = θ xi (ui * uj) (xj * yi * yj) * θ ui uj (xj * yi * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj (xj * yi * yj))
  have c10 := E (show θ (xi * ui) (xj * yi * yj) uj * θ xi ui uj = θ xi (xj * yi * yj * ui) uj * θ ui (xj * yi * yj) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui (xj * yi * yj) uj)
  have c11 := E (show θ (xi * yj) uj (xj * yi * ui) * θ xi yj (xj * yi * ui) = θ xi (yj * uj) (xj * yi * ui) * θ yj uj (xj * yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj uj (xj * yi * ui))
  have c12 := E (show θ (xi * yj) (xj * yi * ui) uj * θ xi yj uj = θ xi (xj * yi * yj * ui) uj * θ yj (xj * yi * ui) uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yj (xj * yi * ui) uj)
  have c13 := E (show θ (xi * ui) uj xj * θ xi ui xj = θ xi (ui * uj) xj * θ ui uj xj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui uj xj)
  have c14 := E (show θ (xi * ui) xj uj * θ xi ui uj = θ xi (xj * ui) uj * θ ui xj uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi ui xj uj)
  have c15 := E (show θ (xi * xj) uj ui * θ xi xj ui = θ xi (xj * uj) ui * θ xj uj ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj uj ui)
  have c16 := E (show θ (xi * xj) ui uj * θ xi xj uj = θ xi (xj * ui) uj * θ xj ui uj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj ui uj)
  have c17 := E (show θ (xi * yi) ui (xj * yj) * θ xi yi (xj * yj) = θ xi (yi * ui) (xj * yj) * θ yi ui (xj * yj) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi ui (xj * yj))
  have c18 := E (show θ (xi * yi) (xj * yj) ui * θ xi yi ui = θ xi (xj * yi * yj) ui * θ yi (xj * yj) ui by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi yi (xj * yj) ui)
  have c19 := E (show θ (xi * xj) (yi * ui) yj * θ xi xj yj = θ xi (xj * yi * ui) yj * θ xj (yi * ui) yj by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj (yi * ui) yj)
  have c20 := E (show θ (xi * xj) yj (yi * ui) * θ xi xj (yi * ui) = θ xi (xj * yj) (yi * ui) * θ xj yj (yi * ui) by
    simpa only [mul_comm, mul_assoc, mul_left_comm] using h.coc xi xj yj (yi * ui))
  have p0 := E (hp xj (yj * uj) xi).2.2.1
  have p1 := E (hp xj yj xi).2.2.1
  have p2 := E (hp xj yj yi).2.1
  have p3 := E (hp xj uj xi).2.2.1
  have p4 := E (hp (xj * ui) uj (yi * yj)).2.2.1
  have p5 := E (hp xj ui (yi * yj)).2.1
  have p6 := E (hp xj (ui * uj) (yi * yj)).2.1
  have p7 := E (hp ui uj (yi * yj)).2.2.1
  have p8 := E (hp (xj * ui) (yi * yj) uj).1
  have p9 := E (hp ui (yi * yj) uj).1
  have p10 := E (hp (xj * yj) uj (yi * ui)).2.1
  have p11 := E (hp yj uj (yi * ui)).2.1
  have p12 := E (hp (xj * yi) ui yj).2.1
  have p13 := E (hp xj (yi * ui) yj).2.1
  have p14 := E (hp yi ui yj).2.1
  have p15 := E (hp (xi * xj) (yj * uj) (yi * ui)).2.1
  have p16 := E (hp xi (xj * yj * uj) (yi * ui)).2.1
  have p17 := E (hp xj (yj * uj) (yi * ui)).2.1
  have p18 := E (hp (xi * ui) uj (xj * yi * yj)).2.2.1
  have p19 := E (hp xi ui (xj * yi * yj)).2.1
  have p20 := E (hp xi (ui * uj) (xj * yi * yj)).2.1
  have p21 := E (hp ui uj (xj * yi * yj)).2.2.1
  have p22 := E (hp (xi * ui) (xj * yi * yj) uj).1
  have p23 := E (hp ui (xj * yi * yj) uj).1
  have p24 := E (hp (xi * yj) uj (xj * yi * ui)).2.1
  have p25 := E (hp xi (yj * uj) (xj * yi * ui)).2.1
  have p26 := E (hp yj uj (xj * yi * ui)).2.1
  have p27 := E (hp (xi * ui) uj xj).2.2.1
  have p28 := E (hp xi ui xj).2.1
  have p29 := E (hp xi (ui * uj) xj).2.1
  have p30 := E (hp ui uj xj).2.2.1
  have p31 := E (hp (xi * ui) xj uj).1
  have p32 := E (hp ui xj uj).1
  have p33 := E (hp (xi * xj) uj ui).2.1
  have p34 := E (hp xi (xj * uj) ui).2.1
  have p35 := E (hp (xi * yi) ui (xj * yj)).2.1
  have p36 := E (hp xi (yi * ui) (xj * yj)).2.1
  have p37 := E (hp yi ui (xj * yj)).2.1
  have p38 := E (hp (xi * xj) (yi * ui) yj).2.1
  have p39 := E (hp xi (xj * yi * ui) yj).2.1
  rw [← mul_assoc xj yj uj]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) c0 - c1 + c2 + c3 - c4 + c5 - c6 + c7 - c8 - c9 + c10 + c11 - c12 + c13 - c14 - c15 + c16 + c17 - c18 + c19 - c20 - p0 + p1 + p2 + p3 + p4 + p5 - p6 - p7 - p8 + p9 - p10 + p11 - p12 + 2 • p13 + p14 - p15 + p16 + p17 + p18 + p19 - p20 - p21 - p22 + p23 - p24 + p25 + p26 - p27 - p28 + p29 + p30 + p31 - p32 + p33 - p34 - p35 + p36 + p37 - p38 + p39

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem vmul_comb {U : Type} [CommGroup U] (s1 s2 t P1 P2 P Q wc wb wb' wcb wcb' wbb' wcbb' w1 : U)
    (h1 : s1 * wc * wb = P1 * wcb * w1) (h2 : s2 * wc * wb' = P2 * wcb' * w1)
    (h3 : t * wcbb' * wc * wb * wb' = Q * wcb * wcb' * wbb' * w1) (h4 : P * Q = P1 * P2) :
    s1 * s2 / t * wc * wbb' = P * wcbb' * w1 := by
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a1 := E h1; have a2 := E h2; have a3 := E h3; have a4 := E h4
  simp only [ofMul_mul, ofMul_div] at *
  linear_combination (norm := abel) a1 + a2 - a3 - a4

theorem gtRelV_mul : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv →
    ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us) := by
  intro F _ N N' r W φ e wv hT v' u' vs us hv hu
  obtain ⟨hφ, -, -, -, hφc, hw0, hcub, -⟩ := hT
  refine ⟨fun j => ?_, fun χ' => ?_⟩
  · show φ (v'.b * u'.b) j = (vs j).b * (us j).b
    rw [hφ, hv.1, hu.1]
  · let w : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
    let Pf : (Fin r → N.Gt) → Fˣ := fun g => ∏ i, ∏ j, ((g j).s (e χ' i) * (g i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (g j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (g j).b (g i).b *
        N.θ (N.c (e χ' i)) (g i).b (N.c (e χ' j) * (g j).b))) ^ W i j
    let Qf : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) ((us i).b * (us j).b) /
      (N.θ (N.c (e χ' i)) (vs i).b (us i).b * N.θ (N.c (e χ' j)) (vs j).b (us j).b)) ^ W i j
    have h1 : v'.s χ' * w (N'.c χ') * w v'.b = Pf vs * w (N'.c χ' * v'.b) * w 1 := Units.ext (hv.2 χ')
    have h2 : u'.s χ' * w (N'.c χ') * w u'.b = Pf us * w (N'.c χ' * u'.b) * w 1 := Units.ext (hu.2 χ')
    have h3 := hcub (N'.c χ') v'.b u'.b
    rw [mul_assoc (N'.c χ') v'.b u'.b] at h3
    simp only [hφc, hv.1, hu.1] at h3
    have h3' : N'.θ (N'.c χ') v'.b u'.b * w (N'.c χ' * (v'.b * u'.b)) * w (N'.c χ') * w v'.b * w u'.b =
        Qf * w (N'.c χ' * v'.b) * w (N'.c χ' * u'.b) * w (v'.b * u'.b) * w 1 := Units.ext h3
    have h4 : Pf (vs * us) * Qf = Pf vs * Pf us := by
      simp only [Pf, Qf]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow]
      exact congrArg (· ^ W i j) (cube_corr N.cub (N.c (e χ' i)) (N.c (e χ' j)) (vs i).b (vs j).b (us i).b (us j).b
        ((vs j).s (e χ' i)) ((vs i).s (e χ' j)) ((us j).s (e χ' i)) ((us i).s (e χ' j)))
    exact congrArg Units.val (vmul_comb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3' h4)

end GlobalTheory.Mum.TensTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_mul : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us → GtRelV W φ e wv (v' * u') (vs * us) := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_mul | exact GlobalTheory.Mum.TensTor.gtRelV_mul | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairs
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeStep

section Gens

variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def zpowGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ) :
    LB.Gen (LB.LinComb L φ (fun k => n * ε k)) where
  s := fun j => t.s j ^ n

theorem zpowGen_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    (zpowGen L φ ε t n).IsGen := fun i j => by
  refine ((map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans (mul_zpow _ _ _))).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)
  exact (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun k _ =>
    (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _)))

theorem val_zpowGen {Z : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℤ)
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) : val (zpowGen L φ ε t n) r z J = val t r z J ^ n :=
  map_zpow _ _ _

theorem finProdGen_isGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProdGen {I : Type} [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Gens

theorem prod_zpow_mul {K U : Type} [Fintype K] [CommGroup U] (f : K → U) (e : K → ℤ) (n : ℤ) :
    ∏ k, f k ^ (n * e k) = (∏ k, f k ^ e k) ^ n := by
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem prod_finset_fin_two_ulift_expand {U : Type} [CommMonoid U] (f : ULift.{0} (Finset (Fin 2)) → U) :
    ∏ I, f I = f ⟨{0, 1}⟩ * f ⟨{0}⟩ * f ⟨{1}⟩ * f ⟨∅⟩ := by
  refine (Fintype.prod_equiv Equiv.ulift f (fun I => f ⟨I⟩) (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  ac_rfl

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

theorem groupSchemePartialSum_pair_both : psum B' (x2 B') {0, 1} = fst B' B' * snd B' B' := congrArg (fst B' B' * ·) (_root_.mul_one _)
theorem psum0 : psum B' (x2 B') {0} = fst B' B' := _root_.mul_one _
theorem psum1 : psum B' (x2 B') {1} = snd B' B' := _root_.mul_one _
theorem psumE : psum B' (x2 B') ∅ = 1 := rfl

theorem pair_eq {r : ℕ} (pr : Fin r → (B' ⟶ B)) (hpr : ∀ i, IsMonHom (pr i)) (w : ℤ) (i j : Fin r) {U : Type}
    [CommGroup U] (h : ((G2 B').left ⟶ B.left) → U) :
    ∏ k : thK.{0} ⊕ (thK.{0} ⊕ thK.{0}), h (Sum.elim
      (fun k => (lift (fst B' B' ≫ pr i) (lift (snd B' B' ≫ pr i) ((fst B' B' ≫ pr j) * (snd B' B' ≫ pr j)))).left ≫
        thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (fst B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr j) (lift (snd B' B' ≫ pr j) (snd B' B' ≫ pr i))).left ≫ thφ B (x3 B) k)) k) ^
      (-w * Sum.elim thε (Sum.elim thε thε) k) =
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr i) (snd B' B' ≫ pr j) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr j) (snd B' B' ≫ pr i) k) ^ Oε k) ^ w *
    (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
      h ((psum B' (x2 B') I.down).left ≫ tensφ pr ((i, j), k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-w) := by
  haveI := hpr i
  haveI := hpr j
  refine (prod_zpow_mul (U := U) _ (Sum.elim thε (Sum.elim thε thε)) (-w)).trans ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [prod_cub, prod_cub, prod_cub]
  simp only [prod_finset_fin_two_ulift_expand, Fin.prod_univ_four, GlobalTheory.PolDeg.lamPts, tensφ, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, groupSchemePartialSum_pair_both, psum0, psum1, psumE]
  have q2 : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  have q0 : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q1 : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have qe : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  simp only [q2, q0, q1, qe, ← Over.comp_left, MonObj.comp_mul, MonObj.mul_comp, MonObj.one_comp, MonObj.comp_one,
    _root_.mul_one, _root_.one_mul]
  generalize fst B' B' ≫ pr i = a
  generalize snd B' B' ≫ pr i = b
  generalize fst B' B' ≫ pr j = c
  generalize snd B' B' ≫ pr j = d
  rw [mul_comm (c * d) a, mul_comm c a, mul_comm d a, mul_comm (c * d) b, mul_comm d b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum.CubeStep

variable {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']

def lamV {T : Over S} {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) (u v : T ⟶ B) : U :=
  ∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts u v k) ^ Oε k

def pairGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B))
    (p : Fin r × Fin r) :=
  zpowGen L.L _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε cb.t
      (lift (fst B' B' ≫ pr p.1) (lift (snd B' B' ≫ pr p.1) ((fst B' B' ≫ pr p.2) * (snd B' B' ≫ pr p.2)))).left)
    (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (fst B' B' ≫ pr p.1))).left)
      (LB.pullGen L.L (thφ B (x3 B)) thε cb.t (lift (fst B' B' ≫ pr p.2) (lift (snd B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1))).left)))
    (-W p.1 p.2)

theorem pairGen_isGen {L : RigLB B} (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (pr : Fin r → (B' ⟶ B)) (p : Fin r × Fin r) : (pairGen cb W pr p).IsGen :=
  zpowGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ cb.isGen _) (DVR.pullGen_isGen _ _ _ _ cb.isGen _))) _

end GlobalTheory.Mum.CubeStep

namespace GlobalTheory.Mum


open CubeStep in
theorem cube_step : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  intro S B B' _ _ _ _ L cb r W pr hpr
  have hfe : FormEq (fun q : (Fin r × Fin r) × (thK.{0} ⊕ (thK.{0} ⊕ thK.{0})) => Sum.elim
      (fun k => (lift (fst B' B' ≫ pr q.1.1) (lift (snd B' B' ≫ pr q.1.1)
        ((fst B' B' ≫ pr q.1.2) * (snd B' B' ≫ pr q.1.2)))).left ≫ thφ B (x3 B) k)
      (Sum.elim (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (fst B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)
        (fun k => (lift (fst B' B' ≫ pr q.1.2) (lift (snd B' B' ≫ pr q.1.2) (snd B' B' ≫ pr q.1.1))).left ≫
          thφ B (x3 B) k)) q.2)
      (fun q => -W q.1.1 q.1.2 * Sum.elim thε (Sum.elim thε thε) q.2)
      (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2)
        (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2))
      (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2)
        (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2))) := by
    intro U _ h
    have h1 : ∏ q : (Fin r × Fin r) × Fin 4,
        h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr q.1.1) (snd B' B' ≫ pr q.1.2) q.2) ^ ((W + W.transpose) q.1.1 q.1.2 * Oε q.2) =
        (∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ Oε k) ^
          W p.1 p.2) *
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.2) (snd B' B' ≫ pr p.1) k) ^ Oε k) ^
          W p.1 p.2 := by
      calc _ = ∏ p : Fin r × Fin r, ∏ k : Fin 4,
            h (GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) k) ^ ((W + W.transpose) p.1 p.2 * Oε k) :=
          Fintype.prod_prod_type _
        _ = ∏ p : Fin r × Fin r, (lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.1 p.2 *
            lamV h (fst B' B' ≫ pr p.1) (snd B' B' ≫ pr p.2) ^ W p.2 p.1) :=
          Finset.prod_congr rfl fun p _ => by
            rw [prod_zpow_mul, Matrix.add_apply, Matrix.transpose_apply, zpow_add]; rfl
        _ = _ := by
          rw [Finset.prod_mul_distrib]
          exact congrArg _ (Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun _ => rfl)
    have h2 : ∏ q : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4),
        h ((psum B' (x2 B') q.1.down).left ≫ tensφ pr q.2) ^ (-((-1) ^ (2 - q.1.down.card) * tensε W q.2)) =
        ∏ p : Fin r × Fin r, (∏ k : Fin 4, ∏ I : ULift.{0} (Finset (Fin 2)),
          h ((psum B' (x2 B') I.down).left ≫ tensφ pr (p, k)) ^ ((-1) ^ (2 - I.down.card) * Oε k)) ^ (-W p.1 p.2) := by
      rw [Fintype.prod_prod_type, Finset.prod_comm, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← zpow_mul]
      congr 1
      simp only [tensε]
      ring
    refine (Fintype.prod_prod_type _).trans (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) h1 h2)).symm)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => pair_eq pr hpr (W p.1 p.2) p.1 p.2 h
  obtain ⟨t, ht, hv⟩ := exists_gen L.isLB hfe (GeneratorPullback.finProdGen L.L _ _ (pairGen cb W pr))
    (finProdGen_isGen _ _ _ _ (pairGen_isGen cb W pr))
  refine ⟨t, ht, fun T ρ z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_finProdGen _ _ _ (pairGen cb W pr) _ _ hJ).trans
    ((Fintype.prod_prod_type _).trans ?_))
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only [pairGen]
  refine (val_zpowGen _ _ _ _ _ _ _ _).trans (congrArg (· ^ (-W i j)) ?_)
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_cub cb ρ hJ _ _ _) (val_cub cb ρ hJ _ _ _))))).trans ?_
  rw [MonObj.comp_mul, ← _root_.mul_assoc]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeStepGeneratorTensorPowerPairsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubeStep_generator_tensorPowerPairs : ∀ {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (L : RigLB B) (cb : CubicalStr B L) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (B' ⟶ B)), (∀ i, IsMonHom (pr i)) → ∃ c : LB.Gen (LB.LinComb L.L (Sum.elim (fun k : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (fst B' B' ≫ pr k.1.1) (snd B' B' ≫ pr k.1.2) k.2) (fun p : ULift.{0} (Finset (Fin 2)) × ((Fin r × Fin r) × Fin 4) => (psum B' (x2 B') p.1.down).left ≫ tensφ pr p.2)) (Sum.elim (fun k => (W + W.transpose) k.1.1 k.1.2 * Oε k.2) (fun p => -((-1) ^ (2 - p.1.down.card) * tensε W p.2)))), c.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ G2 B') (z : T.left) (J : (T.left ⟶ B.left) → L.L.ι), Good L.L z J → val c ρ.left z J = ∏ i, ∏ j, (cubV cb z J (ρ ≫ fst B' B' ≫ pr i) (ρ ≫ snd B' B' ≫ pr i) ((ρ ≫ fst B' B' ≫ pr j) * (ρ ≫ snd B' B' ≫ pr j)) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ fst B' B' ≫ pr i) * cubV cb z J (ρ ≫ fst B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr j) (ρ ≫ snd B' B' ≫ pr i)) ^ (-W i j) := by
  exact @GlobalTheory.Mum.cube_step
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalMul

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PsiEvenPull

theorem exists_isPullDeg_of_val {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {i : R →+* R'} (hi : Function.Injective i) (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (s : (TK R).left ⟶ W.toScheme) (hs : s ≫ W.ι = jK R)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap hi) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R :=
    ⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩
  have hg : g ≫ W.ι = jK R' ≫ specOf i := sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧
      lam ≫ (jK R ∣_ W) = g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem exists_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hi : Function.Injective i) (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
  have hji : Function.Injective (j.comp i) := hj.comp hi
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift hi p
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_val hji D D'' p.psiW s hs gp w (T.pgen_comp D'.P.isLB g₁ g₂) hr
    (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
      have s' : genMap hj ≫ jK R' ≫ spMap i = genMap hji ≫ jK R :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sj.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) sc).trans ((Category.id_comp _).symm.trans (fracMap_sq hji)))))
      have v₁ := psi_val p _ _ s' hJ hJ' (q.xe x)
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

def Sq {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} (h : Y' ⟶ Y)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
    F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
    Geo.Tor.gw wM (r ≫ p') z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL') =
      Geo.Tor.gw w (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ f') z jL jL'

theorem Sq.comp {X X' X'' G G' G'' Y Y' Y'' : Scheme.{0}} {M : LB X} {M' : LB X'} {M'' : LB X''} {L : LB G} {L' : LB G'}
    {L'' : LB G''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {B : G' ⟶ G} {B' : G'' ⟶ G'} {p : Y ⟶ X} {p' : Y' ⟶ X'} {p'' : Y'' ⟶ X''}
    {f : Y ⟶ G} {f' : Y' ⟶ G'} {f'' : Y'' ⟶ G''} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
    {wM : LB.Iso M' (M.pull F)} {wM' : LB.Iso M'' (M'.pull F')} {wM'' : LB.Iso M'' (M.pull (F' ≫ F))}
    {wL : LB.Iso L' (L.pull B)} {wL' : LB.Iso L'' (L'.pull B')} {wL'' : LB.Iso L'' (L.pull (B' ≫ B))}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {w'' : LB.Iso (L''.pull f'') (M''.pull p'')}
    (hM : M'.IsLB) (hL : L'.IsLB) (TM : Tri wM wM' wM'') (TL : Tri wL wL' wL'')
    (hf : h' ≫ f' = f'' ≫ B') (hp : p'' ≫ F' = h' ≫ p') (H : Sq h wM wL w w') (H' : Sq h' wM' wL' w' w'') :
    Sq (h' ≫ h) wM'' wL'' w w'' := by
  intro Z r z jM jM'' jL jL'' h₁ h₂ h₃ h₄
  have ef : f' (h' (r z)) = B' (f'' (r z)) := congrArg (fun g => g (r z)) hf
  have ep : p' (h' (r z)) = F' (p'' (r z)) := congrArg (fun g => g (r z)) hp.symm
  obtain ⟨jM', m⟩ := exists_chart hM (F' (p'' (r z)))
  obtain ⟨jL', l⟩ := exists_chart hL (B' (f'' (r z)))
  have a := H Z (r ≫ h') z jM jM' jL jL' (by show F (p' (h' (r z))) ∈ _; rw [ep]; exact h₁)
    (by show p' (h' (r z)) ∈ _; rw [ep]; exact m) (by show B (f' (h' (r z))) ∈ _; rw [ef]; exact h₃)
    (by show f' (h' (r z)) ∈ _; rw [ef]; exact l)
  have b := H' Z r z jM' jM'' jL' jL'' m h₂ l h₄
  have c := TM Z (r ≫ p'') z jM jM' jM'' h₁ m h₂
  have d := TL Z (r ≫ f'') z jL jL' jL'' h₃ l h₄
  rw [Category.assoc, hp, ← Category.assoc] at c
  rw [Category.assoc, ← hf, ← Category.assoc] at d
  rw [c, d, _root_.mul_assoc, b, ← _root_.mul_assoc, a, _root_.mul_assoc, Category.assoc]

theorem isPullUnif_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {I : Ideal R} {I' : Ideal R'} {I'' : Ideal R''} {i : R →+* R'} {j : R' →+* R''}
    {D : DegData R I} {D' : DegData R' I'} {D'' : DegData R'' I''} {p : IsPullDeg i D.toPre D'.toPre}
    {q : IsPullDeg j D'.toPre D''.toPre} {r : IsPullDeg (j.comp i) D.toPre D''.toPre}
    {w : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull (proj q ≫ proj p))} (r₁ : proj r = proj q ≫ proj p)
    (r₂ : r.xe = q.xe.trans p.xe) (r₃ : HEq r.w w) (T : Tri p.w q.w w)
    {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))} {A'' : PolAV (Sp (FractionRing R''))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {G'' : Over (Sp R'')} [GrpObj G''] [IsCommMonObj G'']
    {b₁ : G' ≅ (Over.pullback (specOf i)).obj G} {b₂ : G'' ≅ (Over.pullback (specOf j)).obj G'}
    {b : G'' ≅ (Over.pullback (specOf (j.comp i))).obj G}
    (hb : b.hom.left ≫ pullback.fst G.hom (specOf (j.comp i)) =
      (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)))
    {U : Unif I D A G} {U' : Unif I' D' A' G'} {U'' : Unif I'' D'' A'' G''}
    (H₁ : IsPullUnif i p b₁ U U') (H₂ : IsPullUnif j q b₂ U' U'') : IsPullUnif (j.comp i) r b U U'' := by
  have sc : specOf j ≫ specOf i = specOf (j.comp i) := (spMap_comp i j).symm
  obtain ⟨w₁, g₁, e₁, m₁, K₁⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₁
  obtain ⟨w₂, g₂, e₂, m₂, K₂⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₂
  replace g₁ := (isGen_iff _).1 g₁
  replace g₂ := (isGen_iff _).1 g₂
  replace m₁ := (maps_iff w₁ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf i) _
    (rigPull_le (G' := G') (G := G) _ (specOf i) e₁ U.LG.L) (fun _ => rfl)).1 m₁
  replace m₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U''.LG.rig U'.LG.rig (specOf j) _
    (rigPull_le (G' := G'') (G := G') _ (specOf j) e₂ U'.LG.L) (fun _ => rfl)).1 m₂
  obtain ⟨wL, TL⟩ := Geo.Tor.exists_comp U'.LG.isLB w₁ w₂ g₁ g₂ U.LG.isLB U''.LG.isLB
  have key : ∀ (Φ : D''.toPre.P.A.left ⟶ D.toPre.P.A.left) (u : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull Φ))
      (xe : D''.toPre.X ≃+ D.toPre.X) (B : G''.left ⟶ G.left), Φ = proj q ≫ proj p → HEq u w → xe = q.xe.trans p.xe →
      B = (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) →
      ∃ wL : LB.Iso U''.LG.L (U.LG.L.pull B), wL.IsGen ∧ ∃ he : eSec G'' ≫ B = specOf (j.comp i) ≫ eSec G,
        LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) U''.LG.rig
          (rigPullOf B (specOf (j.comp i)) he U.LG.L U.LG.rig) ∧
        ∀ e : ℕ, ∃ h : (thickObj R'' I'' e G'').left ⟶ (thickObj R I e G).left,
          h ≫ (fstG I e G).left = (fstG I'' e G'').left ≫ B ∧
          ((U''.gt e).pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D''.toPre.X,
            (∀ κ : Fin 4, D''.toPre.Oφ (U''.gt e).pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧
            PMaps u (D''.toPre.Oφ (U''.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U''.gt e).t x)
              ((U.gt e).t (xe x)) h) ∧ Sq h u wL (U.w e) (U''.w e) := by
    rintro _ u _ _ rfl hu rfl rfl
    obtain rfl := eq_of_heq hu
    have he : eSec G'' ≫ (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) =
        specOf (j.comp i) ≫ eSec G :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
    have hr := TL.pmaps_comp U'.LG.isLB (fun _ => e₂) m₁ m₂
    rw [sc] at hr
    refine ⟨wL, (isGen_iff _).2 (TL.pgen_comp U'.LG.isLB g₁ g₂), he,
      (maps_iff wL _ (fun _ => eSec G) _ U''.LG.rig U.LG.rig (specOf (j.comp i)) _
        (rigPull_le (G' := G'') (G := G) _ (specOf (j.comp i)) he U.LG.L) (fun _ => rfl)).2 hr, fun e => ?_⟩
    obtain ⟨h₁, f₁, ⟨p₁, t₁⟩, s₁⟩ := K₁ e
    obtain ⟨h₂, f₂, ⟨p₂, t₂⟩, s₂⟩ := K₂ e
    refine ⟨h₂ ≫ h₁, ?_, ⟨?_, fun x => ⟨fun κ => ?_, ?_⟩⟩, Sq.comp D'.toPre.P.isLB U'.LG.isLB T TL f₂ p₂ s₁ s₂⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) f₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) f₂).trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) p₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) p₁).trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((t₂ x).1 κ)).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) ((t₁ (q.xe x)).1 κ)).trans (Category.assoc _ _ _).symm)))
    · exact T.pmaps_comp D'.toPre.P.isLB (t₂ x).1 (t₁ (q.xe x)).2 (t₂ x).2
  exact (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 (key _ r.w r.xe _ r₁ r₃ r₂ hb)

end GlobalTheory.Mum.GalMul

namespace GlobalTheory.Mum

theorem galMap_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ τ : Gal ρ) (a b : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' τ b → GalMap hD U' (σ * τ) (a ≫ b) := by
  intro R _ _ _ _ R' _ _ _ ρ _ D D' hD A' G' _ _ _ U' σ τ a b ⟨ga, q, b₂, ha, H₂, x₂, c₂⟩ ⟨gb, p, b₁, hb, H₁, x₁, c₁⟩
  have gp : IsGrpPullback G' G' (spMap ((Gal.hom σ).comp (Gal.hom τ))) (a ≫ b) :=
    (ga.comp gb).congr (spMap_comp _ _).symm rfl
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp (i := Gal.hom τ) (j := Gal.hom σ) τ.1.injective σ.1.injective p q
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf ((Gal.hom σ).comp (Gal.hom τ))))
  refine ⟨gp, r, bc, hbc, GalMul.isPullUnif_comp r₁ r₂ r₃ T (hbc.trans (by rw [ha, hb])) H₁ H₂, fun x => ?_, ?_⟩
  · exact (congrArg (fun e => e x) r₂).trans ((x₁ _).trans (x₂ x))
  · rintro _ _ rfl rfl
    exact (congrArg (· ≫ _) r₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (c₁ _ _ rfl rfl)).trans (c₂ _ _ rfl rfl)))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ τ : Gal ρ) (a b : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' τ b → GalMap hD U' (σ * τ) (a ≫ b) := by
  first | exact @GlobalTheory.Mum.galMap_mul | exact GlobalTheory.Mum.galMap_mul | (intros; apply GlobalTheory.Mum.galMap_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstGenericAppInjective
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fst_generic_app_injective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (W : X.Opens) : Function.Injective ((pullback.fst p (jK R)).app W).hom := by
  have : IsDominant (jK R) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p (jK R)).flip
  exact (pullback.fst p (jK R)).app_injective W

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem discrep_isAt_eq_neg_mult : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ), 0 < m → IsDivOfForm K η → ∀ (E : DivOver q) (w : Y) (g : Y.functionFieldˣ), E.IsAt w → G.IsEqn w g → discrep E η m g = -((G - m • K).mult w : ℚ) / m := by
  intro k _ _ Y _ _ q n _ η hη K G m hm hK E w g hE hg
  obtain ⟨c, hc⟩ := K.exists_isEqn w
  have h1 := (hg.sub (hc.nsmul m)).mult_eq
  rw [← hE.ord_eq, div_eq_mul_inv, E.ord_mul, E.ord_inv, E.ord_pow] at h1
  have h2 := GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y q n η hη K hK E w hE
  rw [hc.mult_eq, ← hE.ord_eq] at h2
  change E.formOrd η = E.ord c at h2
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, h1, h2]
  push_cast
  field_simp
  ring

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

def IsBC {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X) : Prop :=
  ∃ (ev₀ : R →+* u.V) (_ : IsLocalHom ev₀) (hD : IsPullDeg ev₀ D.toPre u.D.toPre)
    (bc : u.G ≅ (Over.pullback (specOf ev₀)).obj G),
    IsMonHom bc.hom ∧ IsPullUnif ev₀ hD bc U u.U ∧ (∀ χ, hD.xe (ε χ) = χ) ∧
    (∀ r, algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (ev₀ r)) = (ev r : PadicAlgCl p)) ∧
    ∃ t : u.A.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀, t ≫ pullback.fst _ _ = u.φ ∧
      t ≫ FinalForm.φ = genMap u.U ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) ≫ gm

end GlobalTheory.Poinc.TestAtPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPos
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_one_eventually_ge : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a + a') (m * b + b') 1 := by
  intro hA k _ X _ p D hD P a b a' b' M α hRep hAmp hSP hSI ε hε
  obtain ⟨t₀, ht⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hA k X p D hD P a b a' b' M α hRep hAmp hSP hSI
  exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge X.functionField
    (fun m : ℕ => P.H (m * a + a') (m * b + b')) (fun m : ℕ => P.Bl (m * a + a') (m * b + b')) (D + 1)
    (Nat.succ_pos D) (fun m => GlobalTheory.VolBr.Pair.isBallFam k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hD P _ _ R) _ _ t₀ ht ε hε

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPosStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a + a') (m * b + b') 1 := by
  first | exact @GlobalTheory.HSNef.lc_one_eventually_ge | exact GlobalTheory.HSNef.lc_one_eventually_ge | (intros; apply GlobalTheory.HSNef.lc_one_eventually_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtR
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev ptR (χ : D.X) : Spec (CommRingCat.of R) ⟶ D.P.A.left :=
  (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ D.c χ).left

def unitAt {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) :
    (FractionRing R)ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map ((Z.presheaf.germ ⊤ z trivial).hom.comp
    (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)).toMonoidHom

def Reads (κ : D.X → (FractionRing R)ˣ) : Prop :=
  ∃ g : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptR D χ) (fun _ => -1)),
    (∀ χ, (g χ).IsGen) ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (D.psi χ) r z J = unitAt r z (κ χ) * val (g χ) (r ≫ jK R) z J

def lead {X : Type} [AddCommGroup X] (κ : X → (FractionRing R)ˣ) (k : ℕ) (α mu : X) : (FractionRing R)ˣ :=
  κ mu ^ k * (κ (mu + α) * (κ mu)⁻¹ * (κ α)⁻¹)

end GlobalTheory.ThFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastOfIsNilpotent
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem span_natCast_pow_eq_bot_of_isNilpotent (p : ℕ) (R : Type) [CommRing R]
    (h : IsNilpotent (p : R)) : ∃ N : ℕ, Ideal.span {(p : R)} ^ N • (⊤ : Submodule R R) = ⊥ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  rw [Ideal.span_singleton_pow, hN, smul_eq_mul, Ideal.mul_top]
  simp

theorem isAdicComplete_span_natCast_of_isNilpotent :
    ∀ (p : ℕ) (R : Type) [CommRing R], IsNilpotent (p : R) →
      IsAdicComplete (Ideal.span {(p : R)}) R := by
  intro p R _ h
  obtain ⟨N, hN⟩ := span_natCast_pow_eq_bot_of_isNilpotent p R h
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have := hx N
    rwa [hN, SModEq.bot] at this
  · intro f hf
    refine ⟨f N, fun n => ?_⟩
    rcases le_total n N with hn | hn
    · exact hf hn
    · have h1 := hf hn
      rw [hN, SModEq.bot] at h1
      rw [h1]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericSemiAbelianCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericSemiAbelianCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.lbIso_of_generic_semiAbelian_cdvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left), IsGrpPullback GK G₁ (jK V) φ → ∀ L L' : LB G₁.left, L.IsLB → L'.IsLB → LBIso (L.pull φ) (L'.pull φ) → LBIso L L' := by
  intro V _ _ _ hV G₁ _ _ hG GK _ φ hφ L L' hL hL' h
  haveI : IsDiscreteValuationRing V := hV.1
  have hi : pullback.fst G₁.hom (jK V) = hφ.1.isoPullback.inv ≫ φ := hφ.1.isoPullback_inv_fst.symm
  have h' : LBIso (L.pull (pullback.fst G₁.hom (jK V))) (L'.pull (pullback.fst G₁.hom (jK V))) :=
    GlobalTheory.GenericSpread.lbIso_pull_of_comp hφ.1.isoPullback.inv hi h
  exact GlobalTheory.lbIso_of_generic_normal_local V inferInstance inferInstance G₁.left G₁.hom (eSec G₁) hG.smooth
    hG.quasiCompact (GlobalTheory.geometricallyIntegral_of_isSemiAbelian G₁ (h := hG)) (Over.w (MonObj.one (X := G₁))) L L' hL hL' h'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericSemiAbelianCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left), IsGrpPullback GK G₁ (jK V) φ → ∀ L L' : LB G₁.left, L.IsLB → L'.IsLB → LBIso (L.pull φ) (L'.pull φ) → LBIso L L' := by
  first | exact @GlobalTheory.lbIso_of_generic_semiAbelian_cdvr | exact GlobalTheory.lbIso_of_generic_semiAbelian_cdvr | (intros; apply GlobalTheory.lbIso_of_generic_semiAbelian_cdvr <;> assumption)
end
end
