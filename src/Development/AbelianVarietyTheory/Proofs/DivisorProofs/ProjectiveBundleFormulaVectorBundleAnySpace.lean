module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaDiscreteSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCocycleSimplicialLevelsCup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainProductAlexanderWhitneyFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GagaLineGeneratorEmbedding
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc.AWCross

theorem idc_eq (M a : ℕ) (h : 0 + a ≤ M) : idc M a = SimplexCategory.subinterval 0 a h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (v : ℕ) = (v : ℕ) + 0
    have := v.2
    omega

theorem backc_eq (M a b : ℕ) (h : a + b ≤ M) : backc M a b = SimplexCategory.subinterval a b h :=
  hom_ext_val _ _ fun v => by
    rw [sub_val]
    change min M (a + (v : ℕ)) = (v : ℕ) + a
    have := v.2
    omega

variable {R : Type} [CommRing R]

theorem evT_of_eq {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (t s : ℤ)
    (ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-(a : ℤ), -(b : ℤ)) = t)
    (h : t + n = s) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) t ht ≫
      γ.v t s h) (freeGen R _ U y) =
    evT γ a b s (by simp only [ComplexShape.π_def] at ht; push_cast; omega) U y := by
  obtain rfl : t = -((a + b : ℕ) : ℤ) := by simp only [ComplexShape.π_def] at ht; push_cast; omega
  rfl

theorem map_comp_apply' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (y : Sec F U) :
    Sec.map (f ≫ g) y = Sec.map g (Sec.map f y) := rfl

theorem mapHom_apply' (F G : Shv R) {U : Scheme.{0}} (y : Sec F U) (φ : F ⟶ G) : mapHom F G y φ = Sec.map φ y := rfl

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

theorem baseS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    baseS V ((awP (twX E V) M a (M - a)).app (op U) x) = (x.sub 0 a (by omega)).map (twPi E V) := by
  unfold awP
  rw [idc_eq M a (by omega)]
  rfl

theorem ell_nat (M p q : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk M)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk M) :
    ((twX E V).map θ.op).app (op (SimplexCategory.mk M)) ≫ ((twX E V).obj (op (SimplexCategory.mk p))).map β.op ≫
      (ℓ.app (op (SimplexCategory.mk p))).app (op (SimplexCategory.mk q)) =
    (ℓ.app (op (SimplexCategory.mk M))).app (op (SimplexCategory.mk M)) ≫ B.map β.op := by
  rw [(ℓ.app _).naturality, ← Category.assoc, ← NatTrans.comp_app, ℓ.naturality]
  simp

theorem vertS_aw (M a : ℕ) (ha : a ≤ M) (U : Scheme.{0}) (x : Sx (bidiag.obj (twX E V)) M U) :
    vertS V ℓ ((awP (twX E V) M a (M - a)).app (op U) x) =
      (x.sub a (M - a) (by omega)).map (bidiag.map ℓ ≫ (bidiagConst B).hom) := by
  unfold awP vertS
  rw [backc_eq M a (M - a) (by omega)]
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M a (M - a) (idc M a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (ell_nat V ℓ M (M - a) (M - a)
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))
    (SimplexCategory.subinterval (n := M) a (M - a) (by omega))) (op U)) x
  exact h1.trans h2.symm
end Cross

theorem isAW_pull_crossT : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  intro R _ E N V B ℓ I J K μ n m k hk α z c hc M w h U x
  rw [ev_def, hc M w h]
  simp only [awZ, Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp]
  change mapHom _ _ (freeGen R _ U x) (∑ a : Fin (M + 1), _) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mapHom_apply', map_comp_apply', freeGen_map, evT_of_eq, evT_crossT, ev_pull, ev_pull, baseS_aw V M (a : ℕ) (by omega), vertS_aw V ℓ M (a : ℕ) (by omega)]

end GlobalTheory.PBFc.AWCross

end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_product_alexander_whitney_formula : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (c : Cochain ((chains R).obj (bidiag.obj (twX E V))) K k) (hc : ∀ (M : ℕ) (s : ℤ) (h : -(M : ℤ) + k = s), c.v (-(M : ℤ)) s h = awZ R (twX E V) M ≫ (crossT V ℓ μ hk α z).v (-(M : ℤ)) s h), μ.IsAW hk ((Cochain.ofHom ((chains R).map (twPi E V))).comp α (zero_add n)) ((Cochain.ofHom ((chains R).map (bidiag.map ℓ ≫ (bidiagConst B).hom))).comp z (zero_add m)) c := by
  first | (exact @GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (exact GlobalTheory.PBFc.AWCross.isAW_pull_crossT) | (intros; apply GlobalTheory.PBFc.AWCross.isAW_pull_crossT  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsStrictlyLE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCocycleClassesPullbackCup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryChartFrameGrowth
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section
namespace GlobalTheory.PBFc

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ n x) := by
  subst hn; subst hi; rfl

theorem cast_cup (q : ℕ) {E : Spc} {n m k a b c : ℤ} (hk : n + m = k) (hc : a + b = c) (x : Ht q E n a) (y : Ht q E m b) :
    Ht.cast hk hc ((twPair q a b).cup E rfl x y) =
      (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
        (twPair q a b) hc).cup E hk x y := by
  subst hk; subst hc; rfl

theorem cls_term (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (j : Fin N)
    (z : Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n,
      γ.1 = (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
        (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) ∧
      pull _ (twIso E V).hom _ n (Ht.cast (by ring) (by ring) (cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a))
        (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) : Ht q _ n i) = CohomologyClass.mk γ := by
  set c := (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
    (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) with hcdef
  have hAW := GlobalTheory.T.cochain_product_alexander_whitney_formula V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1 c (fun M s h => by
    rw [hcdef, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, awChains_f])
  have hδ := aw_cocycle (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _))
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) c (by
      simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW)
  refine ⟨Cocycle.mk c (n + 1) rfl hδ, rfl, ?_⟩
  rw [pull_cast]
  change Ht.cast _ _ (cpull ((chains (ZMod q)).map (twIso E V).hom) _ _ ((twPair q _ _).cup _ rfl _ _)) = _
  rw [Pair.cup_pull, cast_cup]
  change (twPairI q i ((j : ℕ) : ℤ)).cup _ _ (pull _ (twIso E V).hom _ _ (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a)))
    (pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) = _
  rw [← pull_comp, twIso_hom_fst, ← hz]
  refine Pair.cup_spec _ _ _ (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _)) _ _ ?_
  simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW

theorem pbfMap_eq_cpull_aw (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n)
    (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)) :
    pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  choose γ hγ hγc using fun j : Fin N => cls_term q V ℓ n i j (z j) (hz j) (a j)
  have e1 : pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      ∑ j : Fin N, CohomologyClass.mk (γ j) := by
    unfold pbfMap
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hγc j
  have e2 : zcomp (Cocycle.ofHom (awChains (ZMod q) (twX E V))) b (zero_add n) = ∑ j : Fin N, γ j := by
    apply Cocycle.ext
    have hs := map_sum (AddSubgroup.subtype (cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res (ZMod q) (tw q i)) n)) γ Finset.univ
    refine Eq.trans ?_ hs.symm
    change _ = ∑ j, (γ j).1
    simp only [hγ]
    change (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp b.1 (zero_add n) = _
    rw [hb, phi_apply]
    exact map_sum (AddMonoidHom.mk' (fun x : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n =>
      (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp x (zero_add n)) (fun x y => Cochain.comp_add _ _ _ _)) _ _
  rw [e1, cpre_mk, e2]
  exact (map_sum (AddMonoidHom.mk' (CohomologyClass.mk : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n → _)
    (fun x y => CohomologyClass.mk_add x y)) _ _).symm

end GlobalTheory.PBFc
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_cocycle_classes_pullback_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) = pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n) (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)), pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) = cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  first | (exact @GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (exact GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (intros; apply GlobalTheory.PBFc.pbfMap_eq_cpull_aw  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainProductVanishingAboveDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GagaLineGeneratorComplex
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem crossT_ι_eq_zero_of_vanish {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ)
    (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r)
    (hc : p < c) :
    (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  have ht : c + l = t := h
  by_cases hcl : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R (twX E V) a b).inv, comp_zero]
    refine free_ext _ _ fun U y => ?_
    have e1 := evT_crossT V ℓ μ hk α z a b r hr U y
    unfold evT at e1
    refine e1.trans ?_
    have h0 : ev α a _ rfl U (baseS V y) = 0 := by
      rw [ev_def, hα _ _ _ hc, comp_zero]
      exact map_zero (mapHom _ _ (freeGen R _ U (baseS V y)))
    rw [h0, map_zero, LinearMap.zero_apply, smul_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).symm
  · exact (biChains_isZero (R := R) (twX E V) c l (by omega)).eq_of_src _ _

end GlobalTheory.PBFc
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_product_vanishing_above_degree : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ) (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ) (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r) (hc : p < c), (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  first | (exact @GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (exact GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (intros; apply GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossProductTwistedLeibnizRule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossProductTwistedLeibnizRule
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc
variable {R : Type} [CommRing R]
set_option backward.isDefEq.respectTransparency false in
theorem biChains_dh (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X (a + 1) b).inv ≫ ((biChains R X).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ))).f (-(b : ℤ)) =
      (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((X.δ i).app (op (SimplexCategory.mk b)))) ≫
        (biChainsXIso R X a b).inv := by
  let D := (dblF R).obj ((freeBi R).obj X)
  let M := ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  have h1 : (biChains R X).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ)) =
      (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).hom ≫ M.d (a + 1) a ≫
        (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv :=
    HomologicalComplex.extend_d_eq M ComplexShape.embeddingDownNat rfl rfl
  have h2 : ∀ p : ℕ, (biChainsXIso R X p b).inv =
      @CategoryStruct.comp _ _ _ ((M.X p).X (-(b : ℤ))) _
        ((D.X p).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv
        ((M.extendXIso ComplexShape.embeddingDownNat (i := p) rfl).inv.f (-(b : ℤ))) := fun p => rfl
  have h3 : (M.d (a + 1) a).f (-(b : ℤ)) = ((D.X (a+1)).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).hom ≫
      (D.d (a + 1) a).f b ≫ ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := b) rfl
  have key : (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).inv.f (-(b : ℤ)) ≫
      (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).hom.f (-(b : ℤ)) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [h1, h2, h2, HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, reassoc_of% key, h3,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  congr 2
  rw [show D.d (a + 1) a = ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) •
      (((SimplicialObject.whiskering _ _).obj (AlgebraicTopology.alternatingFaceMapComplex (Shv R))).obj ((freeBi R).obj X)).δ i
    from AlgebraicTopology.alternatingFaceMapComplex_obj_d _ a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← HomologicalComplex.eval_map, Functor.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Functor.map_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem biChains_dv (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X a (b + 1)).inv ≫ ((biChains R X).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      (∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • (free R).map ((X.obj (op (SimplexCategory.mk a))).δ j)) ≫
        (biChainsXIso R X a b).inv := by
  let D := (dblF R).obj ((freeBi R).obj X)
  let M := ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  have h2 : ∀ q : ℕ, (biChainsXIso R X a q).inv =
      @CategoryStruct.comp _ _ _ ((M.X a).X (-(q : ℤ))) _
        ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := q) rfl).inv
        ((M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-(q : ℤ))) := fun q => rfl
  have h3 : (M.X a).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b + 1) rfl).hom ≫ (D.X a).d (b + 1) b ≫
        ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv :=
    HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl
  have hc : (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-((b + 1 : ℕ) : ℤ)) ≫
      ((biChains R X).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      (M.X a).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) ≫ (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-(b : ℤ)) :=
    HomologicalComplex.Hom.comm _ _ _
  rw [h2, h2, Category.assoc, hc, h3, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  congr 2
  rw [show (D.X a).d (b + 1) b = ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • ((freeBi R).obj X |>.obj (op (SimplexCategory.mk a))).δ j
    from AlgebraicTopology.alternatingFaceMapComplex_obj_d _ b]
  rfl

section Faces
variable {X : SimplicialObject Spc}

def BSx.hface {a b : ℕ} {U : Scheme.{0}} (y : BSx X (a + 1) b U) (i : Fin (a + 2)) : BSx X a b U :=
  ((X.δ i).app (op (SimplexCategory.mk b))).app (op U) y

def BSx.vface {a b : ℕ} {U : Scheme.{0}} (y : BSx X a (b + 1) U) (j : Fin (b + 2)) : BSx X a b U :=
  ((X.obj (op (SimplexCategory.mk a))).δ j).app (op U) y

variable {K : Cx R} {k : ℤ}

def evD (γ : Cochain (totChains R X) K k) (t : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X t) U :=
  if h : -((a + b : ℕ) : ℤ) + k = t then evT γ a b t h U y else 0

theorem evD_eq (γ : Cochain (totChains R X) K k) (t : ℤ) (a b : ℕ) (h : -((a + b : ℕ) : ℤ) + k = t) (U : Scheme.{0})
    (y : BSx X a b U) : evD γ t a b U y = evT γ a b t h U y := dif_pos h

def hB (γ : Cochain (totChains R X) K k) (t : ℤ) : ∀ (a b : ℕ) (U : Scheme.{0}), BSx X a b U → Sec (K.X t) U
  | 0, _, _, _ => 0
  | a + 1, b, U, y => ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • evD γ t a b U (y.hface i)

def vB (γ : Cochain (totChains R X) K k) (t : ℤ) : ∀ (a b : ℕ) (U : Scheme.{0}), BSx X a b U → Sec (K.X t) U
  | _, 0, _, _ => 0
  | a, b + 1, U, y => ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • evD γ t a b U (y.vface j)

end Faces

theorem ιTotal_v_congr {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (i₁ i₂ p p' t : ℤ)
    (hp : p = p') (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = p)
    (h' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = p')
    (hv : p + k = t) (hv' : p' + k = t) :
    (biChains R X).ιTotal (ComplexShape.up ℤ) i₁ i₂ p h ≫ γ.v p t hv =
      (biChains R X).ιTotal (ComplexShape.up ℤ) i₁ i₂ p' h' ≫ γ.v p' t hv' := by
  subst hp
  rfl

theorem evT_dh {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (a b : ℕ) (p t : ℤ)
    (hp : -((a + b : ℕ) : ℤ) + 1 = p) (hv : p + k = t) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).d₁ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) p ≫ γ.v p t hv)
      (freeGen R _ U y) = hB γ t a b U y := by
  cases a with
  | zero =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel (-((0 : ℕ) : ℤ)) 1 from by simp) (-(b : ℤ)) p
      (by simp only [ComplexShape.π_def]; omega),
      (biChains_isZero X 1 (-(b : ℤ)) (Or.inl one_pos)).eq_of_tgt (HomologicalComplex.Hom.f _ _) 0]
    simp only [zero_comp, smul_zero, comp_zero]
    exact map_zero (mapHom _ _ (freeGen R _ U y))
  | succ a =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ)) from by simp <;> omega)
      (-(b : ℤ)) p (by simp only [ComplexShape.π_def]; omega)]
    show _ = ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • evD γ t a b U (y.hface i)
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-((a + 1 : ℕ) : ℤ), -(b : ℤ)) = 1 from rfl,
      one_smul, Category.assoc, ← Category.assoc _ (HomologicalComplex.Hom.f _ _), biChains_dh, Category.assoc,
      Preadditive.sum_comp]
    refine (map_sum (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map (_ ≫ _ ≫ γ.v p t hv) (Sec.map ((free R).map _) (freeGen R _ U y)) = _
    rw [freeGen_map, evD_eq γ t a b (by omega)]
    unfold evT
    rw [ιTotal_v_congr γ _ _ p (-((a + b : ℕ) : ℤ)) t (by omega) _ (by simp only [ComplexShape.π_def]; omega) hv]
    rfl

theorem evT_dv {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (a b : ℕ) (p t : ℤ)
    (hp : -((a + b : ℕ) : ℤ) + 1 = p) (hv : p + k = t) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).d₂ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) p ≫ γ.v p t hv)
      (freeGen R _ U y) = (a : ℤ).negOnePow • vB γ t a b U y := by
  cases b with
  | zero =>
    rw [HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (-((0 : ℕ) : ℤ)) 1 from by simp) p
      (by simp only [ComplexShape.π_def]; omega),
      (biChains_isZero X (-(a : ℤ)) 1 (Or.inr one_pos)).eq_of_tgt (HomologicalComplex.d _ _ _) 0]
    simp only [zero_comp, smul_zero, comp_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).trans (smul_zero _).symm
  | succ b =>
    show _ = (a : ℤ).negOnePow • ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • evD γ t a b U (y.vface j)
    rw [HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) from by simp <;> omega)
      p (by simp only [ComplexShape.π_def]; omega),
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-(a : ℤ), -((b + 1 : ℕ) : ℤ)) = (a : ℤ).negOnePow
        by simp,
      Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    refine (map_zsmul (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans ?_
    rw [Units.smul_def]
    congr 1
    rw [Category.assoc, ← Category.assoc _ (HomologicalComplex.d _ _ _), biChains_dv, Category.assoc, Preadditive.sum_comp]
    refine (map_sum (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map (_ ≫ _ ≫ γ.v p t hv) (Sec.map ((free R).map _) (freeGen R _ U y)) = _
    rw [freeGen_map, evD_eq γ t a b (by omega)]
    unfold evT
    rw [ιTotal_v_congr γ _ _ p (-((a + b : ℕ) : ℤ)) t (by omega) _ (by simp only [ComplexShape.π_def]; omega) hv]
    rfl

theorem evT_δ {X : SimplicialObject Spc} {K : Cx R} {k k' : ℤ} (hk : k + 1 = k') (γ : Cochain (totChains R X) K k)
    (a b : ℕ) (s t : ℤ) (hs : -((a + b : ℕ) : ℤ) + k = s) (ht : -((a + b : ℕ) : ℤ) + k' = t) (U : Scheme.{0})
    (y : BSx X a b U) :
    evT (δ k k' γ) a b t ht U y = Sec.map (K.d s t) (evT γ a b s hs U y) +
      k'.negOnePow • (hB γ t a b U y + (a : ℤ).negOnePow • vB γ t a b U y) := by
  rw [evT, δ_v k k' hk γ _ t ht s (-((a + b : ℕ) : ℤ) + 1) (by omega) rfl, Preadditive.comp_add, Preadditive.comp_add]
  refine (map_add (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · simp only [← Category.assoc]
    rfl
  · rw [Units.smul_def, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
    refine (map_zsmul (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans ?_
    rw [Units.smul_def]
    congr 1
    rw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add, ← Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂_assoc, Preadditive.comp_add]
    refine (map_add (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact evT_dh γ a b _ t rfl _ U y
    · exact evT_dv γ a b _ t rfl _ U y

section Cross2
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

theorem vertS_hface {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) (a + 1) b U) (i : Fin (a + 2)) :
    vertS V ℓ (y.hface i) = vertS V ℓ y := by
  have h := ℓ.naturality (SimplexCategory.δ i).op
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h (op (SimplexCategory.mk b))) (op U)) y

theorem vertS_vface {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a (b + 1) U) (j : Fin (b + 2)) :
    vertS V ℓ (y.vface j) = (vertS V ℓ y).face j :=
  ConcreteCategory.congr_hom (NatTrans.congr_app ((ℓ.app (op (SimplexCategory.mk a))).naturality
    (SimplexCategory.δ j).op) (op U)) y

end Cross2

section Two
variable {E B : Spc} {U : Scheme.{0}} {I J K : Cx R} (μ : Pair I J K) {n m : ℤ}

def bisimplexFunctionBoundaryFirst {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx B r U → A) : ∀ p r : ℕ, Sx E p U → Sx B r U → A
  | 0, _, _, _ => 0
  | p + 1, r, x, v => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ p r (x.face i) v

def bisimplexFunctionBoundarySecond {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx B r U → A) : ∀ p r : ℕ, Sx E p U → Sx B r U → A
  | _, 0, _, _ => 0
  | p, r + 1, x, v => ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) • φ p r x (v.face j)

def xv (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (w : ℤ) (p r : ℕ) (x : Sx E p U)
    (v : Sx B r U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w then
    μ.mul U _ _ w h (GlobalTheory.EtC.ev (R := R) α p _ rfl U x) (GlobalTheory.EtC.ev (R := R) z r _ rfl U v)
  else 0

theorem xv_eq (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (w : ℤ) (p r : ℕ) (x : Sx E p U)
    (v : Sx B r U) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(r : ℤ) + m = t) (h : s + t = w) :
    xv μ α z w p r x v =
      μ.mul U s t w h (GlobalTheory.EtC.ev (R := R) α p s hs U x) (GlobalTheory.EtC.ev (R := R) z r t ht U v) := by
  subst hs ht
  exact dif_pos h

theorem xv_δ_left {n₁ : ℤ} (hn : n + 1 = n₁) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m)
    (w : ℤ) (p r : ℕ) (x : Sx E p U) (v : Sx B r U) (s s' t : ℤ) (hs : -(p : ℤ) + n = s) (hs' : s + 1 = s')
    (ht : -(r : ℤ) + m = t) (h : s' + t = w) :
    μ.mul U s' t w h (Sec.map (I.d s s') (GlobalTheory.EtC.ev (R := R) α p s hs U x))
      (GlobalTheory.EtC.ev (R := R) z r t ht U v) =
      xv μ (δ n n₁ α) z w p r x v - sg n₁ • bisimplexFunctionBoundaryFirst (xv μ α z w) p r x v := by
  rw [xv_eq μ _ z w p r x v s' t (by omega) ht h]
  cases p with
  | zero => rw [ev_δ_zero hn α U s s' hs, bisimplexFunctionBoundaryFirst, smul_zero, sub_zero]
  | succ p =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ev_δ_succ hn α U p s s' hs, bisimplexFunctionBoundaryFirst, map_add (f := _), LinearMap.add_apply, sg_smul, map_zsmul, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, LinearMap.smul_apply, xv_eq μ α z w p r _ v s' t (by omega) ht h]

theorem xv_δ_right {m₁ : ℤ} (hm : m + 1 = m₁) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m)
    (w : ℤ) (p r : ℕ) (x : Sx E p U) (v : Sx B r U) (s t t' : ℤ) (hs : -(p : ℤ) + n = s)
    (ht : -(r : ℤ) + m = t) (ht' : t + 1 = t') (h : s + t' = w) :
    μ.mul U s t' w h (GlobalTheory.EtC.ev (R := R) α p s hs U x)
      (Sec.map (J.d t t') (GlobalTheory.EtC.ev (R := R) z r t ht U v)) =
      xv μ α (δ m m₁ z) w p r x v - sg m₁ • bisimplexFunctionBoundarySecond (xv μ α z w) p r x v := by
  rw [xv_eq μ α _ w p r x v s t' hs (by omega) h]
  cases r with
  | zero => rw [ev_δ_zero hm z U t t' ht, bisimplexFunctionBoundarySecond, smul_zero, sub_zero]
  | succ r =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ev_δ_succ hm z U r t t' ht, bisimplexFunctionBoundarySecond, map_add (f := _), sg_smul, map_zsmul, map_sum, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, xv_eq μ α z w p r x _ s t' hs (by omega) h]

theorem d_xv {n₁ m₁ : ℤ} (hn : n + 1 = n₁) (hm : m + 1 = m₁) (α : Cochain ((chains R).obj E) I n)
    (z : Cochain ((chains R).obj B) J m) (w w' : ℤ) (hw : w + 1 = w') (p r : ℕ) (x : Sx E p U) (v : Sx B r U)
    (h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w) :
    Sec.map (K.d w w') (xv μ α z w p r x v) =
      (xv μ (δ n n₁ α) z w' p r x v - sg n₁ • bisimplexFunctionBoundaryFirst (xv μ α z w') p r x v) +
        sg (-(p : ℤ) + n) • (xv μ α (δ m m₁ z) w' p r x v - sg m₁ • bisimplexFunctionBoundarySecond (xv μ α z w') p r x v) := by
  subst hw
  rw [xv_eq μ α z w p r x v _ _ rfl rfl h, μ.leibniz, xv_δ_left μ hn α z _ p r x v _ _ _ rfl rfl rfl,
    xv_δ_right μ hm α z _ p r x v _ _ _ rfl rfl rfl, sg_smul]

end Two

theorem evT_usmul {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (c : ℤˣ) (γ : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (c • γ) a b s h U y = c • evT γ a b s h U y := by
  unfold evT
  rw [Units.smul_def, Units.smul_def, Cochain.smul_v, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  exact map_zsmul (mapHom _ _ (freeGen R _ U y)) _ _

section Cross3
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

theorem evT_crossT_xv (a b : ℕ) (w : ℤ) (h : -((a + b : ℕ) : ℤ) + k = w) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b w h U y = sg (m * a) • xv μ α z w a b (baseS V y) (vertS V ℓ y) := by
  rw [evT_crossT, xv_eq μ α z w a b _ _ _ _ rfl rfl (by push_cast at h; omega), sg_smul]

theorem evD_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evD (crossT V ℓ μ hk α z) w a b U y = sg (m * a) • xv μ α z w a b (baseS V y) (vertS V ℓ y) := by
  by_cases h : -((a + b : ℕ) : ℤ) + k = w
  · rw [evD_eq _ _ _ _ h, evT_crossT_xv]
  · rw [evD, dite_eq_right h, xv, dite_eq_right (by push_cast at h; omega), smul_zero]

theorem hB_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    hB (crossT V ℓ μ hk α z) w a b U y = sg (m * a + m) • bisimplexFunctionBoundaryFirst (xv μ α z w) a b (baseS V y) (vertS V ℓ y) := by
  cases a with
  | zero => rw [hB, bisimplexFunctionBoundaryFirst, smul_zero]
  | succ a =>
    rw [hB, bisimplexFunctionBoundaryFirst, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evD_crossT, vertS_hface, smul_comm]
    congr 1
    rw [show m * ((a + 1 : ℕ) : ℤ) + m = m * a + (m + m) by push_cast; ring, sg_add, sg_add, sg_sq, mul_one]

theorem vB_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    vB (crossT V ℓ μ hk α z) w a b U y = sg (m * a) • bisimplexFunctionBoundarySecond (xv μ α z w) a b (baseS V y) (vertS V ℓ y) := by
  cases b with
  | zero => rw [vB, bisimplexFunctionBoundarySecond, smul_zero]
  | succ b =>
    rw [vB, bisimplexFunctionBoundarySecond, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evD_crossT, vertS_vface, smul_comm]
    rfl

end Cross3

theorem crossT_leibniz {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k n' m' k' : ℤ}
    (hk : n + m = k) (hn : n + 1 = n') (hm : m + 1 = m') (hk' : k + 1 = k') (hk₁ : n' + m = k') (hk₂ : n + m' = k')
    (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) :
    δ k k' (crossT V ℓ μ hk α z) = crossT V ℓ μ hk₁ (δ n n' α) z + n.negOnePow • crossT V ℓ μ hk₂ α (δ m m' z) := by
  refine evT_ext _ _ fun a b t ht U y => ?_
  rw [evT_add, evT_usmul, evT_δ hk' _ a b (-((a + b : ℕ) : ℤ) + k) t rfl ht U y, evT_crossT_xv, evT_crossT_xv,
    evT_crossT_xv, hB_crossT, vB_crossT]
  have hd := d_xv μ hn hm α z (-((a + b : ℕ) : ℤ) + k) t (by omega) a b (baseS V y) (vertS V ℓ y) (by push_cast; omega)
  rw [Sec.map] at hd
  rw [Sec.map, map_zsmul, hd]
  clear hd
  subst hn hm hk hk'
  have e1 : sg ((m + 1) * (a : ℤ)) = sg (m * a) * sg a := by rw [add_mul, one_mul, sg_add]
  rw [e1]
  simp only [sg_smul, sg_add, sg_neg, sg_one]
  have q1 := sg_sq m
  have q2 := sg_sq n
  have q3 := sg_sq (a : ℤ)
  have q4 := sg_sq (m * (a : ℤ))
  generalize sg m = σm at *
  generalize sg n = σn at *
  generalize sg (a : ℤ) = σa at *
  generalize sg (m * (a : ℤ)) = σ at *
  match_scalars <;> first | ring1 | linear_combination (-(σ * σn)) * q1 | linear_combination (σ * σn) * q1

end GlobalTheory.PBFc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossProductTwistedLeibnizRuleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crossProductTwisted_leibniz_rule : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k n' m' k' : ℤ} (hk : n + m = k) (hn : n + 1 = n') (hm : m + 1 = m') (hk' : k + 1 = k') (hk₁ : n' + m = k') (hk₂ : n + m' = k') (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m), δ k k' (crossT V ℓ μ hk α z) = crossT V ℓ μ hk₁ (δ n n' α) z + n.negOnePow • crossT V ℓ μ hk₂ α (δ m m' z) := by
  first | (exact @GlobalTheory.PBFc.crossT_leibniz) | (exact GlobalTheory.PBFc.crossT_leibniz) | (intros; apply GlobalTheory.PBFc.crossT_leibniz  <;> assumption)
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

instance res_isStrictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

instance chains_isStrictlyLE (R : Type) [CommRing R] (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
  (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)

theorem phi_δ (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n m : ℤ) (hnm : n + 1 = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i (fun j => (z j).1) m (fun j => δ (n - 2 * ((j : ℕ) : ℤ)) (m - 2 * ((j : ℕ) : ℤ)) (α j)) =
      δ n m (phi q V ℓ i (fun j => (z j).1) n α) := by
  have hs : ∀ (f : Fin N → Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      δ n m (∑ j, f j) = ∑ j, δ n m (f j) := fun f => map_sum (AddMonoidHom.mk' (δ n m) (δ_add n m)) f _
  rw [phi_apply, phi_apply, hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = δ n m _
  rw [GlobalTheory.T.crossProductTwisted_leibniz_rule V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (show n - 2 * ((j : ℕ) : ℤ) + 1 = m - 2 * ((j : ℕ) : ℤ) by omega) rfl hnm (by omega) (by omega),
    Cocycle.δ_eq_zero (z j), crossT_zero_right, smul_zero, add_zero]

theorem phi_van (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (p n : ℤ)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (hα : ∀ j c r hr, p < c → (α j).v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + n = r) (hc : p < c) :
    (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (phi q V ℓ i z n α).v t r hr = 0 := by
  let ev₀ : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n →+ _ :=
    AddMonoidHom.mk' (fun γ => (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ γ.v t r hr)
      (fun γ γ' => by rw [Cochain.add_v, Preadditive.comp_add])
  change ev₀ _ = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [phi_apply, map_sum]
  exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.cochain_product_vanishing_above_degree V ℓ _ _ (α j) (z j) p (hα j) c l t h r hr hc

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv (ZMod q)) (n : ℤ) :
    Function.Bijective (pull (ZMod q) e.hom F n) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨pull (ZMod q) e.inv F n y, ?_⟩⟩
  · have hx := (pull_comp (ZMod q) e.inv e.hom F n x).symm
    have hy := (pull_comp (ZMod q) e.inv e.hom F n y).symm
    rw [e.inv_hom_id, pull_id] at hx hy
    exact hx.symm.trans ((congrArg _ hxy).trans hy)
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pbf_of_model [NeZero q] (hE : Inv q E)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hzd : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map
        (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (hzc : ∀ (a : ℕ) (j : Fin N),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j)
        (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ))
    (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀) : PBF q V := by
  intro n i
  have hf1 := pull_iso_bijective q (twIso E V) (tw q i) n
  have hf2 := pull_awChains_bijective (ZMod q) (twX E V) (res _ (tw q i)) n
  let φ : (∀ j : Fin N, CohomologyClass ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) → CohomologyClass (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
    fun x => Function.surjInv hf2.2 (pull _ (twIso E V).hom _ n (pbfMap q V n i x))
  have hφ : ∀ (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1) →
      φ (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
    intro a b hb
    apply hf2.1
    rw [Function.surjInv_eq hf2.2]
    exact GlobalTheory.T.twisted_cocycle_classes_pullback_cup q V ℓ n i z hzd a b hb
  have hb : Function.Bijective φ :=
    GlobalTheory.ColFilt.bijective_total_of_terms (ZMod q) (biChains (ZMod q) (twX E V))
      (fun p k h => biChains_isZero (twX E V) p k h) ((chains (ZMod q)).obj E)
      (fun j : Fin N => res _ (tw q (i - ((j : ℕ) : ℤ)))) (res _ (tw q i)) (fun j : Fin N => 2 * ((j : ℕ) : ℤ))
      (phi q V ℓ i (fun j => (z j).1)) (fun n m h α => phi_δ q V ℓ i z n m h α)
      (fun p n α hα => phi_van q V ℓ i (fun j => (z j).1) p n α hα)
      (GlobalTheory.T.twisted_cocycle_simplicial_levels_cup q V hE ℓ i z hzc hD) n φ hφ
  have hcomp : (pull _ (twIso E V).hom _ n) ∘ pbfMap q V n i = (cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n) ∘ φ :=
    funext fun x => (Function.surjInv_eq hf2.2 _).symm
  exact (Function.Bijective.of_comp_iff' hf1 _).1 (hcomp ▸ hf2.comp hb)

end GlobalTheory.PBFc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpaces
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFg
open GlobalTheory.EtC

def invPSh (q : ℕ) : PSh where
  obj U := PLift (IsUnit (q : Scheme.Γ.obj U))
  map f := TypeCat.ofHom fun h => ⟨(map_natCast (Scheme.Γ.map f).hom q) ▸ h.down.map (Scheme.Γ.map f).hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev lineSp (q : ℕ) : Spc := ptimes (invPSh q) (ofCat (glCat 1))

abbrev lineSp.line (q : ℕ) : lineSp q ⟶ ofCat (glCat 1) := ptimes.snd _ _

theorem inv_lineSp (q : ℕ) : Inv q (lineSp q) := fun _ ⟨y⟩ => y.1.down

theorem inv_of_map {E E' : Spc} (f : E ⟶ E') {q : ℕ} (h : Inv q E') : Inv q E := fun U ⟨x⟩ =>
  h U ⟨((f.app (op (SimplexCategory.mk 0))).app (op U)) x⟩

theorem isUnit_of_simplex {q : ℕ} {E : Spc} (hE : Inv q E) (p : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ)
    (x : (E.obj p).obj U) : IsUnit (q : Scheme.Γ.obj U) :=
  hE U.unop ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) p.unop 0).op).app U x⟩

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E)

def colInv (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ disc.obj (invPSh q) where
  app n := { app := fun U => TypeCat.ofHom (fun y => ⟨isUnit_of_simplex hE p U y.1⟩), naturality := fun _ _ _ => rfl }
  naturality _ _ _ := rfl

def colLine (p : SimplexCategoryᵒᵖ) : ptimes (E.obj p) (Fib N) ⟶ lineSp q :=
  (ptimesIsLimit _ _).lift (BinaryFan.mk (colInv q hE p) (ptimes.snd _ _ ≫ Fib.line N))

theorem colLine_line (p : SimplexCategoryᵒᵖ) : colLine q hE p ≫ lineSp.line q = ptimes.snd (E.obj p) (Fib N) ≫ Fib.line N :=
  (ptimesIsLimit _ _).fac _ ⟨WalkingPair.right⟩

def ellB : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (lineSp q) where
  app p := colLine q hE p
  naturality _ _ _ := rfl

theorem pull_cast {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E₂ n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f (tw q i) n x : Ht q E₁ n i) := by
  subst hn hi; rfl

theorem pull_cpow [NeZero q] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) (h : Inv q E₂) (x : Ht q E₂ 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (a6nat_holds q).2.1 f h]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (a6nat_holds q).1, ih]

theorem mk_zcomp_ofHom {R : Type} [CommRing R] {E₁ E₂ : Spc} (f : E₁ ⟶ E₂) {F : Shv R} {n : ℤ}
    (z : Cocycle ((chains R).obj E₂) (res R F) n) :
    CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _)) = pull R f F n (CohomologyClass.mk z) :=
  rfl

theorem diag_line : (bidiag.map (ellB q V hE) ≫ (bidiagConst (lineSp q)).hom) ≫ lineSp.line q =
    bidiag.map (twLine E V) ≫ (bidiagConst _).hom := rfl

theorem pbf_of_disc : ∀ (q : ℕ) [NeZero q] (N : ℕ),
    (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) →
      ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  intro q _ N hD E V hE
  have hB := inv_lineSp q
  have hP : Inv q (pullback V (PGL.pr N)) := inv_of_map (pullback.fst V (PGL.pr N)) hE
  choose z hz using fun j : Fin N => CohomologyClass.mk_surjective (cpow q (c1 q (lineSp.line q)) (j : ℕ))
  refine GlobalTheory.PBFc.pbf_of_model q V (ellB q V hE) hE z (fun j => ?_) (fun a j => ?_) hD
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB, pull_cpow q _ hP,
      (a6nat_holds q).2.2.1 _ _ hP, twIso_line, diag_line]
  · rw [mk_zcomp_ofHom, hz, pull_cpow q _ hB, (a6nat_holds q).2.2.1 _ _ hB]
    exact congrArg (fun L => cpow q (c1 q L) (j : ℕ)) (colLine_line q hE _)

end GlobalTheory.PBFg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfDiscreteSpacesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces : ∀ (q : ℕ) [NeZero q] (N : ℕ), (∀ (F : PSh) (V : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V) → ∀ {E : Spc} (V : E ⟶ ofCat (glCat N)), Inv q E → PBF q V := by
  first | (exact @GlobalTheory.PBFg.pbf_of_disc) | (exact GlobalTheory.PBFg.pbf_of_disc) | (intros; apply GlobalTheory.PBFg.pbf_of_disc  <;> assumption)
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

theorem projectiveBundleFormula_vectorBundle_any_space : D1 :=
  projectiveBundleFormula_of_unitOnEtalePoints fun q _ _ N V hq => GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces q N (GlobalTheory.T.projectiveBundleFormula_discrete_space q N) V hq

end GlobalTheory.EtC

end
