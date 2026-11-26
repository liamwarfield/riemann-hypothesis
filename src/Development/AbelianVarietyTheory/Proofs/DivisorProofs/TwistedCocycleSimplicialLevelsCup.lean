module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAwChainsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvPullbackPgl
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem pull_htCast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn; subst hi; rfl

theorem pull_cpow (q : ℕ) [NeZero q] (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x : Ht q E 2 1) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_htCast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_htCast, (hA q).1, ih]

theorem inv_pullback_pgl (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) :
    Inv q (pullback V (PGL.pr N)) := fun U ⟨x⟩ => hE U ⟨Sx.map (pullback.fst V (PGL.pr N)) x⟩

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameFunctionCompare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullColIsoPbfMap
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg
variable (R : Type) [CommRing R]
open GlobalTheory.EtC.DiscChains

def colCx (X : SimplicialObject Spc) (a : ℕ) :
    (biChains R X).X (-(a : ℤ)) ≅ (chains R).obj (X.obj (op (SimplexCategory.mk a))) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapIso (Iso.refl _)

theorem colCx_f (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X a b).inv ≫ (colCx R X a).hom.f (-(b : ℤ)) =
      (chainsXIso R (X.obj (op (SimplexCategory.mk a))) b).inv := by
  have h1 := (HomologicalComplex.extendXIso (((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj ((dblF R).obj ((freeBi R).obj X))) ComplexShape.embeddingDownNat (i := a) (i' := -(a:ℤ)) rfl).inv_hom_id
  have h2 := congrArg (fun f => HomologicalComplex.Hom.f f (-(b:ℤ))) h1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h2
  erw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.trans_inv]
  erw [Category.assoc, reassoc_of% h2]
  erw [Functor.mapIso_refl, Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
  rfl

def prE (E : Spc) (a : ℕ) : (chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))) ⟶
    sgl (((chains R).obj E).X (-(a : ℤ))) :=
  (he R _).inv ≫ (CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv

def prEquiv (E : Spc) (a : ℕ) : HomotopyEquiv ((chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))))
    (sgl (((chains R).obj E).X (-(a : ℤ)))) :=
  (he R _).symm.trans (HomotopyEquiv.ofIso ((CochainComplex.singleFunctor (Shv R) 0).mapIso (chainsXIso R E a).symm))

theorem prE_zero (E : Spc) (a : ℕ) :
    (chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
  set P := E.obj (op (SimplexCategory.mk a))
  have hφψ : (he R P).hom.f 0 ≫ (he R P).inv.f 0 = 𝟙 _ := by
    have hc := (he R P).homotopyHomInvId.comm 0
    have hz1 : IsZero ((sgl ((free R).obj P)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    have hzm : IsZero ((sgl ((free R).obj P)).X (-1)) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp), prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      hz1.eq_of_tgt ((sgl ((free R).obj P)).d 0 1) 0, hzm.eq_of_tgt ((he R P).homotopyHomInvId.hom 0 (-1)) 0] at hc
    simp at hc
    exact hc
  have hinv0 : (chainsXIso R (disc.obj P) 0).inv ≫ (he R P).inv.f 0 = sglι ((free R).obj P) := by
    rw [← he_hom_f_zero R P, Category.assoc, hφψ, Category.comp_id]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (chainsXIso R E a).inv).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [prE, HomologicalComplex.comp_f, ← Category.assoc, hinv0, h1]

theorem mk_sum_cocycle {K L : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι) (γ : ι → Cocycle K L n) :
    ∑ j ∈ s, CohomologyClass.mk (γ j) = CohomologyClass.mk (∑ j ∈ s, γ j) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (CohomologyClass.mk_zero (K := K) (L := L) (n := n)).symm
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, CohomologyClass.mk_add]

theorem pull_colIso_pbfMap (q : ℕ) [NeZero q] (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N))
    (hP : Inv q (disc.obj P)) (m i : ℤ) (x : ∀ j : Fin N, Ht q (disc.obj P) (m - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (colIso P V₀).hom _ m (pbfMap q V₀ m i x) =
      ∑ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _ (x j))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) := by
  unfold pbfMap
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast, (a6nat_holds q).1, ← pull_comp, colIso_hom_fst, pull_cpow q a6nat_holds _ (inv_pullback_pgl q V₀ hP),
    (a6nat_holds q).2.2.1 _ _ (inv_pullback_pgl q V₀ hP), colIso_line]

theorem ev_prE_pos (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (s : ℕ) (t : ℤ) (h : -(s : ℤ) + d = t) (U : Scheme.{0})
    (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) s U) (hs : 0 < s) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) s t h U x = 0 := by
  have hz : IsZero ((sgl (((chains R).obj E).X (-(a : ℤ)))).X (-(s : ℤ))) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (-(s : ℤ)) (by omega)
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, hz.eq_of_src (c.v (-(s : ℤ)) t h) 0, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U x))

theorem ev_prE_zero (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (t : ℤ) (h : -((0 : ℕ) : ℤ) + d = t) (U : Scheme.{0}) (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0 U) :
    _root_.GlobalTheory.EtC.ev (R := R) ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) 0 t h U x =
      Sec.map ((chainsXIso R E a).inv ≫ sglι _ ≫ c.v 0 t (by simpa using h)) (freeGen R _ U x) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change Sec.map ((chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 ≫ c.v 0 t _) _ = _
  rw [reassoc_of% prE_zero R E a]
  rfl

end GlobalTheory.PBFg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductCastMkOfIsAlexanderWhitney
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductCastMkOfIsAlexanderWhitney
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem cup_cast_mk_of_isAW_rec (q : ℕ) {S : Spc} (a b k n m N : ℤ) (e : a + b = k) (hN : n + m = N)
    (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q a)) n)
    (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q b)) m)
    (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q k)) N)
    (h : (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
      (twPair q a b) e).IsAW hN α.1 β.1 γ.1) :
    ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast hN e : Ht q S N k) = CohomologyClass.mk γ := by
  subst e
  subst hN
  exact Pair.cup_spec (twPair q a b) S rfl α β γ h

theorem cup_cast_mk_of_isAW : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  intro q S i j m α β γ h
  exact cup_cast_mk_of_isAW_rec q (i - (j : ℤ)) (j : ℤ) i (m - 2 * (j : ℤ)) (2 * (j : ℤ)) m
    (sub_add_cancel i _) (sub_add_cancel m _) α β γ h

end GlobalTheory.PBFc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductCastMkOfIsAlexanderWhitneyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (exact GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (intros; apply GlobalTheory.PBFc.cup_cast_mk_of_isAW  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleCochainApplyBisimplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleCochainApplyBisimplex
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc

theorem evT_finsetSum {R : Type} [CommRing R] {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} {ι : Type} (S : Finset ι)
    (γ : ι → Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (∑ j ∈ S, γ j) a b s h U y = ∑ j ∈ S, evT (γ j) a b s h U y := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, evT_zero]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, evT_add, ih]

theorem evT_phi : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  intro q E N V B ℓ i z n α a b s h U y
  rw [phi_apply, evT_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [evT_crossT]
  have he : Even (2 * ((j : ℕ) : ℤ) * (a : ℤ)) := by
    rw [mul_assoc]; exact even_two_mul _
  rw [Int.negOnePow_even _ he, one_smul]

end GlobalTheory.PBFc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleCochainApplyBisimplexStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveBundleCochain_apply_bisimplex : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  first | (exact @GlobalTheory.PBFc.evT_phi) | (exact GlobalTheory.PBFc.evT_phi) | (intros; apply GlobalTheory.PBFc.evT_phi  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupDegreeZeroSupportCochain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupDegreeZeroSupportCochain
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.AWFront

theorem sub_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem ev_of_front {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k)
    (hγ : μ.IsAW hk α β γ)
    (hα : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U) :
    ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega)))
      (ev β N _ rfl U x) := by
  have key : ∀ (s : ℤ) (hs : s = n) (H : s + (-(N : ℤ) + m) = w) (h1 : -((0 : ℕ) : ℤ) + n = s),
      μ.mul U s (-(N : ℤ) + m) w H (ev α 0 s h1 U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) =
        μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro s rfl H h1
    rfl
  have gen : ∀ (p : ℕ), p = 0 → ∀ (H : -(p : ℤ) + n + (-((N - p : ℕ) : ℤ) + m) = w) (h1 : 0 + p ≤ N)
      (h2 : p + (N - p) ≤ N),
      (m * (p : ℤ)).negOnePow • μ.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w H
        (ev α p _ rfl U (x.sub 0 p h1)) (ev β (N - p) _ rfl U (x.sub p (N - p) h2)) =
      μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro p rfl H h1 h2
    have e1 : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub 0 (N - 0) h2 = x := sub_full x h2
    rw [e2]
    exact key _ (by simp) H rfl
  rw [hγ N w h U x, Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => ?_), add_zero]
  · exact gen _ (by simp) _ _ _
  · rw [hα (i.succ : ℕ) _ rfl U _ (by simp), map_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.AWFront
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupDegreeZeroSupportCochainStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain : ∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k), μ.IsAW hk α β γ → (∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0) → ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U), ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
  first | (exact @GlobalTheory.AWFront.ev_of_front) | (exact GlobalTheory.AWFront.ev_of_front) | (intros; apply GlobalTheory.AWFront.ev_of_front  <;> assumption)
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg

theorem ev_finset_sum {R : Type} [CommRing R] {S : Spc} {I : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (c : ι → Cochain ((chains R).obj S) I n) (p : ℕ) (t : ℤ) (h : -(p : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S p U) :
    ev (∑ j ∈ s, c j) p t h U x = ∑ j ∈ s, ev (c j) p t h U x := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ev_add, ih]

theorem col_identity (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (a : ℕ) (n m : ℤ) (hnm : n + -(a : ℤ) = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (c : ∀ j : Fin N, Cochain (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ)))) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ)))
    (ha : ∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X (-(a : ℤ))) ≫ (c j).v 0 r hr = (α j).v (-(a : ℤ)) r hr')
    (β : Cochain ((biChains (ZMod q) (twX E V)).X (-(a : ℤ))) (res _ (tw q i)) m)
    (hb : ∀ (k t : ℤ) (h : -(a : ℤ) + k = t) r hr hr', β.v k r hr =
      (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) k t h ≫ (phi q V ℓ i z n α).v t r hr')
    (γ : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a)))) (res _ (tw q i)) m)
    (hγ : ∀ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).IsAW (sub_add_cancel m _)
      ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _))
      ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) (γ j)) :
    (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m) = β := by
  ext k r hkr : 1
  by_cases hk : k ≤ 0
  · obtain ⟨b', rfl⟩ : ∃ b' : ℕ, k = -(b' : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [← cancel_epi (biChainsXIso (ZMod q) (twX E V) a b').inv]
    refine free_ext _ _ fun U y => ?_
    have e1 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫
        ((Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m)).v (-(b' : ℤ)) r hkr)
        (freeGen (ZMod q) _ U y) = ev (∑ j, γ j) b' r hkr U y := by
      rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% colCx_f]
      rfl
    have e2 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫ β.v (-(b' : ℤ)) r hkr) (freeGen (ZMod q) _ U y) =
        evT (phi q V ℓ i z n α) a b' r (by push_cast; omega) U y := by
      rw [hb (-(b' : ℤ)) (-((a + b' : ℕ) : ℤ)) (by push_cast; ring) r hkr (by push_cast; omega)]
      rfl
    rw [e1, e2, ev_finset_sum, GlobalTheory.T.projectiveBundleCochain_apply_bisimplex]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hA : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = t) (U' : Scheme.{0})
        (x : Sx ((twX E V).obj (op (SimplexCategory.mk a))) s U'), 0 < s →
        ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) s t h U' x = 0 := by
      intro s t h U' x hs
      erw [ev_pull]
      exact ev_prE_pos _ E a (c j) s t h U' _ hs
    rw [GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel m _) _ _ (γ j) (hγ j) hA b' r hkr U y]
    have hAv : ∀ (h0 : -((0 : ℕ) : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = m - 2 * ((j : ℕ) : ℤ)) (h00 : 0 + 0 ≤ b'),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) 0 (m - 2 * ((j : ℕ) : ℤ)) h0 U
          (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00) =
        Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 (m - 2 * ((j : ℕ) : ℤ)) (by simpa using h0))
          (freeGen (ZMod q) _ U (baseS V y)) := fun h0 h00 =>
      (ev_pull (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N))
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) 0 _ h0 U
        (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00)).trans
        (ev_prE_zero _ E a (c j) _ h0 U _)
    have hZv : ∀ (h2 : -(b' : ℤ) + 2 * ((j : ℕ) : ℤ) = -(b' : ℤ) + 2 * ((j : ℕ) : ℤ)),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) b'
          (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) h2 U y = EtC.ev (z j) b' _ rfl U (vertS V ℓ y) := fun h2 =>
      ev_pull (ℓ.app (op (SimplexCategory.mk a))) (z j) b' _ h2 U y
    refine (congrArg₂ (fun u v => (twPairI q i ((j : ℕ) : ℤ)).mul U (m - 2 * ((j : ℕ) : ℤ))
      (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r (by omega) u v) (hAv _ _) (hZv _)).trans ?_
    have key : ∀ (s : ℤ) (hs : -(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ)) = s) (h0 : 0 + (m - 2 * ((j : ℕ) : ℤ)) = s)
        (h1 : s + (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) = r),
        (twPairI q i ((j : ℕ) : ℤ)).mul U s (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r h1
          (Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 s h0) (freeGen (ZMod q) _ U (baseS V y)))
          (ev (z j) b' _ rfl U (vertS V ℓ y)) =
        (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r
          (by omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b' _ rfl U (vertS V ℓ y)) := by
      intro s hs
      subst hs
      intro h0 h1
      rw [ha j _ h0 (by omega)]
      rfl
    exact key _ (by omega) _ _
  · exact (biChains_isZero (twX E V) (-(a : ℤ)) k (Or.inr (by omega))).eq_of_src _ _

theorem graded_bijective : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  intro q _ E N V hE B ℓ i z hz hD p hp
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a : ℤ) := ⟨(-p).toNat, by omega⟩
  set P : PSh := E.obj (op (SimplexCategory.mk a)) with hPdef
  have hP : Inv q (disc.obj P) := fun U ⟨x⟩ =>
    hE U ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk a) 0).op).app (op U) x⟩
  have hpbf := hD P (trivV N (disc.obj P)) hP
  have hpi : ∀ m, Function.Bijective (fun (x : ∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ))))
      (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (j : Fin N) => cpull (prE _ E a) _ _ (x j)) := by
    intro m
    have hb := fun (j : Fin N) => LevelCmp.cpull_bij_of_heq (prEquiv (ZMod q) E a) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ))
    refine ⟨fun x y hxy => funext fun j => (hb j).1 (congrFun hxy j), fun y => ?_⟩
    exact ⟨fun j => ((hb j).2 (y j)).choose, funext fun j => ((hb j).2 (y j)).choose_spec⟩
  refine ⟨fun m x => cpull (colCx _ (twX E V) a).hom _ m (pull _ (colIso P (trivV N (disc.obj P))).hom _ m
    (pbfMap q (trivV N (disc.obj P)) m i (fun j => cpull (prE _ E a) _ _ (x j)))), fun m => ?_, ?_⟩
  · exact (LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso (colCx _ (twX E V) a)) _ m).comp
      ((LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso ((chains (ZMod q)).mapIso (colIso P (trivV N (disc.obj P))))) _ m).comp
        ((hpbf m i).comp (hpi m)))
  · intro n m hnm α hα ac b ha hb
    let A : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ptimes.fst P (Fib N))))
        (zcomp (Cocycle.ofHom (prE _ E a)) (ac j) (zero_add _)) (zero_add _)
    let Z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)
    choose γ hγ using fun j : Fin N => Pair.aw_exists (twPairI q i ((j : ℕ) : ℤ)) ((twX E V).obj (op (SimplexCategory.mk a)))
      (sub_add_cancel m (2 * ((j : ℕ) : ℤ))) (A j) (Z j)
    have hterm : ∀ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _
        (cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) =
        CohomologyClass.mk (γ j) := by
      intro j
      rw [← hz a j]
      exact GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney q i j m (A j) (Z j) (γ j) (hγ j)
    change cpull _ _ m (pull _ _ _ m (pbfMap q (trivV N (disc.obj P)) m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))) = _
    have h1 := pull_colIso_pbfMap q P (trivV N (disc.obj P)) hP m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j)))
    erw [h1]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    erw [mk_sum_cocycle]
    change CohomologyClass.mk (zcomp _ _ _) = _
    congr 1
    apply Cocycle.ext
    change (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j).1 (zero_add m) = b.1
    have hsum : ∀ s : Finset (Fin N), (∑ j ∈ s, γ j).1 = ∑ j ∈ s, (γ j).1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | @insert j s hj ih => simp only [Finset.sum_insert hj, Cocycle.coe_add, ih]
    rw [hsum]
    exact col_identity q V ℓ i (fun j => (z j).1) a n m hnm α (fun j => (ac j).1) ha b.1 hb (fun j => (γ j).1) hγ

end GlobalTheory.PBFg
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_cocycle_simplicial_levels_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  first | (exact @GlobalTheory.PBFg.graded_bijective) | (exact GlobalTheory.PBFg.graded_bijective) | (intros; apply GlobalTheory.PBFg.graded_bijective  <;> assumption)
