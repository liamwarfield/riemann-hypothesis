module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

variable {ι : Type} [LinearOrder ι] {A : Type} [CommRing A]
  {P : Finset ι → Type} [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)]
  [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)]
  (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')

def glueD : (∀ i : ι, P {i}) →ₗ[MvPolynomial ι A] ∀ k : ι × ι, P {k.1, k.2} :=
  LinearMap.pi fun k => res _ _ (sub_pair_left k.1 k.2) ∘ₗ LinearMap.proj k.1 -
    res _ _ (sub_pair_right k.1 k.2) ∘ₗ LinearMap.proj k.2

def glue : Submodule (MvPolynomial ι A) (∀ i : ι, P {i}) := LinearMap.ker (glueD res)

variable {res} in
theorem mem_glue {c : ∀ i : ι, P {i}} : c ∈ glue res ↔
    ∀ i j, res {i} {i, j} (sub_pair_left i j) (c i) = res {j} {i, j} (sub_pair_right i j) (c j) := by
  rw [glue, LinearMap.mem_ker]
  constructor
  · intro h i j
    have hk := congrFun h (i, j)
    simpa [glueD, sub_eq_zero] using hk
  · intro h
    funext k
    simp [glueD, sub_eq_zero, h k.1 k.2]

def evAt (i : ι) (I : Finset ι) (hi : i ∈ I) : glue res →ₗ[MvPolynomial ι A] P I :=
  res {i} I (Finset.singleton_subset_iff.2 hi) ∘ₗ LinearMap.proj i ∘ₗ (glue res).subtype

theorem evAt_apply (i : ι) (I : Finset ι) (hi : i ∈ I) (m : glue res) :
    evAt res i I hi m = res {i} I (Finset.singleton_subset_iff.2 hi) (m.1 i) := rfl

def ev (I : Finset ι) (hI : I.Nonempty) : glue res →ₗ[MvPolynomial ι A] P I :=
  evAt res (I.min' hI) I (I.min'_mem hI)

variable {res}

theorem evAt_eq (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    {i i' : ι} {I : Finset ι} (hi : i ∈ I) (hi' : i' ∈ I) (m : glue res) :
    evAt res i I hi m = evAt res i' I hi' m := by
  have hsub : ({i, i'} : Finset ι) ⊆ I := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hi'
  have hm := (mem_glue.1 m.2) i i'
  have e1 : res {i} I (Finset.singleton_subset_iff.2 hi) (m.1 i) =
      res {i, i'} I hsub (res {i} {i, i'} (sub_pair_left i i') (m.1 i)) :=
    (hcomp _ _ _ _ _ _).symm
  have e2 : res {i'} I (Finset.singleton_subset_iff.2 hi') (m.1 i') =
      res {i, i'} I hsub (res {i'} {i, i'} (sub_pair_right i i') (m.1 i')) :=
    (hcomp _ _ _ _ _ _).symm
  rw [evAt_apply, evAt_apply, e1, e2, hm]

theorem ev_eq (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    {i : ι} {I : Finset ι} (hI : I.Nonempty) (hi : i ∈ I) (m : glue res) :
    ev res I hI m = res {i} I (Finset.singleton_subset_iff.2 hi) (m.1 i) := by
  show evAt res (I.min' hI) I (I.min'_mem hI) m = _
  rw [evAt_eq hcomp (I.min'_mem hI) hi m, evAt_apply]

theorem res_ev (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    {I J : Finset ι} (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (m : glue res) :
    res I J h (ev res I hI m) = ev res J hJ m := by
  have hi := I.min'_mem hI
  rw [ev_eq hcomp hI hi, ev_eq hcomp hJ (h hi), hcomp]

variable [Fintype ι] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, DirectSum.Decomposition (𝒢 S)]

omit [Fintype ι] [∀ S, DirectSum.Decomposition (𝒢 S)] in
theorem isGradedMap_glueD (hgr : ∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) :
    IsGradedMap (grPi fun i : ι => 𝒢 {i}) (grPi fun k : ι × ι => 𝒢 {k.1, k.2}) (glueD res) := by
  unfold glueD
  refine IsGradedMap.pi fun k => ?_
  beta_reduce
  rw [sub_eq_add_neg]
  exact ((hgr _ _ _).comp (isGradedMap_piProj _ _ k.1)).add
    ((hgr _ _ _).comp (isGradedMap_piProj _ _ k.2)).neg


variable (res) in
def glueGr : ℤ → Submodule A (glue res) := grSub (grPi fun i : ι => 𝒢 {i}) (glue res)

@[instance_reducible]
def glueDec (hgr : ∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) :
    DirectSum.Decomposition (glueGr res 𝒢) :=
  grSubDecomposition _ (isGradedMap_glueD 𝒢 hgr).isHomogeneous_ker

omit [Fintype ι] [∀ S, DirectSum.Decomposition (𝒢 S)] in
instance glueGr.polyGradedSMul [∀ S, PolyGradedSMul ι (𝒢 S)] :
    PolyGradedSMul ι (glueGr res 𝒢) :=
  grSub.polyGradedSMul _ _

omit [Fintype ι] [∀ S, DirectSum.Decomposition (𝒢 S)] in
theorem isGradedMap_ev (hgr : ∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h))
    (I : Finset ι) (hI : I.Nonempty) : IsGradedMap (glueGr res 𝒢) (𝒢 I) (ev res I hI) := by
  unfold ev evAt glueGr
  exact (hgr _ _ _).comp ((isGradedMap_piProj _ _ _).comp (isGradedMap_subtype _ _))

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.XProdPowSmulMemRangeResIter
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem xProd_pow_smul_mem_range_res_iter : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (T S : Finset ι) (b : P (S ∪ T)), S.Nonempty → ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S (S ∪ T) Finset.subset_union_left)) := by
  intro ι _ A _ P _ _ res hid hcomp hstep
  have hA : ∀ (S0 U : Finset ι) (h : S0 ⊆ U) (j : ι), U ⊆ insert j S0 → ∀ b : P U, S0.Nonempty →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S0 U h) := by
    intro S0 U h j hU b hS0
    by_cases hj : j ∈ U
    · obtain rfl : U = insert j S0 := subset_antisymm hU (Finset.insert_subset hj h)
      exact hstep S0 j b hS0
    · have hUS : U ⊆ S0 := by
        intro x hx
        rcases Finset.mem_insert.mp (hU hx) with hx' | hx'
        · subst hx'
          exact absurd hx hj
        · exact hx'
      obtain rfl : U = S0 := subset_antisymm hUS h
      exact ⟨0, LinearMap.mem_range.mpr ⟨b, by rw [hid, pow_zero, one_smul]⟩⟩
  have hQ : ∀ T : Finset ι, ∀ (S U : Finset ι) (h : S ⊆ U), U ⊆ S ∪ T → ∀ b : P U, S.Nonempty →
      ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S U h) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro S U h hU b hS
      obtain rfl : U = S := subset_antisymm (by simpa using hU) h
      exact ⟨0, LinearMap.mem_range.mpr ⟨b, by rw [hid, pow_zero, one_smul]⟩⟩
    | insert j T hj ih =>
      intro S U h hU b hS
      have hSV : S ⊆ S ∪ U.erase j := Finset.subset_union_left
      have hVU : S ∪ U.erase j ⊆ U := Finset.union_subset h (Finset.erase_subset j U)
      have hUV : U ⊆ insert j (S ∪ U.erase j) := by
        intro x hx
        by_cases hxj : x = j
        · subst hxj
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxj, hx⟩))
      have hVT : S ∪ U.erase j ⊆ S ∪ T := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ hx
        · obtain ⟨hxj, hxU⟩ := Finset.mem_erase.mp hx
          rcases Finset.mem_union.mp (hU hxU) with h1 | h1
          · exact Finset.mem_union_left _ h1
          · rcases Finset.mem_insert.mp h1 with h2 | h2
            · exact absurd h2 hxj
            · exact Finset.mem_union_right _ h2
      have hVne : (S ∪ U.erase j).Nonempty := hS.mono hSV
      obtain ⟨k, hk⟩ := hA (S ∪ U.erase j) U hVU j hUV b hVne
      obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hk
      obtain ⟨l, hl⟩ := ih S (S ∪ U.erase j) hSV hVT c hS
      obtain ⟨d, hd⟩ := LinearMap.mem_range.mp hl
      refine ⟨k + l, ?_⟩
      have hmem : xProd A T ^ l • (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈
          LinearMap.range (res S U h) := by
        refine LinearMap.mem_range.mpr ⟨d, ?_⟩
        rw [← hc, ← (res (S ∪ U.erase j) U hVU).map_smul, ← hd, hcomp]
      have heq : xProd A (insert j T) ^ (k + l) • b =
          ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T ^ k) •
            (xProd A T ^ l • (MvPolynomial.X j : MvPolynomial ι A) ^ k • b) := by
        rw [smul_smul, smul_smul]
        congr 1
        simp only [GlobalTheory.xProd, Finset.prod_insert hj]
        ring
      rw [heq]
      exact Submodule.smul_mem _ _ hmem
  intro T S b hS
  exact hQ T S (S ∪ T) Finset.subset_union_left (Finset.Subset.refl _) b hS

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCoboundaryOfPairsCocycle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem cube_res_injective_of_eq {ι : Type} {A : Type} [CommRing A] (C : Cube.{0} ι A)
    {s t : Finset ι} (e : s = t) (h : s ⊆ t) : Function.Injective (Cube.res C h) := by
  subst e
  intro x y hxy
  rwa [GlobalTheory.Cube.res_self, GlobalTheory.Cube.res_self] at hxy

theorem cube_pairs_diag {ι : Type} [LinearOrder ι] {A : Type} [CommRing A] (C : Cube.{0} ι A)
    (c : ∀ i j : ι, C.obj {i, j})
    (hc : ∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) +
      Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k))
    (i : ι) : c i i = 0 := by
  have hx := hc i i i
  rw [add_eq_left] at hx
  apply GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_res_injective_of_eq C (s := {i, i}) (t := {i, i, i}) (by ext; simp)
    (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_triple_ij i i i)
  rw [map_zero]
  exact hx

theorem exists_coboundary_of_pairs_cocycle : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (C : Cube.{0} ι A), Function.Exact (Cube.d C 1) (Cube.d C 2) → ∀ c : ∀ i j : ι, C.obj {i, j}, (∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) + Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, C.obj {i}, ∀ i j, c i j = Cube.res C (sub_pair_left i j) (b i) - Cube.res C (sub_pair_right i j) (b j) := by
  intro ι _ A _ C hex c hc
  have hne : ∀ s : Finset ι, s.card = 2 → s.Nonempty := fun s hs => Finset.card_pos.1 (by omega)
  have hmm : ∀ (s : Finset ι) (hs : s.card = 2), ({s.min' (hne s hs), s.max' (hne s hs)} : Finset ι) ⊆ s :=
    fun s hs => Finset.insert_subset (Finset.min'_mem _ _)
      (Finset.singleton_subset_iff.2 (Finset.max'_mem _ _))
  have htr : ∀ {a b a' b' : ι} (ha : a = a') (hb : b = b') (h : ({a, b} : Finset ι) ⊆ {a', b'}),
      GlobalTheory.Cube.res C h (c a b) = c a' b' := by
    intro a b a' b' ha hb h
    subst ha hb
    exact GlobalTheory.Cube.res_self C h _
  let y : GlobalTheory.Cube.Term C 2 := fun s =>
    -GlobalTheory.Cube.res C (hmm s.1 s.2) (c (s.1.min' (hne s.1 s.2)) (s.1.max' (hne s.1 s.2)))
  have hy : ∀ {i j : ι} (hij : i < j) (hs : ({i, j} : Finset ι).card = 2), y ⟨{i, j}, hs⟩ = -c i j := by
    intro i j hij hs
    have hmin : ({i, j} : Finset ι).min' (hne _ hs) = i :=
      le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [hij.le]))
    have hmax : ({i, j} : Finset ι).max' (hne _ hs) = j :=
      le_antisymm (Finset.max'_le _ _ _ (by simp [hij.le])) (Finset.le_max' _ _ (by simp))
    exact congrArg Neg.neg (htr hmin hmax _)
  have hy0 : GlobalTheory.Cube.d C 2 y = 0 := by
    funext ⟨t, ht⟩
    show _ = 0
    obtain ⟨i, j, k, hij, hjk, rfl⟩ := GlobalTheory.AbLaw.CechOne.exists_triple (t := t) ht
    rw [GlobalTheory.AbLaw.CechOne.d_two_apply_triple C y hij hjk ht, hy hij, hy hjk, hy (hij.trans hjk)]
    simp only [map_neg]
    rw [← hc i j k]
    abel
  obtain ⟨x, hx⟩ := (hex y).1 hy0
  have hlt : ∀ i j, i < j → c i j =
      GlobalTheory.Cube.res C (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_pair_left i j) (x ⟨{i}, Finset.card_singleton i⟩) -
        GlobalTheory.Cube.res C (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_pair_right i j) (x ⟨{j}, Finset.card_singleton j⟩) := by
    intro i j hij
    have h1 := GlobalTheory.Cube.d_one_apply_pair C x hij
    rw [hx, hy hij] at h1
    rw [← neg_sub, ← h1, neg_neg]
  refine ⟨fun i => x ⟨{i}, Finset.card_singleton i⟩, fun i j => ?_⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hlt i j hij
  · rw [GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_pairs_diag C c hc i, sub_self]
  · apply GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_res_injective_of_eq C (s := {i, j}) (t := {i, j, i})
      (by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (GlobalTheory.CompanionTheory.FormalAlg.Lift.sub_triple_ij i j i)
    have h := hc i j i
    rw [GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.cube_pairs_diag C c hc i, map_zero] at h
    rw [eq_neg_of_add_eq_zero_left h, hlt j i hji]
    simp only [map_sub, neg_sub, GlobalTheory.Cube.res_res]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfEvEqZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem smul_eq_zero_of_ev_eq_zero : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) → ∀ (I : Finset ι) (hI : I.Nonempty) (m : glue res), ev res I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0 := by
  intro ι _ _ A _ P _ _ _ _ res hcomp H I hI m hm
  have key : ∀ i, res {i} ({i} ∪ I) Finset.subset_union_left (m.1 i) = 0 := by
    intro i
    have hJ : ({i} ∪ I).Nonempty := ⟨i, Finset.mem_union_left I (Finset.mem_singleton_self i)⟩
    have h1 := ev_eq hcomp hJ (Finset.mem_union_left I (Finset.mem_singleton_self i)) m
    have h2 := res_ev hcomp hI hJ Finset.subset_union_right m
    rw [hm, map_zero] at h2
    exact h1.symm.trans h2.symm
  choose L hL using fun i => H I {i} (m.1 i) (Finset.singleton_nonempty i) (key i)
  refine ⟨∑ j, L j, ?_⟩
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_zero, Pi.zero_apply]
  have hsum : ∑ j, L j = (∑ j, L j - L i) + L i :=
    (Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [hsum, pow_add, mul_smul, hL i, smul_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionCompatibleIteratedInjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.IterInj

theorem restriction_compatible_iterated_injective (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type)
    [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)]
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (hid : ∀ S (h : S ⊆ S) a, res S S h a = a)
    (hcomp : ∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a)
    (hloc : ∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty →
      res S (insert j S) (Finset.subset_insert j S) a = 0 →
      ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0)
    (S : Finset ι) (hS : S.Nonempty) (T : Finset ι) :
    ∀ (S' : Finset ι) (_ : S' = S ∪ T) (h : S ⊆ S') (a : P S), res S S' h a = 0 →
      ∃ l : ℕ, xProd A T ^ l • a = 0 := by
  induction T using Finset.induction_on with
  | empty =>
    intro S' hS' h a ha
    have : S' = S := by simpa using hS'
    subst this
    refine ⟨0, ?_⟩
    rw [hid] at ha
    simpa using ha
  | insert j T' hj ih =>
    intro S' hS' h a ha
    have hS'' : S' = insert j (S ∪ T') := by
      rw [hS', Finset.union_insert]
    subst hS''
    have hsub : S ⊆ S ∪ T' := Finset.subset_union_left
    have hb : res (S ∪ T') (insert j (S ∪ T')) (Finset.subset_insert j _) (res S (S ∪ T') hsub a) = 0 := by
      rw [hcomp]; exact ha
    obtain ⟨k, hk⟩ := hloc (S ∪ T') j _ (hS.mono hsub) hb
    have h2 : res S (S ∪ T') hsub ((MvPolynomial.X j : MvPolynomial ι A) ^ k • a) = 0 := by
      rw [map_smul]; exact hk
    obtain ⟨l, hl⟩ := ih (S ∪ T') rfl hsub _ h2
    refine ⟨k + l, ?_⟩
    have hx : xProd A (insert j T') = MvPolynomial.X j * xProd A T' := by
      simp [xProd, Finset.prod_insert hj]
    have : (xProd A (insert j T')) ^ (k + l) =
        ((MvPolynomial.X j : MvPolynomial ι A) ^ l * xProd A T' ^ k) *
          (xProd A T' ^ l * (MvPolynomial.X j : MvPolynomial ι A) ^ k) := by
      rw [hx, mul_pow]; ring
    rw [this, mul_smul _ (xProd A T' ^ l * _), mul_smul (xProd A T' ^ l), hl, smul_zero]

theorem iter_localisation_injective : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) := by
  intro ι _ A _ P _ _ res hid hcomp hloc T S a hS ha
  exact restriction_compatible_iterated_injective ι A P res hid hcomp hloc S hS T (S ∪ T) rfl Finset.subset_union_left a ha

end GlobalTheory.CompanionTheory.FormalAlg.IterInj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHomLocPiecesCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_homLoc_pieces_compatible : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (M : Type) [AddCommGroup M] [Module A M] [Module (MvPolynomial ι A) M] [IsScalarTower A (MvPolynomial ι A) M] (ℳ : ℤ → Submodule A M) [PolyGradedSMul ι ℳ] [DirectSum.Decomposition ℳ] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S') (ev : ∀ I : Finset ι, I.Nonempty → M →ₗ[MvPolynomial ι A] P I), (∀ I hI, IsGradedMap ℳ (𝒢 I) (ev I hI)) → (∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) m, res I J h (ev I hI m) = ev J hJ m) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ I (hI : I.Nonempty) (m : M), ev I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0) → (∀ I (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : M), ev I hI m = xProd A I ^ l • f) → ∀ t : ℤ, ∃ φ : ∀ I : Finset ι, I.Nonempty → (homLoc ℳ I t →ₗ[A] 𝒢 I t), (∀ I hI, Function.Bijective (φ I hI)) ∧ ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : homLoc ℳ I t), (φ J hJ (homLocRes ℳ h t z) : P J) = res I J h (φ I hI z : P I) := by
  intro ι _ A _ M _ _ _ _ ℳ _ _ P _ _ _ _ 𝒢 _ _ res ev hgr hres hX hker hcok t
  have key : ∀ (I : Finset ι) (hI : I.Nonempty), ∃ φ : homLoc ℳ I t →ₗ[A] 𝒢 I t,
      Function.Bijective φ ∧ ∀ (z : homLoc ℳ I t) (k : ℕ) (m : M),
        awayFrac M (xProd A I) k m = z → xProd A I ^ k • (φ z : P I) = ev I hI m := by
    intro I hI
    exact exists_homLoc_bijective_of (hgr I hI) I
      (xProd_smul_bijective_of I fun i hi => hX i I hi)
      (fun _ y _ hy => hker I hI y hy) (fun _ a _ => hcok I hI a) t
  choose φ hφbij hφ using key
  refine ⟨φ, hφbij, ?_⟩
  intro I J hI hJ h z
  have hb : Function.Bijective fun x : P J => xProd A J • x :=
    xProd_smul_bijective_of J fun i hi => hX i J hi
  have hinj : ∀ (n : ℕ) (x y : P J), xProd A J ^ n • x = xProd A J ^ n • y → x = y := by
    intro n
    induction n with
    | zero => intro x y hxy; simpa using hxy
    | succ n ih =>
      intro x y hxy
      apply ih
      apply hb.1
      show xProd A J • (xProd A J ^ n • x) = xProd A J • (xProd A J ^ n • y)
      rw [← mul_smul, ← mul_smul, ← pow_succ']
      exact hxy
  obtain ⟨k, m, hkm⟩ := exists_awayFrac (z : LocalizedModule.Away (xProd A I) M)
  have hc : xProd A J = (∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) * xProd A I :=
    (Finset.prod_sdiff h).symm
  have hz : (homLocRes ℳ h t z : LocalizedModule.Away (xProd A J) M) =
      awayFrac M (xProd A J) k ((∏ i ∈ J \ I, (MvPolynomial.X i : MvPolynomial ι A)) ^ k • m) := by
    rw [coe_homLocRes, ← hkm]
    exact locRes_awayFrac MvPolynomial.X h (Finset.prod_sdiff h).symm k m
  have h1 := hφ I hI z k m hkm
  have h2 := hφ J hJ (homLocRes ℳ h t z) k _ hz.symm
  apply hinj k
  rw [h2, map_smul, ← hres I J hI hJ h m, ← h1, map_smul, ← mul_smul, ← mul_pow, hc]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompatibleFamilyOfSingleton
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_compatible_family_of_singleton : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) := by
  intro ι _ _ A _ P _ _ res hid hcomp hker hext i f
  have inj : ∀ (S S' : Finset ι) (h : S ⊆ S'), S = S' → Function.Injective (res S S' h) := by
    rintro S _ h rfl a b hab
    rwa [hid, hid] at hab
  set x : MvPolynomial ι A := MvPolynomial.X i with hx

  have h1 : ∀ j : ι, ∃ (k : ℕ) (g : P {j}),
      res {j} {i, j} (sub_pair_right i j) g = x ^ k • res {i} {i, j} (sub_pair_left i j) f := by
    intro j
    obtain ⟨k, g, hg⟩ := hext {j} i (res {i} {i, j} (sub_pair_left i j) f)
      (Finset.singleton_nonempty j)
    exact ⟨k, g, hg⟩
  choose k g hg using h1
  set K : ℕ := Finset.univ.sup k with hK
  have hkK : ∀ j, k j ≤ K := fun j => Finset.le_sup (Finset.mem_univ j)
  obtain ⟨f', hres⟩ : ∃ f' : ∀ j : ι, P {j}, ∀ j, res {j} {i, j} (sub_pair_right i j) (f' j)
      = x ^ K • res {i} {i, j} (sub_pair_left i j) f := by
    refine ⟨fun j => x ^ (K - k j) • g j, fun j => ?_⟩
    simp only [map_smul, hg, smul_smul, ← pow_add, Nat.sub_add_cancel (hkK j)]

  have htriple : ∀ (j : ι) (T : Finset ι) (hT : ({i, j} : Finset ι) ⊆ T),
      res {j} T ((sub_pair_right i j).trans hT) (f' j)
        = x ^ K • res {i} T ((sub_pair_left i j).trans hT) f := by
    intro j T hT
    rw [← hcomp _ _ _ (sub_pair_right i j) hT, hres, map_smul, hcomp]
  have h2 : ∀ j l : ι, ∃ n : ℕ, x ^ n • (res {j} {j, l} (sub_pair_left j l) (f' j)
      - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
    intro j l
    refine hker {j, l} i _ (Finset.insert_nonempty _ _) ?_
    have hj : ({i, j} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_left j l)
    have hl : ({i, l} : Finset ι) ⊆ insert i {j, l} :=
      Finset.insert_subset_insert i (sub_pair_right j l)
    rw [map_sub, hcomp, hcomp, sub_eq_zero]
    have e1 := htriple j _ hj
    have e2 := htriple l _ hl
    exact e1.trans e2.symm
  choose n hn using h2
  set N' : ℕ := Finset.univ.sup (fun p : ι × ι => n p.1 p.2) with hN'
  have hnN : ∀ j l, n j l ≤ N' := fun j l =>
    Finset.le_sup (f := fun p : ι × ι => n p.1 p.2) (Finset.mem_univ (j, l))
  refine ⟨fun j => x ^ N' • f' j, N' + K, ?_, ?_⟩
  · intro j l
    have h0 : x ^ N' • (res {j} {j, l} (sub_pair_left j l) (f' j)
        - res {l} {j, l} (sub_pair_right j l) (f' l)) = 0 := by
      rw [← Nat.sub_add_cancel (hnN j l), pow_add, mul_smul, hn, smul_zero]
    show res {j} {j, l} (sub_pair_left j l) (x ^ N' • f' j)
      = res {l} {j, l} (sub_pair_right j l) (x ^ N' • f' l)
    rw [map_smul, map_smul, ← sub_eq_zero, ← smul_sub]
    exact h0
  · have hii : ({i} : Finset ι) ⊆ {i, i} := sub_pair_left i i
    have hfi : f' i = x ^ K • f := by
      apply inj {i} {i, i} hii (Finset.pair_eq_singleton i).symm
      rw [map_smul]
      exact hres i
    show x ^ N' • f' i = x ^ (N' + K) • f
    rw [hfi, smul_smul, ← pow_add]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsXProdPowSmulEqEv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_xProd_pow_smul_eq_ev : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (b : P (S ∪ T)), S.Nonempty → ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S (S ∪ T) Finset.subset_union_left)) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) → ∀ (I : Finset ι) (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : glue res), ev res I hI m = xProd A I ^ l • f := by
  intro ι _ A _ P _ _ _ _ res hcomp hsurj hfam I hI f
  classical
  obtain ⟨i, hi⟩ := hI
  have hsub : ({i} : Finset ι) ⊆ I := Finset.singleton_subset_iff.2 hi
  have key : ∀ (J : Finset ι) (hJ : {i} ∪ I = J) (g : P J),
      ∃ (l : ℕ) (a : P {i}), res {i} J (hJ ▸ Finset.subset_union_left) a = xProd A I ^ l • g := by
    intro J hJ
    subst hJ
    intro g
    obtain ⟨l, a, ha⟩ := hsurj I {i} g ⟨i, Finset.mem_singleton_self i⟩
    exact ⟨l, a, ha⟩
  obtain ⟨l, a, ha⟩ := key I (Finset.union_eq_right.2 hsub) f
  obtain ⟨c, N, hc, hci⟩ := hfam i a
  obtain ⟨q, hq⟩ : (MvPolynomial.X i : MvPolynomial ι A) ∣ xProd A I := by
    simpa [xProd] using Finset.dvd_prod_of_mem (fun j => (MvPolynomial.X j : MvPolynomial ι A)) hi
  refine ⟨N + l, q ^ N • ⟨c, mem_glue.2 hc⟩, ?_⟩
  rw [map_smul, ev_eq hcomp ⟨i, hi⟩ hi]
  change q ^ N • res {i} I hsub (c i) = _
  rw [hci, map_smul, show res {i} I hsub a = xProd A I ^ l • f from ha, hq, smul_smul, smul_smul,
    pow_add, mul_pow]
  congr 1
  ring

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SaturatedFgOfPowerTorsionKerCoker
namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat

theorem saturated_fg_of_powerTorsion_ker_coker :
    ∀ (B : Type) [CommRing B] (x : B) (M N : Type) [AddCommGroup M] [Module B M]
      [AddCommGroup N] [Module B N] (e : M →ₗ[B] N),
      (∀ m, e m = 0 → ∃ l : ℕ, x ^ l • m = 0) →
      (∀ f, ∃ (l : ℕ) (m : M), e m = x ^ l • f) →
      (∃ s : Finset N, ∀ f : N, ∃ k : ℕ, x ^ k • f ∈ Submodule.span B (s : Set N)) →
      ∃ T : Finset M, ∀ m : M, ∃ k : ℕ, x ^ k • m ∈ Submodule.span B (T : Set M) := by
  classical
  intro B _ x M N _ _ _ _ e hker hcoker hfg
  obtain ⟨s, hs⟩ := hfg
  choose l lift hlift using hcoker
  set L := ∑ n ∈ s, l n with hL
  have key : ∀ f ∈ Submodule.span B (s : Set N),
      ∃ t ∈ Submodule.span B ((s.image lift : Finset M) : Set M), e t = x ^ L • f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem n hn =>
      refine ⟨x ^ (L - l n) • lift n, Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem lift hn))), ?_⟩
      rw [map_smul, hlift, smul_smul, ← pow_add,
        Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn)]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨ta, hta, ea⟩ := ha
      obtain ⟨tb, htb, eb⟩ := hb
      exact ⟨ta + tb, add_mem hta htb, by rw [map_add (f := _), ea, eb, smul_add]⟩
    | smul c a _ ha =>
      obtain ⟨t, ht, et⟩ := ha
      exact ⟨c • t, Submodule.smul_mem _ _ ht, by rw [map_smul, et, smul_comm]⟩
  refine ⟨s.image lift, fun m0 => ?_⟩
  obtain ⟨k, hk⟩ := hs (e m0)
  obtain ⟨t, ht, et⟩ := key _ hk
  have he : e (x ^ (L + k) • m0 - t) = 0 := by
    rw [map_sub, map_smul, et, smul_smul, ← pow_add, sub_self]
  obtain ⟨l', hl'⟩ := hker _ he
  refine ⟨l' + (L + k), ?_⟩
  have hm : x ^ (l' + (L + k)) • m0 = x ^ l' • t := by
    rw [smul_sub, smul_smul, ← pow_add, sub_eq_zero] at hl'
    exact hl'
  rw [hm]
  exact Submodule.smul_mem _ _ ht

end GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedModuleSystemRestriction
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue


open MvPolynomial in
theorem exists_finite_sub (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [DirectSum.Decomposition 𝒢]
    (h : ∀ i : ι, ∃ T : Finset G, ∀ y : G, ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set G)) :
    ∃ K : Submodule (MvPolynomial ι R) G, K.IsHomogeneous 𝒢 ∧
      Module.Finite (MvPolynomial ι R) K ∧ ∀ (t : ℤ) (I : Finset ι), I.Nonempty →
        Function.Bijective (homLocMap (isGradedMap_subtype 𝒢 K) I t) := by
  obtain ⟨r, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 h
  have hhom : (Submodule.span (MvPolynomial ι R) (Set.range g)).IsHomogeneous 𝒢 :=
    isHomogeneous_span_gr 𝒢 (by
      rintro _ ⟨l, rfl⟩
      exact ⟨d l, hg l⟩)
  refine ⟨_, hhom, Module.Finite.span_of_finite _ (Set.finite_range g), fun t I ⟨i, hi⟩ => ?_⟩
  letI := grSubDecomposition 𝒢 hhom
  exact homLocMap_bijective_of_X _ hi
    (fun m hm => ⟨0, by
      rw [(map_eq_zero_iff _ (Submodule.injective_subtype _)).1 hm, smul_zero]⟩)
    (fun y => by simpa using hsat i y) t

theorem pairs_of_cube {ι : Type} [LinearOrder ι] {A : Type} [CommRing A] (C : Cube.{0} ι A)
    (hpairs : ∀ c : ∀ i j : ι, C.obj {i, j}, (∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) +
      Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k)) →
      ∃ b : ∀ i : ι, C.obj {i}, ∀ i j, c i j = Cube.res C (sub_pair_left i j) (b i) -
        Cube.res C (sub_pair_right i j) (b j))
    {P : Finset ι → Type} [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)]
    [∀ S, Module (MvPolynomial ι A) (P S)]
    (Qs : ∀ S, Submodule A (P S))
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (ψ : ∀ I : Finset ι, I.Nonempty → (C.obj I →ₗ[A] Qs I))
    (hb : ∀ I hI, Function.Bijective (ψ I hI))
    (hr : ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : C.obj I),
      (ψ J hJ (Cube.res C h z) : P J) = res I J h (ψ I hI z : P I))
    (c : ∀ i j : ι, P {i, j}) (hc : ∀ i j, c i j ∈ Qs {i, j})
    (hcoc : ∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) +
      res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) =
        res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) :
    ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ Qs {i}) ∧
      ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) -
        res {j} {i, j} (sub_pair_right i j) (b j) := by
  have n2 (i j : ι) : ({i, j} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  have n1 (i : ι) : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  have n3 (i j k : ι) : ({i, j, k} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  choose c' hc' using fun i j => (hb {i, j} (n2 i j)).2 ⟨c i j, hc i j⟩
  have hv (i j : ι) : (ψ _ (n2 i j) (c' i j) : P {i, j}) = c i j := congrArg Subtype.val (hc' i j)
  obtain ⟨b', hb'⟩ := hpairs c' fun i j k => by
    refine (hb _ (n3 i j k)).1 (Subtype.ext ?_)
    rw [map_add (f := _), Submodule.coe_add, hr _ _ (n2 i j) (n3 i j k), hr _ _ (n2 j k) (n3 i j k),
      hr _ _ (n2 i k) (n3 i j k), hv, hv, hv, hcoc]
  refine ⟨fun i => ψ _ (n1 i) (b' i), fun i => (ψ _ (n1 i) (b' i)).2, fun i j => ?_⟩
  rw [← hv i j, hb' i j, map_sub, Submodule.coe_sub, hr _ _ (n1 i) (n2 i j),
    hr _ _ (n1 j) (n2 i j)]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem serre_cech_pairs : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] [IsNoetherianRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) → (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ i : ι, ∃ s : Finset (P {i}), ∀ m : P {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι A) ^ k • m ∈ Submodule.span (MvPolynomial ι A) (s : Set (P {i}))) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ c : ∀ i j : ι, P {i, j}, (∀ i j, c i j ∈ 𝒢 {i, j} t) → (∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ 𝒢 {i} t) ∧ ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) - res {j} {i, j} (sub_pair_right i j) (b j) := by
  intro ι _ _ A _ _ P _ _ _ _ 𝒢 _ _ res hgr hid hcomp hbij hinj hsurj hfin
  have iI := GlobalTheory.CompanionTheory.FormalAlg.IterInj.iter_localisation_injective ι A P res hid hcomp hinj
  have iS := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.xProd_pow_smul_mem_range_res_iter ι A P res hid hcomp hsurj
  have g1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_compatible_family_of_singleton ι A P res hid hcomp hinj hsurj
  have K1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.smul_eq_zero_of_ev_eq_zero ι A P res hcomp iI
  have K2 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_xProd_pow_smul_eq_ev ι A P res hcomp iS g1
  letI : DirectSum.Decomposition (glueGr res 𝒢) := glueDec 𝒢 hgr
  have sat : ∀ i : ι, ∃ T : Finset (glue res), ∀ y : glue res, ∃ k : ℕ,
      (MvPolynomial.X i : MvPolynomial ι A) ^ k • y ∈
        Submodule.span (MvPolynomial ι A) (T : Set (glue res)) := by
    intro i
    refine GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat.saturated_fg_of_powerTorsion_ker_coker (MvPolynomial ι A) (MvPolynomial.X i) (glue res) (P {i})
      (ev res {i} (Finset.singleton_nonempty i)) (fun m hm => ?_) (fun f => ?_) (hfin i)
    · simpa [xProd] using K1 {i} _ m hm
    · simpa [xProd] using K2 {i} (Finset.singleton_nonempty i) f
  obtain ⟨K, hK, hKf, hb⟩ := exists_finite_sub ι A (glue res) (glueGr res 𝒢) sat
  letI := grSubDecomposition (glueGr res 𝒢) hK
  obtain ⟨t₀, ht₀⟩ := cubeComplex_grCube_exactAt_of_finite ι A K (grSub (glueGr res 𝒢) K) hKf
  refine ⟨t₀, fun t ht c hc hcoc => ?_⟩
  have hex := (cechComplex_exactAt_succ_iff _ 0).1
    ((cechComplex_exactAt_succ_iff_cube _ 0).2 (ht₀ t ht 2))
  obtain ⟨φ, hφb, hφr⟩ := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_homLoc_pieces_compatible ι A (glue res) (glueGr res 𝒢) P 𝒢 res (ev res)
    (isGradedMap_ev 𝒢 hgr) (fun I J hI hJ h m => res_ev hcomp hI hJ h m) hbij K1 K2 t
  refine pairs_of_cube (grCube ι (grSub (glueGr res 𝒢) K) t) (GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_coboundary_of_pairs_cocycle ι A _ hex)
    (fun S => 𝒢 S t) res
    (fun I hI => φ I hI ∘ₗ homLocMap (isGradedMap_subtype _ K) I t)
    (fun I hI => (hφb I hI).comp (hb t I hI)) (fun I J hI hJ h z => ?_) c hc hcoc
  have e : homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) J t (Cube.res _ h z) =
      homLocRes _ h t (homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) I t z) :=
    homLocMap_homLocRes _ h t z
  exact (congrArg (fun w => ((φ J hJ w : 𝒢 J t) : P J)) e).trans (hφr I J hI hJ h _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedModuleSystemRestrictionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_module_system_restriction : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] [IsNoetherianRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) → (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ i : ι, ∃ s : Finset (P {i}), ∀ m : P {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι A) ^ k • m ∈ Submodule.span (MvPolynomial ι A) (s : Set (P {i}))) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ c : ∀ i j : ι, P {i, j}, (∀ i j, c i j ∈ 𝒢 {i, j} t) → (∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ 𝒢 {i} t) ∧ ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) - res {j} {i, j} (sub_pair_right i j) (b j) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.serre_cech_pairs | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.serre_cech_pairs | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.serre_cech_pairs <;> assumption)
end
