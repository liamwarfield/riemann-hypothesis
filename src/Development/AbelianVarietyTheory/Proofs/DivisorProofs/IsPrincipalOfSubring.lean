module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.UU
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KTrivDvrSpread

theorem symGen_of_local {V : Type} [CommRing V] [IsLocalRing V] {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (L : LB G.left) (hs : Out.Sym G L) (g : Sp V ⟶ S) :
    ∃ t : LB.Gen (LB.LinComb (L.pull (pullback.fst G.hom g)) (K := Fin 2)
      ![(ι[(Over.pullback g).obj G]).left, 𝟙 ((Over.pullback g).obj G).left] ![1, -1]), t.IsGen := by
  obtain ⟨U, hU, t, ht⟩ := hs (g (IsLocalRing.closedPoint V))
  have hU' : ⊤ ≤ g ⁻¹ᵁ U := (top_le_iff_cpt g U).2 hU
  have hr : Set.range (pullback.fst G.hom g) ⊆ Set.range (G.hom ⁻¹ᵁ U).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show G.hom (pullback.fst G.hom g y) ∈ U
    have e : G.hom (pullback.fst G.hom g y) = g (pullback.snd G.hom g y) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [e]
    exact hU' trivial
  have hψ : IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι =
      pullback.fst G.hom g := IsOpenImmersion.lift_fac _ _ _
  refine gen_chartPull (chartPullLinComb L (pullback.fst G.hom g) _ _ _
    (IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr) fun k => ?_) t ht
  fin_cases k
  · show (ι[(Over.pullback g).obj G]).left ≫ pullback.fst G.hom g =
      IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left
    rw [← Category.assoc, hψ]
    exact GlobalTheory.PolBaseChange.inv_comm (isGrpPullback_pullback G g)
  · show 𝟙 _ ≫ pullback.fst G.hom g = IsOpenImmersion.lift (G.hom ⁻¹ᵁ U).ι (pullback.fst G.hom g) hr ≫ (G.hom ⁻¹ᵁ U).ι
    rw [hψ, Category.id_comp]

theorem trivAlong_of_generic : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), IsAbelianScheme G → L.IsLB → Out.RelAmple G L → Out.Rigidified G L → Out.Sym G L → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (g : Sp V ⟶ S), GlobalTheory.KTrivSpread.TrivAlong G L (spMap (algebraMap V (FractionRing V)) ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S G _ _ L hG hL ha hR hS V _ _ _ g h
  have hl := GlobalTheory.abelianSchemeLaws_all.1
  have hp := isGrpPullback_pullback G g
  have hLB : (L.pull (pullback.fst G.hom g)).IsLB := pull_isLB hL _
  have hB : IsAbelianScheme ((Over.pullback g).obj G) := TLinPf.isAb_pullback g G hG
  have := hG.proper
  have haB : Out.RelAmple ((Over.pullback g).obj G) (L.pull (pullback.fst G.hom g)) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL ha (IsPullback.of_hasPullback G.hom g)
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V ((Over.pullback g).obj G) _ hLB).1 haB
  have hP : GlobalTheory.AbLaw.IsProjBy ((Over.pullback g).obj G).hom := ⟨_, GlobalTheory.AbLaw.isLB_pw hLB _, n, s, hs⟩
  obtain ⟨t, ht⟩ := GlobalTheory.AbLaw.CubeProj.exists_gen_theta_of_isProjBy hl.globalFns V _ hB hP _ hLB
  obtain ⟨r, hr⟩ := GlobalTheory.PolBaseChange.rigidified_pull hp hR
  obtain ⟨u, hu⟩ := symGen_of_local G L hS g
  obtain ⟨M, hM⟩ := GlobalTheory.AbPackage.exists_cp hl.globalFns hB ⟨L.pull (pullback.fst G.hom g), r, hLB, hr⟩
    ⟨t, ht⟩ ⟨u, hu⟩
  have hML : M.L.L = L.pull (pullback.fst G.hom g) := by rw [hM]
  let j := spMap (algebraMap V (FractionRing V))
  let B := (Over.pullback g).obj G
  have hq := isGrpPullback_pullback B j
  have hA : IsAbelianScheme ((Over.pullback j).obj B) := TLinPf.isAb_pullback j B hB
  have := hA.smooth
  have := hA.geomConnected
  have := hB.proper
  have : ConnectedSpace ((Over.pullback j).obj B).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback j).obj B).hom
  obtain ⟨dim, hdim⟩ := exists_dim_of_preconnected ((Over.pullback j).obj B).hom
    (eSec ((Over.pullback j).obj B) (IsLocalRing.closedPoint (FractionRing V)))
  have hLA := pull_isLB hLB (pullback.fst B.hom j)
  have hK : GlobalTheory.KTrivSpread.TrivAlong ((Over.pullback j).obj B)
      ((L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)) (𝟙 _) :=
    GlobalTheory.KTrivSpread.TrivAlong.pull hq hLB ((GlobalTheory.KTrivSpread.TrivAlong.pull hp hL h).comp (𝟙 _))
  let P : Out.PolAV (Sp (FractionRing V)) :=
    { A := (Over.pullback j).obj B
      isAb := hA
      g := dim
      smoothDim := hdim
      L := (L.pull (pullback.fst G.hom g)).pull (pullback.fst B.hom j)
      isLB := hLA
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hq ⟨r, hr⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hq (GlobalTheory.PolBaseChange.sym_pull hp hS)
      ample := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hLB haB (IsPullback.of_hasPullback B.hom j)
      ktriv := kTriv_iff_forall.2 fun T x hx => hK T T.hom (Category.comp_id _) x hx }
  have hw : LBIso P.L (M.L.L.pull (pullback.fst B.hom j)) := by
    rw [hML]
    exact GlobalTheory.PolBaseChange.lbIso_refl hLA
  have hK' : Out.KTriv B M.L.L :=
    GlobalTheory.KTrivSpread.kTriv_of_generic_fibre hl V (FractionRing V) P B M (pullback.fst B.hom j) hB hq hw
      (by rw [hML]; exact haB)
  rw [hML] at hK'
  exact GlobalTheory.KTrivSpread.trivAlong_of_kTriv hp hL hK'

end GlobalTheory.KTrivDvrSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kGroup_trivial_spreads_from_dvr_generic_point : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left), IsAbelianScheme G → L.IsLB → Out.RelAmple G L → Out.Rigidified G L → Out.Sym G L → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (g : Sp V ⟶ S), GlobalTheory.KTrivSpread.TrivAlong G L (spMap (algebraMap V (FractionRing V)) ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  first | exact @GlobalTheory.KTrivDvrSpread.trivAlong_of_generic | exact GlobalTheory.KTrivDvrSpread.trivAlong_of_generic | (intros; apply GlobalTheory.KTrivDvrSpread.trivAlong_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivFlatDescent

theorem trivAlong_of_flat_surjective : ∀ {S S' S'' : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (g : S' ⟶ S) (f : S'' ⟶ S') [Flat f] [Surjective f], L.IsLB → GlobalTheory.KTrivSpread.TrivAlong G L (f ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S S' S'' G _ L g f _ _ _ h T a ha x hx
  let u := pullback.fst a f
  have hu : Epi u := Flat.epi_of_flat_of_surjective _
  let T' : Over S := Over.mk (u ≫ T.hom)
  let U : T' ⟶ T := Over.homMk u rfl
  have hs : pullback.snd a f ≫ f ≫ g = T'.hom := by
    show pullback.snd a f ≫ f ≫ g = u ≫ T.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, ha]
  have e₁ : U ≫ x = 1 := h T' (pullback.snd a f) hs (U ≫ x) (hx.comp U)
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ G) := by rw [e₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi u).1 (congrArg (fun q => q.left) e₂))

end GlobalTheory.KTrivFlatDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kGroup_trivial_descends_flat_surjective : ∀ {S S' S'' : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (g : S' ⟶ S) (f : S'' ⟶ S') [Flat f] [Surjective f], L.IsLB → GlobalTheory.KTrivSpread.TrivAlong G L (f ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  first | exact @GlobalTheory.KTrivFlatDescent.trivAlong_of_flat_surjective | exact GlobalTheory.KTrivFlatDescent.trivAlong_of_flat_surjective | (intros; apply GlobalTheory.KTrivFlatDescent.trivAlong_of_flat_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral GlobalTheory.KTrivSpread

noncomputable section

namespace GlobalTheory.PrincSubring

section Calc

variable {S : Scheme.{0}} {A : Over S} {n : ℕ}
variable [GrpObj A] [IsCommMonObj A] {π : Pic (A ⊗ A).left}
  (hadd : ∀ (T : Over S) (x x' y : T ⟶ A), pair π (x * x') y = pair π x y + pair π x' y)
  (hsym : ∀ (T : Over S) (x y : T ⟶ A), pair π x y = pair π y x)
variable {G : Over S} [GrpObj G] {pr : Fin n → (G ⟶ A)} (hmon : ∀ u, IsMonHom (pr u))
  (huniv : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
  {W : Matrix (Fin n) (Fin n) ℤ} {L : LB G.left} (hL : L.IsLB) (hLW : cls L hL = quad π W pr)


include hadd hsym hLW hmon huniv in
theorem trivAlong_of_kernelAlong {S' : Scheme.{0}} (g : S' ⟶ S) (hdet : (W + W.transpose).det = 1)
    (hker : ∀ (T : Over S) (a : T.left ⟶ S'), a ≫ g = T.hom → ∀ x : T ⟶ A,
      pair π (snd A T ≫ x) (fst A T) = 0 → x = 1) : TrivAlong G L g := by
  intro T a ha x hx
  have hd : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨z, -, hz⟩ := huniv T fun _ => 1
  refine (hz x fun u₀ => ?_).trans (hz (1 : T ⟶ G) fun u => ?_).symm
  swap
  · have := hmon u
    exact MonObj.one_comp _
  choose V hV c hc using hx
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext
    (T.left.openCoverOfIsOpenCover V
      (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hV p⟩)) _ _ fun p => ?_)
  let T' : Over S := Over.mk ((V p).ι ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (V p).ι rfl
  have key : ∀ w : Fin n → ℤ, quad π W (fun u => (snd A T' ≫ j) ≫ x ≫ pr u) +
      ∑ u, ((W + W.transpose).mulVec w) u • pair π ((snd A T' ≫ j) ≫ x ≫ pr u) (fst A T') = 0 := fun w => by
    obtain ⟨b, hb, -⟩ := huniv (A ⊗ T') fun v => fst A T' ^ w v
    have h := pull_translDiff hadd hsym hmon hL hLW x (snd A T' ≫ j) b hd
    have k : (lift (snd A T' ≫ j) b).left ≫ (fst T G).left = (snd A T').left ≫ (V p).ι :=
      congrArg (fun q => q.left) (lift_fst (snd A T' ≫ j) b)
    obtain ⟨m, hm⟩ : ∃ m : (A ⊗ T').left ⟶ ((fst T G).left ⁻¹ᵁ V p).toScheme,
        m ≫ ((fst T G).left ⁻¹ᵁ V p).ι = (lift (snd A T' ≫ j) b).left :=
      ⟨IsOpenImmersion.lift _ (lift (snd A T' ≫ j) b).left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ V p) k).mpr ((snd A T').left y).2), IsOpenImmersion.lift_fac _ _ _⟩
    have h0 := (cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩
    rw [cls_pull hd] at h0
    rw [← hm, pull_comp, h0, map_zero] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hb, hsym _ _ (fst A T' ^ w v), pair_zpow hadd, hsym _ (fst A T'), mul_smul]
  have k₀ := key 0
  have k₁ := key ((W + W.transpose).adjugate.mulVec (Pi.single u₀ 1))
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec] at k₁
  simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at k₀
  rw [k₀, zero_add, Finset.sum_eq_single u₀ (fun v _ hv => by rw [Pi.single_eq_of_ne hv, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul, Category.assoc] at k₁
  have e : j ≫ x ≫ pr u₀ = j ≫ 1 :=
    (hker T' ((V p).ι ≫ a) (by simp [T', ha]) _ k₁).trans (MonObj.comp_one j).symm
  exact congrArg (fun q => q.left) e


include hadd hsym hLW hmon huniv in
theorem kernelAlong_of_trivAlong {S' : Scheme.{0}} (g : S' ⟶ S) (u₀ : Fin n) (hK : TrivAlong G L g)
    (T : Over S) (a : T.left ⟶ S') (ha : a ≫ g = T.hom) (x : T ⟶ A)
    (hx : pair π (snd A T ≫ x) (fst A T) = 0) : x = 1 := by
  obtain ⟨y, hy, -⟩ := huniv T fun u => if u = u₀ then x else 1
  have hz : ∀ (Z : Over S) (b : Z ⟶ T) (z : Z ⟶ A) u, pair π (b ≫ y ≫ pr u) z = 0 := fun Z b z u => by
    rw [hy]
    split_ifs
    · have h := congrArg (pull (lift z b).left) hx
      rwa [pull_pair, map_zero, lift_snd_assoc, lift_fst] at h
    · rw [MonObj.comp_one, pair_one hadd]
  have hd : (Out.translDiff G L y).IsLB := LB.isLB_linComb hL _ _
  have h1 : y = 1 := hK T a ha y fun p => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (pull_isLB hd _)).1 ?_
    have h := pull_translDiff hadd hsym hmon hL hLW y (fst T G) (snd T G) hd
    simp only [quad, hz, smul_zero, Finset.sum_const_zero, add_zero, lift_fst_snd, Over.id_left] at h
    rw [pull_id] at h
    rw [cls_pull hd]
    exact (congrArg _ h).trans (map_zero _)⟩
  have := hmon u₀
  have h := hy u₀
  rw [if_pos rfl, h1, MonObj.one_comp] at h
  exact h.symm

end Calc

theorem kerAlong_iff_trivAlong : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}}
    (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  intro S h A _ _ P hs hA S' g
  obtain ⟨hab, -, hP, hr₁, hr₂, hsw⟩ := hs
  have hadd : ∀ (T : Over S) (x x' y : T ⟶ A),
      pair (cls P hP) (x * x') y = pair (cls P hP) x y + pair (cls P hP) x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (Biadditive.biadditive_of_triv_axes globalFns_holds S A
      (diagPull A P) hab (pull_isLB hP _) hA P hP hr₁ hr₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    unfold PrincipalIntegral.pair
    abel
  have hsym : ∀ (T : Over S) (x y : T ⟶ A), pair (cls P hP) x y = pair (cls P hP) y x := fun T x y => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsw
    have k : (lift y x).left ≫ (lift (snd A A) (fst A A)).left = (lift x y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    unfold PrincipalIntegral.pair
    rw [← k, pull_comp, ← e]
  obtain ⟨-, hdet⟩ := isE8_W8
  have hmon : ∀ u : Fin 8, IsMonHom (Out.powPr A u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ Out.powPr A u = y u :=
    fun T y => ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP _ _
  have hLW : cls (powLB A P) hL = quad (cls P hP) GlobalTheory.W8 (Out.powPr A) := cls_linComb hP _ _ _
  have tr : ∀ (T : Over S) (x : T ⟶ A), pair (cls P hP) (snd A T ≫ x) (fst A T) = 0 ↔ IsTrivial (slice A P x) :=
    fun T x => by
      rw [PrincipalIntegral.pair, ← cls_pull hP _ (pull_isLB hP _)]
      exact (cls_eq_zero_iff _).trans (GlobalTheory.SiegelTypings.triv_swap hP x)
  constructor
  · intro hk
    exact trivAlong_of_kernelAlong hadd hsym hmon huniv hL hLW g hdet fun T a ha x hx => hk T a ha x ((tr T x).1 hx)
  · intro hK T a ha x hx
    exact kernelAlong_of_trivAlong hadd hsym hmon huniv hL hLW g 0 hK T a ha x ((tr T x).2 hx)

end GlobalTheory.PrincSubring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}} (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  first | exact @GlobalTheory.PrincSubring.kerAlong_iff_trivAlong | exact GlobalTheory.PrincSubring.kerAlong_iff_trivAlong | (intros; apply GlobalTheory.PrincSubring.kerAlong_iff_trivAlong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrincSubring

section Transport

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gm_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {Z : Scheme.{0}} (f : Z ⟶ X')
    (z : Z) {k : L'.ι} (hk : f z ∈ L'.U k) : gm f z (L'.U k ⊓ L'.U k) (L'.g k k) = 1 := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (f z))
  have e := hw Z f z j j k k hj hj hk hk
  rw [gm_self hL (f ≫ F) z hj, _root_.one_mul] at e
  exact inv_eq_one.1 (mul_eq_right.1 e.symm)

theorem trF_self_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {q : K → L'.ι} (hq : r z ∈ LB.wchart L' φ' q) :
    trF (L := L') φ' ε r z q q = 1 := by
  unfold trF
  refine Finset.prod_eq_one fun k _ => ?_
  rw [gm_self_of_pGen hw hL (r ≫ φ' k) z (Set.mem_iInter.1 hq k), one_zpow]

theorem exists_down_of_pGen {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self_of_pGen hw hL _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  choose p hp using fun k => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

end Transport

theorem kerAlong_of_pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  intro S S' f A _ P A₁ _ P₁ φ φ₂ hP₁ h hs hw hK T a ha x hx
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨c, hc⟩ := hx
  let T' : Over S' := Over.mk a
  have hxw : x.left ≫ A₁.hom = a ≫ f := (Over.w x).trans ha.symm
  let x' : T' ⟶ A := Over.homMk (h.1.lift x.left a hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = x.left := h.1.lift_fst _ _ _
  have key : x' = 1 := hK T' x' <| by
    let b : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ T := Over.homMk (fst T' A).left (by
      show (fst T' A).left ≫ T.hom = (T' ⊗ A).hom ≫ f
      rw [← ha, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w (fst T' A)))
    let c' : Over.mk ((T' ⊗ A).hom ≫ f) ⟶ A₁ := pushPt h.1.w (snd T' A)
    have k₁ : (lift b c').left ≫ (fst T A₁).left = (fst T' A).left := congrArg (fun q => q.left) (lift_fst b c')
    have k₂ : (lift b c').left ≫ (snd T A₁).left = (snd T' A).left ≫ φ := congrArg (fun q => q.left) (lift_snd b c')
    have k₃ : (fst T' A ≫ x').left ≫ φ = (lift b c').left ≫ (fst T A₁ ≫ x).left := by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hx', ← Category.assoc, k₁]
    have k₄ := GlobalTheory.SiegelDescent.lift_comp_square hs (T' := T' ⊗ A) (lift b c').left _ _ _ _ k₃ k₂.symm
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame P₁
      (fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left ≫ φ₂) _ _ (lift b c').left fun _ => k₄) c hc
    exact exists_down_of_pGen (φ' := fun _ : PUnit => (lift (fst T' A ≫ x') (snd T' A)).left) (ε := fun _ => 1)
      ((isGen_iff w).1 hwg) hP₁ c₂ h₂
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) (by
    show 𝟙 T.left ≫ T.hom = a ≫ f
    rw [Category.id_comp, ha])
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext (by
    show 𝟙 T.left ≫ x.left = x'.left ≫ φ
    rw [Category.id_comp, hx'])
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A₁) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  have e₃ : 𝟙 T.left ≫ x.left = 𝟙 T.left ≫ (1 : T ⟶ A₁).left := congrArg (fun q => q.left) e₂
  exact Over.OverMorphism.ext (by simpa only [Category.id_comp] using e₃)

end GlobalTheory.PrincSubring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_condition_along_baseChange_of_pullback : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  first | exact @GlobalTheory.PrincSubring.kerAlong_of_pull | exact GlobalTheory.PrincSubring.kerAlong_of_pull | (intros; apply GlobalTheory.PrincSubring.kerAlong_of_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section

namespace GlobalTheory.PrimeReach

theorem prime_contraction_or_dvr : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (p : PrimeSpectrum R₁), p ∈ Set.range (PrimeSpectrum.comap R₁.subtype) ∨ ∃ (Q : PrimeSpectrum R) (k : Type) (_ : Field k) (i : R₁ →+* k) (j : k →+* Q.asIdeal.ResidueField) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ρ : R₁ →+* V) (e : k →+* FractionRing V), j.comp i = (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype ∧ e.comp i = (algebraMap V (FractionRing V)).comp ρ ∧ p ∈ Set.range (PrimeSpectrum.comap ρ) := by
  intro R _ R₁ _ p
  by_cases hp : p ∈ Set.range (PrimeSpectrum.comap R₁.subtype)
  · exact Or.inl hp
  right
  haveI := p.isPrime
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R₁)) (J := p.asIdeal) bot_le
  obtain ⟨P, hP, hPq⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := R₁.subtype) Subtype.val_injective q hq
  let Q : PrimeSpectrum R := ⟨P, hP⟩
  haveI hqpr : q.IsPrime := hq.1.1
  let f₀ : R₁ →+* Q.asIdeal.ResidueField := (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype
  have hker : RingHom.ker f₀ = q := by
    rw [← hPq]
    ext x
    simp only [f₀, RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    exact (Ideal.algebraMap_residueField_eq_zero).trans Iff.rfl
  let A := R₁ ⧸ q
  let g₀ : A →+* Q.asIdeal.ResidueField := Ideal.Quotient.lift q f₀ (fun a ha => by rw [← RingHom.mem_ker, hker]; exact ha)
  have hg₀ : Function.Injective g₀ := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.lift_mk, ← RingHom.mem_ker, hker] at hx
    exact (Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 hx)
  let k := FractionRing A
  let i : R₁ →+* k := (algebraMap A k).comp (Ideal.Quotient.mk q)
  let j : k →+* Q.asIdeal.ResidueField := IsFractionRing.lift hg₀
  have hji : j.comp i = f₀ := by
    ext x
    simp only [i, j, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    rfl
  let p' : Ideal A := p.asIdeal.map (Ideal.Quotient.mk q)
  haveI hp' : p'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hqp)
  have hcp' : p'.comap (Ideal.Quotient.mk q) = p.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.2 hqp
  let O := Localization.AtPrime p'
  haveI : IsDomain O := IsLocalization.isDomain_localization p'.primeCompl_le_nonZeroDivisors
  have hOinj : Function.Injective (algebraMap A O) := IsLocalization.injective O p'.primeCompl_le_nonZeroDivisors
  have hcm : (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p' := Localization.AtPrime.under_maximalIdeal
  have hnf : ¬ IsField O := by
    intro hF
    apply hp
    have hm : IsLocalRing.maximalIdeal O = ⊥ := by
      letI := hF.toField
      exact IsLocalRing.maximalIdeal_eq_bot
    have h1 : p' = ⊥ := by
      rw [← hcm, hm, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).1 hOinj]
    refine ⟨Q, PrimeSpectrum.ext ?_⟩
    show P.comap R₁.subtype = p.asIdeal
    rw [hPq, ← hcp', h1, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  obtain ⟨V, _, _, _, ρ₀, hρinj, hρloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hnf
  let ρ : R₁ →+* V := ρ₀.comp ((algebraMap A O).comp (Ideal.Quotient.mk q))
  let g' : A →+* FractionRing V := (algebraMap V (FractionRing V)).comp (ρ₀.comp (algebraMap A O))
  have hg' : Function.Injective g' := (IsFractionRing.injective V (FractionRing V)).comp (hρinj.comp hOinj)
  let e : k →+* FractionRing V := IsFractionRing.lift hg'
  refine ⟨Q, k, inferInstance, i, j, V, inferInstance, inferInstance, inferInstance, ρ, e, hji, ?_, ?_⟩
  · ext x
    simp only [e, i, ρ, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
    rfl
  · have hmV : (IsLocalRing.maximalIdeal V).comap ρ₀ = IsLocalRing.maximalIdeal O := by
      refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal V).ne_top)) ?_
      intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal x).1 hx (isUnit_of_map_unit ρ₀ x hu)
    refine ⟨⟨IsLocalRing.maximalIdeal V, inferInstance⟩, PrimeSpectrum.ext ?_⟩
    show (IsLocalRing.maximalIdeal V).comap ρ = p.asIdeal
    rw [show ρ = (ρ₀.comp (algebraMap A O)).comp (Ideal.Quotient.mk q) from rfl, ← Ideal.comap_comap,
      ← Ideal.comap_comap, hmV, hcm, hcp']

end GlobalTheory.PrimeReach
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noetherian_subring_prime_contraction_or_dvr : ∀ (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (p : PrimeSpectrum R₁), p ∈ Set.range (PrimeSpectrum.comap R₁.subtype) ∨ ∃ (Q : PrimeSpectrum R) (k : Type) (_ : Field k) (i : R₁ →+* k) (j : k →+* Q.asIdeal.ResidueField) (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ρ : R₁ →+* V) (e : k →+* FractionRing V), j.comp i = (algebraMap R Q.asIdeal.ResidueField).comp R₁.subtype ∧ e.comp i = (algebraMap V (FractionRing V)).comp ρ ∧ p ∈ Set.range (PrimeSpectrum.comap ρ) := by
  first | exact @GlobalTheory.PrimeReach.prime_contraction_or_dvr | exact GlobalTheory.PrimeReach.prime_contraction_or_dvr | (intros; apply GlobalTheory.PrimeReach.prime_contraction_or_dvr <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.PrincSubring

theorem isPrincipal_of_subring : ∀ (h : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsSymmetricPair h A₁ P₁ → Out.RelAmple A₁ (diagPull A₁ P₁) → IsGrpPullback A A₁ (spMap R₁.subtype) φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsPrincipal A P → IsPrincipal A₁ P₁ := by
  intro h R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hS hamp hpb hsq hiso hpr
  haveI : IsAbelianScheme A₁ := hS.1
  haveI : IsCommMonObj A₁ := IsAbelianScheme.comm
  obtain ⟨hG, hL, hLa, hrig, hsym⟩ := GlobalTheory.T.eighth_power_symmetric_ample h A₁ P₁ hS hamp
  have hf : KerAlong A₁ P₁ (spMap R₁.subtype) := GlobalTheory.T.kernel_condition_along_baseChange_of_pullback _ A P A₁ P₁ φ φ₂ hS.2.2.1 hpb hsq hiso hpr.2
  have hfT := (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp _).1 hf
  have hK : Out.KTriv (Out.powObj A₁ 8) (powLB A₁ P₁) := by
    refine GlobalTheory.KTrivSpread.kTriv_of_primes GlobalTheory.abelianSchemeLaws_all.1.globalFns R₁ _ hG _ hL hLa fun p => ?_
    rcases GlobalTheory.T.noetherian_subring_prime_contraction_or_dvr R R₁ p with hp | ⟨Q, k, _, i, j, V, _, _, _, ρ, e, h1, h2, hp⟩
    · exact ⟨R, inferInstance, R₁.subtype, hp, hfT⟩
    · refine ⟨V, inferInstance, ρ, hp, ?_⟩
      refine GlobalTheory.T.kGroup_trivial_spreads_from_dvr_generic_point _ _ hG hL hLa hrig hsym V (spMap ρ) ?_
      have t1 := hfT.comp (spMap (algebraMap R Q.asIdeal.ResidueField))
      have e1 : spMap (algebraMap R Q.asIdeal.ResidueField) ≫ spMap R₁.subtype = spMap j ≫ spMap i := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h1]
      rw [e1] at t1
      have t2 := (GlobalTheory.T.kGroup_trivial_descends_flat_surjective _ _ (spMap i) (spMap j) hL t1).comp (spMap e)
      have e2 : spMap e ≫ spMap i = spMap (algebraMap V (FractionRing V)) ≫ spMap ρ := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h2]
      rwa [e2] at t2
  have hT : GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A₁ 8) (powLB A₁ P₁) (𝟙 _) :=
    fun T a ha x hx => GlobalTheory.UU.kTriv_iff_forall.1 hK T x hx
  exact ⟨hamp, fun T x hx => (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp (𝟙 _)).2 hT T T.hom (Category.comp_id _) x hx⟩

end GlobalTheory.PrincSubring
