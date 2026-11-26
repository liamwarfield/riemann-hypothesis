module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusPointMemRangeSiegelModuliOpenImmersi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyPointOfPrincipalObject
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyPointOfPrincipalObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem dense_asIdeal_eq_bot_spMap (n : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) : Dense {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
  let p₀ : Sp V₁ := ⟨⊥, Ideal.isPrime_bot⟩
  let K := FractionRing V₁
  have hinj : Function.Injective (algebraMap V₁ K) := IsFractionRing.injective V₁ K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hmem : p₀ ∈ {x : Sp V₁ | (spMap b₁ x).asIdeal = ⊥} := by
    let q : Sp K := ⟨⊥, Ideal.isPrime_bot⟩
    have h := GlobalTheory.AbChart.asIdeal_eq_bot_of_charZero n K (spMap ((algebraMap V₁ K).comp b₁)) q
    show Ideal.comap b₁ (⊥ : Ideal V₁) = ⊥
    have hc : Ideal.comap (algebraMap V₁ K) (⊥ : Ideal K) = ⊥ :=
      (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => hinj (by rw [ha, map_zero])
    rw [← hc, Ideal.comap_comap]
    exact h
  have hcl : closure ({p₀} : Set (Sp V₁)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    exact (PrimeSpectrum.le_iff_mem_closure (R := V₁) p₀ x).1 bot_le
  refine Dense.mono (Set.singleton_subset_iff.2 hmem) ?_
  exact dense_iff_closure_eq.2 hcl

theorem exists_sFam_point : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁]
    (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal →
    ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  intro n hn hodd h V₁ _ _ _ b₁ s hs
  obtain ⟨F⟩ : Nonempty (SFam h n (zetaAway n)) := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exact ⟨zeroFam n hn⟩
    · exact GlobalTheory.SiegelTor.exists_sFam_cycAway h n hh hn hodd
  obtain ⟨x, hx, hpb⟩ := F.rep (Sp V₁) (spMap b₁) s inferInstance (dense_asIdeal_eq_bot_spMap n V₁ b₁) hs
  exact ⟨F, x, hx, hpb⟩

end GlobalTheory.LowChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelFamilyPointOfPrincipalObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_family_point_of_principal_object : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [CharZero V₁] (b₁ : cycAway n →+* V₁) (s : SiegPre h n (zetaAway n) (spMap b₁)), s.Principal → ∃ (F : SFam h n (zetaAway n)) (x : Sp V₁ ⟶ F.X), x ≫ F.s = spMap b₁ ∧ SiegPB s F.univ x := by
  first | exact @GlobalTheory.LowChart.exists_sFam_point | exact GlobalTheory.LowChart.exists_sFam_point | (intros; apply GlobalTheory.LowChart.exists_sFam_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DVRExt

theorem exists_unique_extend : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  intro R _ P W L _ _ _ _ _ _ f x
  haveI : ValuationRing W := inferInstance
  have hv : ValuativeCriterion P.A.hom := by
    have h : IsProper P.A.hom := P.isAb.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x.left ≫ P.A.hom = spMap (algebraMap W L) ≫ spMap f := by
    rw [Over.w x]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let S : ValuativeCommSq P.A.hom :=
    { R := W, K := L, i₁ := x.left, i₂ := spMap f, commSq := ⟨hsq⟩ }
  have hU := (hv S).some
  refine ⟨Over.homMk hU.default.l hU.default.fac_right, hU.default.fac_left, ?_⟩
  intro y hy
  have hy2 : y.left ≫ P.A.hom = spMap f := Over.w y
  let T : S.commSq.LiftStruct := ⟨y.left, hy, hy2⟩
  have hT : T = hU.default := hU.uniq T
  apply Over.OverMorphism.ext
  change T.l = hU.default.l
  rw [hT]

end GlobalTheory.DVRExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  first | exact @GlobalTheory.DVRExt.exists_unique_extend | exact GlobalTheory.DVRExt.exists_unique_extend | (intros; apply GlobalTheory.DVRExt.exists_unique_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilDomain

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (a : A) :
    (spMap g).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (g a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

theorem weilIs_of_fractionField : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  intro R _ _ P W L _ _ _ _ _ f e he n x y hx hy w H
  have hL := (GlobalTheory.firstFiveLaws).1
  obtain ⟨c, hc, -⟩ := (hL.weil _ P n (Over.mk (spMap f))).1 x y hx hy
  have H' := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB e hc
  have hu := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H' H
  have hinj : Function.Injective e.left.appTop.hom := by
    rw [he]
    intro a b hab
    have ia := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) a
    have ib := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) b
    rw [← ia, ← ib, appTop_spMap_inv, appTop_spMap_inv] at hab
    have h1 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).1 hab
    have h2 := IsFractionRing.injective W L h1
    rw [← ia, ← ib, h2]
  have hc' : c = unitOn w := by
    apply Units.ext
    apply hinj
    have := congrArg Units.val hu
    refine this.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (algebraMap W L w) = _
    rw [he]
    exact (appTop_spMap_inv (algebraMap W L) (w : W)).symm
  exact hc' ▸ hc

end GlobalTheory.WeilDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_eq_of_fractionField_domain : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  first | exact @GlobalTheory.WeilDomain.weilIs_of_fractionField | exact GlobalTheory.WeilDomain.weilIs_of_fractionField | (intros; apply GlobalTheory.WeilDomain.weilIs_of_fractionField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegelLevelPull

theorem exists_siegPre_of_points : ∀ (n : ℕ) (hn : 3 ≤ n) (V V₁ : Type) [CommRing V] [CommRing V₁] [IsLocalRing V₁] [IsNoetherianRing V₁] (f₁ : V →+* V₁) (b : cycAway n →+* V) (PB : PolAV (Sp V)) (lev : (Fin PB.g ⊕ Fin PB.g → ℤ) → (Over.mk (spMap f₁) ⟶ PB.A)) (r : ℕ) (d₀ : Fin r → (Over.mk (spMap f₁) ⟶ PB.A)) (c : Fin r → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ n = 1) → (∀ x y, Out.WeilIs PB.A PB.L n (lev x) (lev y) (unitOn (Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit ^ omegaStd x y))) → (∀ i, d₀ i ^ n = toUnit _ ≫ c i) → ∃ (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c i).left := by
  set_option backward.isDefEq.respectTransparency false in
    intro n hn V V₁ _ _ _ _ f₁ b PB lev r d₀ c hadd htors hweil hd
    have hn0 : n ≠ 0 := by omega
    haveI := PB.isAb.comm
    let P₁ : PolAV (Sp V₁) := GlobalTheory.StrictPull.polPull PB (spMap f₁)
    haveI : IsCommMonObj P₁.A := P₁.isAb.comm
    have hpb : IsGrpPullback P₁.A PB.A (spMap f₁) (pullback.fst PB.A.hom (spMap f₁)) :=
      isGrpPullback_pullback PB.A (spMap f₁)
    obtain ⟨κ, hκ⟩ := GlobalTheory.UnifPoint.exists_pointEquiv hpb
    have hk : ∀ x, (κ.symm x).left ≫ pullback.fst PB.A.hom (spMap f₁) = x.left := fun x => by
      rw [← hκ, κ.apply_symm_apply]
    let ze : V₁ˣ := Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit
    let lev₁ : (Fin PB.g ⊕ Fin PB.g → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ P₁.A) := fun x => κ.symm (lev x)
    have hL₁ : LBIso P₁.L (PB.L.pull (pullback.fst PB.A.hom (spMap f₁))) :=
      GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB PB.isLB _)
    have hw : ∀ x y, WeilIs P₁.A P₁.L n (lev₁ x) (lev₁ y) (unitOn (ze ^ omegaStd x y)) := fun x y =>
      (GlobalTheory.weilIs_grpPullback_of_comm _ _ PB.A P₁.A (spMap f₁) _ PB.L P₁.L PB.isLB P₁.isLB hpb hL₁ _ n _ _
        (pushPt hpb.1.w (lev₁ x)) (pushPt hpb.1.w (lev₁ y)) _ rfl rfl).2
        (GlobalTheory.UnifPoint.weilIs_congr (Category.id_comp _).symm (hk _).symm (hk _).symm (hweil x y))
    have hadd₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y => by
      simp only [lev₁, hadd, map_mul]
    have htors₁ : ∀ x, lev₁ x ^ n = 1 := fun x => by
      simp only [lev₁, ← map_pow, htors, map_one]
    have hu : IsUnit (n : V₁) := by simpa using (GlobalTheory.SiegelTor.isUnit_natCast hn0).map (f₁.comp b)
    have hze : (ze : V₁) = (f₁.comp b) (zetaAway n) := by simp [ze]
    have hprim : ∀ (k : Type) [Field k] (gk : V₁ →+* k), IsPrimitiveRoot (gk ze) n := fun k _ gk => by
      rw [hze]; exact GlobalTheory.SiegelTor.isPrimitiveRoot_map hn0 (gk.comp (f₁.comp b))
    haveI : IsMonHom (Iso.refl P₁.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    have hid : IsGrpPullback P₁.A P₁.A (spMap (RingHom.id V₁)) (𝟙 _) :=
      (isGrpPullback_of_iso (Iso.refl P₁.A)).congr (by simp [spMap]) rfl
    obtain ⟨s, ψ, hψ, hs, hsP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre V₁ V₁ P₁ (RingHom.id V₁) P₁ (𝟙 _) hid
      (GlobalTheory.lbIso_pull_id P₁.isLB).symm rfl (cycAway n) (f₁.comp b) PB.g n (zetaAway n) ze lev₁ rfl hu hze hprim
      hadd₁ htors₁ hw

    haveI := hψ
    have hLamB : (abelian₂ PB.A PB.L).IsLB := DVR.linComb_isLB _ PB.isLB _ _
    have hLam₁ : (abelian₂ P₁.A P₁.L).IsLB := DVR.linComb_isLB _ P₁.isLB _ _
    obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap f₁) PB.A P₁.A _ hpb
    have e₁ : LBIso (abelian₂ P₁.A P₁.L) ((abelian₂ PB.A PB.L).pull (β₂ ≫ 𝟙 _)) :=
      hlam PB.L P₁.L _ (abelian₂ PB.A PB.L) (𝟙 _) PB.isLB P₁.isLB hLamB hL₁ (GlobalTheory.lbIso_pull_id hLamB).symm
    rw [Category.comp_id] at e₁
    let κ₂ := (lift (fst s.A s.A ≫ ψ.hom) (snd s.A s.A ≫ ψ.hom)).left
    have e₂ : LBIso ((abelian₂ P₁.A P₁.L).pull κ₂) ((abelian₂ PB.A PB.L).pull (κ₂ ≫ β₂)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl) (chartPullSame (abelian₂ PB.A PB.L) _ (fun _ => β₂) _ κ₂ fun _ => rfl) e₁
    let d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A) := fun i => κ.symm (d₀ i) ≫ ψ.inv
    have hpow : ∀ (x : 𝟙_ (Over (Sp V₁)) ⟶ P₁.A) (m : ℕ), ((x ≫ ψ.inv) ^ m) ≫ ψ.hom = x ^ m := fun x m => by
      induction m with
      | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
      | succ m ih => rw [pow_succ, MonObj.mul_comp, ih, Category.assoc, Iso.inv_hom_id, Category.comp_id, pow_succ]
    refine ⟨s, ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁), κ₂ ≫ β₂, d, hs,
      ((isGrpPullback_of_iso ψ).comp hpb).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩,
      LBIso.trans s.isLB (pull_isLB hLam₁ _) (pull_isLB hLamB _) hsP e₂, fun i => ?_⟩
    · rw [Category.assoc, hsq.1]
      have e : κ₂ ≫ (fst P₁.A P₁.A).left = (fst s.A s.A).left ≫ ψ.hom.left := by
        simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_fst]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
    · rw [Category.assoc, hsq.2]
      have e : κ₂ ≫ (snd P₁.A P₁.A).left = (snd s.A s.A).left ≫ ψ.hom.left := by
        simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_snd]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
    · have h1 : (d i ^ n).left ≫ ψ.hom.left = (κ.symm (d₀ i) ^ n).left := by
        rw [← Over.comp_left, hpow]
      have hT : (toUnit (Over.mk (spMap f₁))).left = spMap f₁ := by
        simpa using Over.w (toUnit (Over.mk (spMap f₁)))
      calc (d i ^ n).left ≫ ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁)
          = ((d i ^ n).left ≫ ψ.hom.left) ≫ pullback.fst PB.A.hom (spMap f₁) := (Category.assoc _ _ _).symm
        _ = (κ.symm (d₀ i) ^ n).left ≫ pullback.fst PB.A.hom (spMap f₁) := by rw [h1]
        _ = (d₀ i ^ n).left := by rw [← map_pow, hk]
        _ = spMap f₁ ≫ (c i).left := by rw [hd, Over.comp_left, hT]

end GlobalTheory.SiegelLevelPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_of_symplecticLevel_points : ∀ (n : ℕ) (hn : 3 ≤ n) (V V₁ : Type) [CommRing V] [CommRing V₁] [IsLocalRing V₁] [IsNoetherianRing V₁] (f₁ : V →+* V₁) (b : cycAway n →+* V) (PB : PolAV (Sp V)) (lev : (Fin PB.g ⊕ Fin PB.g → ℤ) → (Over.mk (spMap f₁) ⟶ PB.A)) (r : ℕ) (d₀ : Fin r → (Over.mk (spMap f₁) ⟶ PB.A)) (c : Fin r → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ n = 1) → (∀ x y, Out.WeilIs PB.A PB.L n (lev x) (lev y) (unitOn (Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit ^ omegaStd x y))) → (∀ i, d₀ i ^ n = toUnit _ ≫ c i) → ∃ (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c i).left := by
  first | exact @GlobalTheory.SiegelLevelPull.exists_siegPre_of_points | exact GlobalTheory.SiegelLevelPull.exists_siegPre_of_points | (intros; apply GlobalTheory.SiegelLevelPull.exists_siegPre_of_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldLevel

open GlobalTheory.TorsionGenerators

theorem pairing_prod {H U : Type} [CommGroup H] [CommGroup U] (e : H →* H →* U) (z : U) {g : ℕ}
    (x : Fin g ⊕ Fin g → H) (h₁ : ∀ i j, e (x (.inl i)) (x (.inl j)) = 1)
    (h₂ : ∀ i j, e (x (.inr i)) (x (.inr j)) = 1)
    (h₃ : ∀ i j, e (x (.inl i)) (x (.inr j)) = if i = j then z else 1)
    (h₄ : ∀ i j, e (x (.inr i)) (x (.inl j)) = if i = j then z⁻¹ else 1) (a b : Fin g ⊕ Fin g → ℤ) :
    e (∏ i, x i ^ a i) (∏ i, x i ^ b i) = z ^ omegaStd a b := by
  have hz : z ^ omegaStd a b = ∏ i, z ^ (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)) :=
    (map_prod (zpowersHom U z) (fun i => Multiplicative.ofAdd
      (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))) Finset.univ)
  have hi : ∀ (p : Prop) [Decidable p] (u : U) (m : ℤ), (if p then u else 1) ^ m = if p then u ^ m else 1 :=
    fun p _ u m => by split_ifs <;> simp
  have hp : ∀ (f : Fin g → H →* U) (t : H), (∏ i, f i) t = ∏ i, f i t :=
    fun f t => map_prod (MonoidHom.eval t) f Finset.univ
  rw [hz]
  simp only [map_prod, map_zpow, hp, MonoidHom.zpow_apply, Fintype.prod_sum_type,
    map_mul, MonoidHom.mul_apply, h₁, h₂, h₃, h₄, one_zpow, Finset.prod_const_one, _root_.one_mul, _root_.mul_one,
    hi, Finset.prod_ite_eq, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← zpow_mul, inv_zpow', ← zpow_add, zpow_sub, ← zpow_neg]
  congr 1
  ring

theorem stdSymp_mk {g p q : ℕ} (hp : p < 2 * g) (hq : q < 2 * g) : stdSymp g ⟨p, hp⟩ ⟨q, hq⟩ =
    if p < g ∧ q = p + g then 1 else if q < g ∧ p = q + g then -1 else 0 := rfl

theorem exists_points (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) [IsCommMonObj P.A] {g : ℕ}
    (hg : g = P.g) (M : ℕ) (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) :
    ∃ x : Fin g ⊕ Fin g → (baseOver (Sp K) ⟶ P.A), (∀ i, x i ^ M = 1) ∧
      ∀ a b : Fin g ⊕ Fin g → ℤ, Out.WeilIs P.A P.L M (∏ i, x i ^ a i) (∏ i, x i ^ b i) (ze ^ omegaStd a b) := by
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL K P hg M hM ze hz
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P M (baseOver (Sp K))
  let H : Subgroup (baseOver (Sp K) ⟶ P.A) := (powMonoidHom M).ker
  have hH : ∀ x : H, x.1 ^ M = 1 := fun x => x.2
  choose c hc hu using fun x y : H => w₁ x.1 y.1 (hH x) (hH y)
  have l : ∀ x x' y, c (x * x') y = c x y * c x' y := fun x x' y => (hu _ _ _ (w₂ _ _ _ _ _ (hc x y) (hc x' y))).symm
  have s : ∀ x y, c y x = (c x y)⁻¹ := fun x y => (hu _ _ _ (CommPairing.weilIs_symm P.isLB (hc x y))).symm
  let e : H →* H →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (c x) fun y y' => by
    rw [s (y * y'), l, mul_inv, ← s, ← s]) fun x x' => MonoidHom.ext fun y => l x x' y
  let κ : Fin g ⊕ Fin g → Fin (2 * g) := Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + g, by omega⟩)
  let y : Fin g ⊕ Fin g → H := fun i => ⟨x (κ i), hx _⟩
  have he : ∀ i j, e (y i) (y j) = ze ^ stdSymp g (κ i) (κ j) := fun i j => (hu (y i) (y j) _ (hw _ _)).symm
  refine ⟨fun i => (y i).1, fun i => hH _, fun a b => ?_⟩
  have E := pairing_prod e ze y (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) a b
  · have h := hc (∏ i, y i ^ a i) (∏ i, y i ^ b i)
    rw [show c (∏ i, y i ^ a i) (∏ i, y i ^ b i) = _ from E] at h
    change Out.WeilIs P.A P.L M (H.subtype (∏ i, y i ^ a i))
      (H.subtype (∏ i, y i ^ b i)) (ze ^ omegaStd a b) at h
    simpa only [map_prod, map_zpow, Subgroup.subtype_apply] using h
  all_goals
    have hi := i.2
    have hj := j.2
    rw [he]
    simp only [κ, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff]
    rw [stdSymp_mk]
    split_ifs <;> first | omega | (simp; done)

theorem exists_level_and_roots : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (K : Type) [Field K] [CharZero K] (j : R →+* K) (n : ℕ), 0 < n → ∀ (ζ : Kˣ), IsPrimitiveRoot ζ n → ∀ (r : ℕ) (c : Fin r → (𝟙_ (Over (Sp R)) ⟶ P.A)), ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (lev : (Fin P.g ⊕ Fin P.g → ℤ) → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)) (d : Fin r → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)), (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ n = 1) ∧ (∀ x y, Out.WeilIs P.A P.L n (lev x) (lev y) (unitOn (Units.map (algebraMap K L).toMonoidHom ζ ^ omegaStd x y))) ∧ ∀ i, d i ^ n = toUnit _ ≫ c i := by
  intro R _ P K _ _ j n hn ζ hζ r c
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have := P.isAb.smooth
  let Q := AlgebraicClosure K
  let t : R →+* Q := (algebraMap K Q).comp j
  have hnQ : (n : Q) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hz : IsPrimitiveRoot (Units.map (algebraMap K Q).toMonoidHom ζ) n :=
    hζ.map_of_injective (unitsMap_injective _)
  obtain ⟨P', φ', β, h, -, H⟩ := exists_fibre hL P t
  have := P'.isAb.comm
  obtain ⟨x, hx, hw⟩ := exists_points hL Q P' h.1.symm n hnQ _ (ZH.RealDimOne.isPrimitiveRoot_unitOn hz)
  have hroot : ∀ p : Over.mk (spMap t) ⟶ P.A, ∃ q, q ^ n = p := fun p => by
    obtain ⟨p, rfl⟩ := β.surjective p
    obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_div hL.mulN P' p n hn
    exact ⟨β q, (map_pow β _ _).symm.trans (congrArg β hq)⟩
  choose d hd using fun i => hroot (toUnit _ ≫ c i)
  let z : (Fin P.g ⊕ Fin P.g) ⊕ Fin r → (Over.mk (spMap t) ⟶ P.A) := Sum.elim (fun i => β (x i)) d
  choose s hs hb using fun i => exists_finite_coordinates P.A.hom t (z i).left (Over.w _)
  let s' : Set Q := ⋃ i, s i
  have : Finite s' := (Set.finite_iUnion hs).to_subtype
  let L := IntermediateField.adjoin K s'
  have : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let io : L →+* Q := algebraMap L Q
  let j' : R →+* L := (algebraMap K L).comp j
  have hj : io.comp j' = t := rfl
  choose b hb' using fun i => hb i L io io.injective (fun c => ⟨j' c, rfl⟩) (fun y hy =>
    ⟨⟨y, IntermediateField.subset_adjoin K s' (Set.mem_iUnion.2 ⟨i, hy⟩)⟩, rfl⟩)
  have hbw : ∀ i, b i ≫ P.A.hom = spMap j' := fun i => by
    have := TorsionSeparable.epi_specMap io
    rw [← cancel_epi (spMap io), ← Category.assoc, hb', spMap_comp_spMap]
    exact Over.w (z i)
  let y : _ → (Over.mk (spMap j') ⟶ P.A) := fun i => Over.homMk (b i) (hbw i)
  have hy : ∀ i, extPt hj ≫ y i = z i := fun i => Over.OverMorphism.ext (hb' i)
  let F : (Over.mk (spMap j') ⟶ P.A) →* (Over.mk (spMap t) ⟶ P.A) :=
    MonoidHom.mk' (fun p => extPt hj ≫ p) fun p q => comp_mul _ _ _
  have hF : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, extPt hj ≫ (∏ i, y (.inl i) ^ a i) = β (∏ i, x i ^ a i) := fun a => by
    show F _ = _
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_zpow]
    exact congrArg (· ^ a i) (hy (.inl i))
  have hyM : ∀ i, y (.inl i) ^ n = 1 := fun i => by
    rw [← extPt_eq_one_iff hj, comp_pow, hy]
    exact (map_pow β _ _).symm.trans ((congrArg β (hx i)).trans (map_one β))
  have hT : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, (∏ i, y (.inl i) ^ a i) ^ n = 1 := fun a => by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, hyM, one_zpow]
  refine ⟨L, inferInstance, inferInstance, this, fun a => ∏ i, y (.inl i) ^ a i, fun i => y (.inr i),
    fun a a' => ?_, hT, fun a a' => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · obtain ⟨u, hu⟩ := exists_weilIs hL P j' (hT a) (hT a')
    have H₁ := weilIs_extPt hL P hj hu
    rw [hF, hF] at H₁
    have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H₁ (H _ _ _ _ (hw a a'))
    have hζ' : Units.map (algebraMap K Q).toMonoidHom ζ =
      Units.map io.toMonoidHom (Units.map (algebraMap K L).toMonoidHom ζ) := Units.ext rfl
    rw [← ZH.RealDimOne.unitOn_zpow, hζ', ← map_zpow] at e
    rwa [← unitsMap_injective io (unitOn_injective e)]
  · apply extPt_injective hj
    rw [comp_pow, hy, ← Category.assoc, comp_toUnit]
    exact hd i

end GlobalTheory.FieldLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_roots_finite_ext_charZero : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (K : Type) [Field K] [CharZero K] (j : R →+* K) (n : ℕ), 0 < n → ∀ (ζ : Kˣ), IsPrimitiveRoot ζ n → ∀ (r : ℕ) (c : Fin r → (𝟙_ (Over (Sp R)) ⟶ P.A)), ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (lev : (Fin P.g ⊕ Fin P.g → ℤ) → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)) (d : Fin r → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)), (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ n = 1) ∧ (∀ x y, Out.WeilIs P.A P.L n (lev x) (lev y) (unitOn (Units.map (algebraMap K L).toMonoidHom ζ ^ omegaStd x y))) ∧ ∀ i, d i ^ n = toUnit _ ≫ c i := by
  first | exact @GlobalTheory.FieldLevel.exists_level_and_roots | exact GlobalTheory.FieldLevel.exists_level_and_roots | (intros; apply GlobalTheory.FieldLevel.exists_level_and_roots <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelAfterExt

theorem exists_siegPre_divPoints : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c (Pi.single i 1)).left := by
  intro n hn3 _ V _ _ _ hV _ b PB r c
  have hn0 : n ≠ 0 := by omega
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  let ze : (cycAway n)ˣ := (GlobalTheory.LowChart.isUnit_zetaAway n hn3).unit
  let ζ : (FractionRing V)ˣ := Units.map ((algebraMap V (FractionRing V)).comp b).toMonoidHom ze
  have hζ : IsPrimitiveRoot ζ n :=
    IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hn0 ((algebraMap V (FractionRing V)).comp b))
  obtain ⟨L, _, _, _, lev, d, hadd, htor, hweil, hd⟩ :=
    GlobalTheory.T.exists_symplecticLevel_roots_finite_ext_charZero V PB (FractionRing V) (algebraMap V (FractionRing V)) n (by omega) ζ hζ r (fun i => c (Pi.single i 1))
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  generalize hT : (algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V)) = T at lev d hadd htor hweil hd
  have hT' : (algebraMap W L).comp (algebraMap V W) = T := hcomp.trans hT
  subst hT'
  let f₁ : V →+* W := algebraMap V W
  let e : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ Over.mk (spMap f₁) :=
    Over.homMk (spMap (algebraMap W L)) (by show Spec.map _ ≫ Spec.map _ = Spec.map _; rw [← Spec.map_comp]; rfl)
  have hel : e.left = spMap (algebraMap W L) := rfl
  have uniq : ∀ y y' : Over.mk (spMap f₁) ⟶ PB.A, e ≫ y = e ≫ y' → y = y' := fun y y' h =>
    (GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ (e ≫ y)).unique (rfl : spMap (algebraMap W L) ≫ y.left = (e ≫ y).left)
      (show spMap (algebraMap W L) ≫ y'.left = (e ≫ y).left by rw [h]; rfl)
  have lift : ∀ x : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ PB.A, ∃ y, e ≫ y = x := fun x => by
    obtain ⟨y, hy, -⟩ := GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ x
    exact ⟨y, Over.OverMorphism.ext hy⟩
  choose lev₁ hlev₁ using fun a => lift (lev a)
  choose d₁ hd₁ using fun i => lift (d i)
  have add₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y =>
    uniq _ _ (by rw [MonObj.comp_mul, hlev₁, hlev₁, hlev₁, hadd])
  have tor₁ : ∀ x, lev₁ x ^ n = 1 := fun x =>
    uniq _ _ (by rw [MonObj.comp_pow, hlev₁, htor, MonObj.comp_one])
  have div₁ : ∀ i, d₁ i ^ n = toUnit _ ≫ c (Pi.single i 1) := fun i =>
    uniq _ _ (by rw [MonObj.comp_pow, hd₁, hd, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (toUnit _)])
  have weil₁ : ∀ x y, Out.WeilIs PB.A PB.L n (lev₁ x) (lev₁ y)
      (unitOn (Units.map (f₁.comp b).toMonoidHom ze ^ omegaStd x y)) := fun x y => by
    refine GlobalTheory.T.weilPairing_eq_of_fractionField_domain V PB W L f₁ e hel n _ _ (tor₁ x) (tor₁ y) _ ?_
    rw [hlev₁, hlev₁, map_zpow]
    have hz : Units.map (algebraMap W L).toMonoidHom (Units.map (f₁.comp b).toMonoidHom ze) =
        Units.map (algebraMap (FractionRing V) L).toMonoidHom ζ := Units.ext (by
      show (algebraMap W L) (f₁ (b (zetaAway n))) = (algebraMap (FractionRing V) L) ((algebraMap V (FractionRing V)) (b (zetaAway n)))
      exact congrArg (fun q : V →+* L => q (b (zetaAway n))) hcomp)
    rw [hz]
    exact hweil x y
  obtain ⟨s, β₁, β₁₂, d', hP, hpb, hsq, hlb, hdd⟩ :=
    GlobalTheory.T.exists_siegelObject_of_symplecticLevel_points n hn3 V W f₁ b PB lev₁ r d₁ (fun i => c (Pi.single i 1)) add₁ tor₁ weil₁ div₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, f₁, s, β₁, β₁₂, d',
    ⟨inferInstance, inferInstance, hcW, charZero_of_injective_ringHom hinj⟩, inferInstance, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, hP, hpb, hsq, hlb, hdd⟩

end GlobalTheory.LevelAfterExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelLevel_after_finiteExtension_DVR : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c (Pi.single i 1)).left := by
  first | exact @GlobalTheory.LevelAfterExt.exists_siegPre_divPoints | exact GlobalTheory.LevelAfterExt.exists_siegPre_divPoints | (intros; apply GlobalTheory.LevelAfterExt.exists_siegPre_divPoints <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowChart.Compare

open TopologicalSpace

section Comp

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gm_self_of_pgen (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) {Y : Scheme.{0}} (f : Y ⟶ X')
    (y : Y) {j : L.ι} {i : L'.ι} (hj : F (f y) ∈ L.U j) (hi : f y ∈ L'.U i) :
    gm (f ≫ F) y (L.U j ⊓ L.U j) (L.g j j) = 1 := by
  have c := hw Y f y j j i i hj hj hi hi
  rw [gm_self hL' f y hi, inv_one, _root_.mul_one] at c
  exact mul_eq_right.1 c.symm

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [gm_self_of_pgen hL' w hw (f ≫ F') y hj hi] at a
  rw [gm_self hL'' f y hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL'' : L''.IsLB) :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL' hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1
          h₂.2.1 h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Comp

end GlobalTheory.LowChart.Compare

namespace GlobalTheory.LowChart

theorem exists_siegAt_of_siegPB : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {S S₀ : Scheme.{0}} (g : S ⟶ S₀) (s' : S ⟶ Sp o) (x : S ⟶ F.X), x ≫ F.s = s' → ∀ (c : SiegPre h n ζ s'), SiegPB c F.univ x → ∀ (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (Q : LB (G2 A₀).left) (β : c.A.left ⟶ A₀.left) (β₂ : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ g β → IsSquare β β₂ → LBIso c.P (Q.pull β₂) → ∀ (r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ c.A)), ∃ (v : S ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = s') (β₁ : (GlobalTheory.LowChart.siegAt F v s' hs).A.left ⟶ A₀.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v s' hs).A).left ⟶ (G2 A₀).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v s' hs).A A₀ g β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v s' hs).P (Q.pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v s' hs a).left ≫ β₁ = (∏ i, d i ^ a i).left ≫ β := by
  intro o _ ζ h n F S S₀ g s' x hx c hc A₀ _ _ Q β β₂ hβ hβ₂ hQ r d
  obtain ⟨φ, φ₂, hφ, hφ₂, hP, -⟩ := hc
  have hp : ∀ i, ((d i).left ≫ φ) ≫ F.univ.A.hom = x := fun i => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (d i)]
    exact Category.id_comp _
  obtain ⟨v, hv, hvc⟩ : ∃ v : S ⟶ (powA F r).left, v ≫ (powA F r).hom = x ∧
      ∀ i, v ≫ (coord F i).left = (d i).left ≫ φ :=
    ⟨lift x (fun i => (d i).left ≫ φ) hp, lift_hom _ _ _, fun i => lift_coord _ _ _ i⟩
  have hs : v ≫ toO F r = s' := by
    rw [toO, ← Category.assoc, hv, hx]
  refine ⟨v, hs, ?_⟩
  have hpb : IsGrpPullback (siegAt F v s' hs).A F.univ.A x (Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A) :=
    (Pdiv.PullbackComparison.isGrpPullback _ _).congr hv rfl
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hpb hφ
  haveI := he
  let C := siegAt F v s' hs
  let θ₂ : (G2 C.A).left ⟶ (G2 c.A).left := (CartesianMonoidalCategory.lift (fst C.A C.A ≫ e.hom) (snd C.A C.A ≫ e.hom)).left
  have hθf : θ₂ ≫ (fst c.A c.A).left = (fst C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst, Over.comp_left]
  have hθs : θ₂ ≫ (snd c.A c.A).left = (snd C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd, Over.comp_left]
  refine ⟨e.hom.left ≫ β, θ₂ ≫ β₂, ((isGrpPullback_of_iso e).comp hβ).congr (Category.id_comp g) rfl,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hβ₂.1, ← Category.assoc, hθf, Category.assoc]
  · rw [Category.assoc, hβ₂.2, ← Category.assoc, hθs, Category.assoc]
  · have hθ₂ : Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A = θ₂ ≫ φ₂ :=
      have e1 : (θ₂ ≫ φ₂) ≫ (fst F.univ.A F.univ.A).left =
          (fst C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.1, ← Category.assoc, hθf, Category.assoc, heφ]
      have e2 : (θ₂ ≫ φ₂) ≫ (snd F.univ.A F.univ.A).left =
          (snd C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.2, ← Category.assoc, hθs, Category.assoc, heφ]
      Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components (G := F.univ.A) _ _
        ((Pdiv.PullbackComparison.pφ₂_fst _ _).trans e1.symm) ((Pdiv.PullbackComparison.pφ₂_snd _ _).trans e2.symm)
    have w1 : LBIso C.P (c.P.pull θ₂) :=
      LBIso.chartPull (chartPullSame F.univ.P (fun _ : PUnit.{1} => Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A)
        (fun _ => φ₂) (fun _ => 1) θ₂ (fun _ => hθ₂)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P θ₂ θ₂ rfl) (LBIso.symm hP)
    obtain ⟨w, hw⟩ := hQ
    obtain ⟨w', hw'⟩ := w1
    have pw := (isGen_iff w).1 hw
    have pw' := (isGen_iff w').1 hw'
    obtain ⟨w'', T⟩ := Compare.exists_comp' c.isLB w w' pw pw' C.isLB
    exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp c.isLB pw pw')⟩
  · have hpt : ∀ i, ptAt F v s' hs i ≫ e.hom = d i := fun i =>
      Over.OverMorphism.ext (hφ.1.hom_ext
        (by rw [Over.comp_left, Category.assoc, heφ, ptAt_left, hvc])
        (by rw [Over.comp_left, Category.assoc, Over.w e.hom, Over.w (ptAt F v s' hs i), Over.w (d i)]))
    let ψ : (𝟙_ (Over S) ⟶ C.A) →* (𝟙_ (Over S) ⟶ c.A) :=
      MonoidHom.mk' (· ≫ e.hom) fun a b => MonObj.mul_comp a b e.hom
    intro a
    have key : cAt F v s' hs a ≫ e.hom = ∏ i, d i ^ a i := by
      show ψ (cAt F v s' hs a) = _
      rw [cAt, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow]
      exact congrArg (· ^ a i) (hpt i)
    rw [← Category.assoc, ← Over.comp_left, key]

end GlobalTheory.LowChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelObject_fibrePower_at_sections : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {S S₀ : Scheme.{0}} (g : S ⟶ S₀) (s' : S ⟶ Sp o) (x : S ⟶ F.X), x ≫ F.s = s' → ∀ (c : SiegPre h n ζ s'), SiegPB c F.univ x → ∀ (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (Q : LB (G2 A₀).left) (β : c.A.left ⟶ A₀.left) (β₂ : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ g β → IsSquare β β₂ → LBIso c.P (Q.pull β₂) → ∀ (r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ c.A)), ∃ (v : S ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = s') (β₁ : (GlobalTheory.LowChart.siegAt F v s' hs).A.left ⟶ A₀.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v s' hs).A).left ⟶ (G2 A₀).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v s' hs).A A₀ g β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v s' hs).P (Q.pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v s' hs a).left ≫ β₁ = (∏ i, d i ^ a i).left ≫ β := by
  first | exact @GlobalTheory.LowChart.exists_siegAt_of_siegPB | exact GlobalTheory.LowChart.exists_siegAt_of_siegPB | (intros; apply GlobalTheory.LowChart.exists_siegAt_of_siegPB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivPush

theorem push_div_pts : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  intro S S₀ f G _ _ G₀ _ _ β hp n r d c hc hd a
  let T : Over S := 𝟙_ (Over S)
  let U : Over.mk (T.hom ≫ f) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = f := by
    simp [U, T, Over.toUnit_left]
  let cH : (Fin r → ℤ) →+ Additive (𝟙_ (Over S₀) ⟶ G₀) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) (fun a a' => by simp [hc])
  have hca : c a = ∏ i, c (Pi.single i 1) ^ a i := by
    have e : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin r → ℤ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have := congrArg cH e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_zsmul] at this
    exact congrArg Additive.toMul this
  have hdi : ∀ i, pushHom hp T (d i ^ n) = preHom U (c (Pi.single i 1)) := by
    intro i
    apply Over.OverMorphism.ext
    show (d i ^ n).left ≫ β = U.left ≫ (c (Pi.single i 1)).left
    rw [hU]; exact hd i
  have key : pushHom hp T (∏ i, d i ^ ((n : ℤ) * a i)) = preHom U (c a) := by
    rw [hca, map_prod, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_zpow, map_zpow, zpow_mul, zpow_natCast, ← map_pow, hdi]
  have := congrArg (fun z => z.left) key
  rw [← hU]
  exact this

end GlobalTheory.DivPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpPullback_divisionPoints_push_eq : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  first | exact @GlobalTheory.DivPush.push_div_pts | exact GlobalTheory.DivPush.push_div_pts | (intros; apply GlobalTheory.DivPush.push_div_pts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem exists_fibrePow_point_of_polAV : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  intro n hn hodd V _ _ _ hV hD b PB r c hc
  obtain ⟨V₁, _, _, _, f₁, s, β, β₂, d, h1, h2, h3, h4, h5, hP, hpb, hsq, hlb, hd⟩ :=
    GlobalTheory.T.exists_siegelLevel_after_finiteExtension_DVR n hn hodd V hV hD b PB r c
  have : CharZero V₁ := h1.2.2.2
  obtain ⟨F, x, hx, hpbF⟩ := GlobalTheory.T.exists_siegel_family_point_of_principal_object n hn hodd PB.g V₁ (f₁.comp b) s hP
  obtain ⟨v, hs, β₁, β₁₂, p1, p2, p3, p4⟩ :=
    GlobalTheory.T.exists_siegelObject_fibrePower_at_sections F (spMap f₁) (spMap (f₁.comp b)) x hx s hpbF PB.A (abelian₂ PB.A PB.L) β β₂ hpb hsq hlb r d
  refine ⟨F, V₁, inferInstance, inferInstance, inferInstance, f₁, v, hs, h1, h2, h3, h4, h5, β₁, β₁₂, p1, p2, p3,
    fun a => ?_⟩
  rw [p4]
  exact GlobalTheory.T.grpPullback_divisionPoints_push_eq (spMap f₁) s.A PB.A β hpb n r d c hc hd a

end GlobalTheory.LowChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibrePower_point_finite_extension_dvr : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  first | exact @GlobalTheory.LowChart.exists_fibrePow_point_of_polAV | exact GlobalTheory.LowChart.exists_fibrePow_point_of_polAV | (intros; apply GlobalTheory.LowChart.exists_fibrePow_point_of_polAV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_lowBase_of_trait : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn ho V _ _ _ hV hd b PB r c hc
  obtain ⟨F, V₁, _, _, _, f₁, v, hs, hV₁, hd₁, hi₁, hf₁, hl₁, β₁, β₁₂, hp₁, hq₁, hL₁, hc₁⟩ :=
    GlobalTheory.T.exists_fibrePower_point_finite_extension_dvr n hn ho V hV hd b PB r c hc
  obtain ⟨L, V', _, _, _, f, κ, e, hh, hV', hd', hi, hf, hl, hκ, hb, B', _, β', β'', β₂, β₂', hp, hp', hq, hq', hL, hx⟩ :=
    GlobalTheory.T.siegelFibrePower_point_lifts_to_lower_base n hn ho PB.g F r V₁ hV₁ hd₁ (f₁.comp b) v hs
  have es : spMap (f.comp f₁) = spMap f ≫ spMap f₁ := by
    rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hl' : IsLocalHom (f.comp f₁) := RingHom.isLocalHom_comp f f₁
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f.comp f₁, κ, e, hh, hV', hd', hi.comp hi₁,
    hf.comp hf₁, hl', hκ, ?_, B', inferInstance, β' ≫ β₁, β'', β₂ ≫ β₁₂, β₂', ?_, hp', isSquare_comp hq hq₁, hq', ?_, ?_⟩
  · rw [hb, RingHom.comp_assoc]
  · rw [es]
    exact hp.comp hp₁
  · have h1 : LBIso ((LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ PB.A PB.L).pull (β₂ ≫ β₁₂)) :=
      lbIso_pull_comp hL₁ β₂ rfl
    exact LBIso.trans (pull_isLB (LB.isLB_linComb PB.isLB _ _) _) (pull_isLB (LowChart.siegAt F v _ hs).isLB _)
      (pull_isLB (LB.isLB_linComb L.T.M.isLB _ _) _) h1.symm hL
  · intro a
    obtain ⟨x, h1, h2, h3⟩ := hx a
    refine ⟨x, h1, ?_, h3⟩
    rw [← Category.assoc, h2, Category.assoc, hc₁, es, Category.assoc]

end GlobalTheory.TChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lower_base_of_trait_abelian_part : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = PB.g ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ PB.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 PB.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' PB.A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((abelian₂ PB.A PB.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (c (e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  first | exact @GlobalTheory.TChart.exists_lowBase_of_trait | exact GlobalTheory.TChart.exists_lowBase_of_trait | (intros; apply GlobalTheory.TChart.exists_lowBase_of_trait <;> assumption)
end
