module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientUniqueOfComp
public import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftExistsOfQuotientLevel
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplierIsUnit
public import Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliObjectExists
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TracePullbackIdentity
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceIdentityOfTjElement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceCRTOfLatticeGen
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TowerCoveringOfInvariantFiniteEtaleSeparated
public import Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeCorrespondenceLiesInTowerOfLiftCount
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.QuotObjLink
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOverStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.StandardDatumExists
open UpperTheory.Gal.Int.Geo

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen in
theorem UpperTheory.standard_datum_exists :
    StdEx := by
  intro p _ D ha E _ _ e
  let φ : 𝓞 D.F →+* E := (e : D.F →+* E).comp (algebraMap (𝓞 D.F) D.F)
  have key : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]
    ring
  have hroot : φ D.ω ^ 2 - (D.tr : E) * φ D.ω + (D.nm : E) = 0 := by
    simpa using congrArg φ key
  have hsub : Subsingleton (Fin D.toG.a) := by
    have h : D.toG.a = 1 := ha
    rw [h]
    infer_instance
  exact ⟨{ ρ := φ D.ω
           ρ_root := hroot
           t := fun _ => φ
           t_ω := fun _ => rfl
           comax := fun i j hij => (hij (Subsingleton.elim i j)).elim }, rfl, fun _ _ => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.PowerMapCartesian
open UpperTheory.Gal.Int.Geo
open CategoryTheory

theorem UpperTheory.power_map_cartesian :
    PowCart := by
  intro X Y Z A B C f g φ χ u v k
  refine ⟨fun H => GlobalTheory.KS.PowPB.powMap_isPullback _ _ _ _ f φ u H k,
    GlobalTheory.KS.PowPB.powMap_w f φ u k, fun w => ?_⟩
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_w]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      Category.assoc, GlobalTheory.KS.PowPB.powMap_pr]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.GroupSchemePullbackExists
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.group_scheme_pullback_exists :
    GPull := by
  intro G R _ _ gb N X X' s e o
  exact GlobalTheory.UPel.HT.Gen.BaseChange.exists_gObjMap_pull e o
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientSeparatedOfTraceUnitCrt
open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem UpperTheory.quotient_separated_of_trace_unit_crt :
    GPull → QComp → QIso → QUniq → TrEta → TrEtaPt → TrUnit → CongCRT → BaseSep := by
  intro hGP hQC hQI hQU hTE hTP hTU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C u hu W Ω _ _ z hz
  have huN : L.CongOne S.N₀ u ∧ L.CongOne S.N₀ u⁻¹ := hu
  have hu1 : u ∈ L.KN 1 := KN_anti (one_dvd _) hu
  have hInt : Integ L u := integ_of_mem hu1
  rw [hLev]
  refine ⟨hu1, ?_⟩
  rw [S.lev]
  obtain ⟨hcrt1, hcrt2⟩ := hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hInt
  rw [hcrt1]
  refine ⟨huN.1, ?_⟩
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  rw [hcrt2 a N hNpos N.2.2 hNum.2]
  intro y
  set x := (algebraMap (𝓞 D.F) D.O a) • y with hx
  refine (hTP p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans Ω z x).2 rfl x ?_
  have ht : (toUnit (Over.mk z)).left = z := by
    simpa using Over.w (toUnit (Over.mk z))
  obtain ⟨oz, ⟨mz⟩⟩ := hGP _ _ gb (N : ℕ) (T.M N).X (Sp Ω) (T.M N).s z (T.M N).univ
  obtain ⟨nW, hnW⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans hu1
  have heta : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ W.ψ = W.o.eta (c • y') := by
    intro y'
    refine hTE p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans S.N₀ c c hNum.1 hNum.1
      y' y' ?_
    exact huN.1 _ (inAf_mem D y')
  obtain ⟨nI, hnI⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb N N S.N₀ c c _ _ _ _ (T.M N).univ W.o S.Y.univ _ W.ψ hiso W.trans.1
    W.trans.2.1 hlb heta nW
  obtain ⟨nA, hnA⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ oz z mz C.m
  obtain ⟨nB, hnB⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ (W.π ≫ C.j) (𝟙 _)).2.2.2
    _ _ oz z mz nI
  have hfeq : z ≫ W.π ≫ C.j = z ≫ C.j := hz
  have hAB : mz.φ ≫ Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = mz.φ ≫ C.m.φ := by
    generalize hF : z ≫ W.π ≫ C.j = F at nB hnB
    have hF' : F = z ≫ C.j := hF.symm.trans hfeq
    subst hF'
    have h := hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c S.std.three S.std.cop _ _ _ _ _ _ _ nB nA
    rw [hnB, hnI, hnW, hnA] at h
    exact h
  apply Over.OverMorphism.ext
  apply nW.cart.1.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [hnW, reassoc_of% (W.φ.eta x)]
    have hl := C.lv y
    have hr : Over.Hom.left ((T.M N).univ.eta x) ≫ C.m.φ = C.j ≫ Over.Hom.left (S.Y.lv y) := hl
    have hz' := mz.eta x
    rw [ht]
    rw [← reassoc_of% hz', hAB, reassoc_of% hz', hr, reassoc_of% hfeq]
  · simp only [Over.comp_left, Category.assoc, Over.w]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SiteExistsOfSplittingAndPowerProjector
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
open UpperTheory.Gal.Int.Geo

theorem UpperTheory.site_exists_of_splitting_and_power_projector :
    MIn → SplitQ → BaseEx → PowProj → SiteEx := by
  intro hM hS hB hP
  intro p _ D G hSc E _ _ e gb hstd w q _ r 𝔴 𝔫 hpl hat hlev
  have sp := hS p D hSc.m1 q
  obtain ⟨N₀, 𝔞, h3, hcq, hcp, hsup, hupow, hlv⟩ := hlev
  obtain ⟨f, b, hmat, hstdb, hqmem, hnorm⟩ :=
    hB q (datAt hat sp) hSc.a1 hSc.m1 E e gb hstd w 𝔴 r hpl hat.le N₀ h3 hcq
  obtain ⟨M⟩ := hM.ex q (datAt hat sp) (Ow w) b N₀ h3 hcq
  have hEt : UpperTheory.Gal.FiniteEtaleModels.IsEtIdeal b 𝔞 :=
    (hM.placeOf q (datAt hat sp) (Ow w) b r 𝔴 hat.max hstdb.pmem hSc.a1 hstdb.ule hstdb.tw 𝔞 hsup).2 hupow
  obtain ⟨Y, π, ρ, hov, ⟨hmπ⟩, hgal⟩ := hM.finModel q (datAt hat sp) (Ow w) b N₀ h3 hcq 𝔞 1 hEt M
  have hfin : IsFinite π := hgal.fin
  have het : Etale π := hgal.etale
  have hMproj : IsProjOver M.s := hM.proj q (datAt hat sp) (Ow w) b N₀ h3 hcq hSc.cpt M
  have hYproj : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.T.isProjOver_comp_finite (Ow w) M.X Y.X π M.s hfin hMproj
  have hYsm : SmoothOfRelativeDimension (0 + (datAt hat sp).a * ((datAt hat sp).n - 1)) Y.s := by
    rw [← hov]
    haveI : SmoothOfRelativeDimension 0 π := by
      rw [← AlgebraicGeometry.Etale.eq_smoothOfRelativeDimension_zero]
      exact het
    haveI := M.smooth
    infer_instance
  have hPw := fun k => hP q (datAt hat sp) (Ow w) b N₀ h3 hcq Y.X Y.s Y.univ k
  exact ⟨⟨hat, sp, f, b, hmat, N₀, 𝔞, hstdb, hqmem, hnorm, hcp, hsup, hupow, hlv, M, Y, π, hov, hmπ,
    hfin, het, fun k => (hPw k).1 hYproj, fun k => (hPw k).2 _ hYsm⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem level_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (hl : IsEtLevOver o 𝔞 r l) {u v : D.La}
    (e : (wSub D 𝔞 r).mkQ u = (wSub D 𝔞 r).mkQ v) : l u = l v := by
  have hmem : u - v ∈ wSub D 𝔞 r := (Submodule.Quotient.eq _).mp e
  have h1 : l (u - v) = 1 := hl.2.2.1 _ hmem
  calc l u = l ((u - v) + v) := by rw [sub_add_cancel]
    _ = l (u - v) * l v := hl.1 _ _
    _ = l v := by rw [h1, _root_.one_mul]

private theorem rep_ext {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {Y : Scheme.{0}} {π : Y ⟶ S}
    {lu : D.La → (Over.mk π ⟶ o.A)} (hlu : IsEtLevOver o 𝔞 r lu)
    (hrep : ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o 𝔞 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y)
    {T : Over S} {f f' : T ⟶ Over.mk π} (h : ∀ y, f ≫ lu y = f' ≫ lu y) : f = f' := by
  obtain ⟨g, -, huniq⟩ := hrep T (fun y => f ≫ lu y)
    (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu f hlu)
  rw [huniq f (fun y => rfl), huniq f' (fun y => (h y).symm)]

theorem UpperTheory.Gal.FiniteEtaleModels.finCover_holds :
    RepAll → PtAll → GrpFin → FinCover := by
  intro hRep hPt hGrp p _ D R _ b N 𝔞 r hN hcop het S _ s o
  obtain ⟨Y, π, lu, hfin, het', hlu, hrep⟩ := hRep p D R b N 𝔞 r hcop het S s o
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y s π o
  have hpb := m.cart.1
  have hluw : ∀ y, (lu y).left ≫ o.A.hom = 𝟙 Y ≫ π := fun y => by
    rw [Category.id_comp]; exact Over.w (lu y)
  let lv : D.La → (𝟙_ (Over Y) ⟶ o'.A) := fun y =>
    Over.homMk (hpb.lift (lu y).left (𝟙 Y) (hluw y)) (by rw [hpb.lift_snd]; rfl)
  have hlv : ∀ y, (lv y).left ≫ m.φ = (lu y).left := fun y => hpb.lift_fst _ _ _
  have hlv2 : ∀ y, (lv y).left ≫ o'.A.hom = 𝟙 Y := fun y => hpb.lift_snd _ _ _
  have hpt : ∀ y, ptOf m (lv y) = lu y := fun y => by
    ext1; exact hlv y
  have hcomp : ∀ (a c : LevGrp D 𝔞 r) (y : D.La), lu (levAct a (levAct c y)) = lu (levAct (a * c) y) :=
    fun a c y => level_congr hlu (by rw [mkQ_levAct, mkQ_levAct, mkQ_levAct]; rfl)
  have hone : ∀ y, lu (levAct (1 : LevGrp D 𝔞 r) y) = lu y :=
    fun y => level_congr hlu (by rw [mkQ_levAct]; rfl)
  have hact : ∀ g : LevGrp D 𝔞 r, ∃ f : Over.mk π ⟶ Over.mk π, ∀ y, f ≫ lu y = lu (levAct g y) :=
    fun g => (hrep _ _ (GlobalTheory.T.etale_level_group_action p D R b N S s o 𝔞 r _ lu g hlu)).exists
  choose fg hfg using hact
  have hfgeq : ∀ (f : Over.mk π ⟶ Over.mk π) (g : LevGrp D 𝔞 r),
      (∀ y, f ≫ lu y = lu (levAct g y)) → f = fg g :=
    fun f g hf => rep_ext hlu hrep (fun y => by rw [hf, hfg])
  refine ⟨Y, π, o', m, lv, fun g => (fg g).left, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S Y s π (π ≫ s) o o' m 𝔞 r lv]
    simpa only [hpt] using hlu
  · refine ⟨(hGrp p D 𝔞 r het.1).2, ?_, ?_, ?_, hfin, het', ?_, ?_⟩
    · show (fg 1).left = 𝟙 Y
      rw [← hfgeq (𝟙 _) 1 (fun y => by rw [Category.id_comp, hone])]
      rfl
    · intro a c
      show (fg (a * c)).left = (fg a).left ≫ (fg c).left
      rw [← hfgeq (fg a ≫ fg c) (a * c) (fun y => by rw [Category.assoc, hfg, hfg, hcomp])]
      rfl
    · intro a
      exact Over.w (fg a)
    · constructor
      intro x
      obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point S x
      obtain ⟨l, hl⟩ := hPt p D R b N 𝔞 r hcop het S s o k a
      obtain ⟨f, -, -⟩ := hrep _ l hl
      have hx : x ∈ Set.range ⇑a := by rw [ha]; rfl
      obtain ⟨q, hq⟩ := hx
      have hw : f.left ≫ π = a := Over.w f
      refine ⟨f.left q, ?_⟩
      rw [← hq, ← Scheme.Hom.comp_apply, hw]
    · intro K _ _ y y' hyy
      let j : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y rfl
      let j' : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y' hyy.symm
      have hl := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j hlu
      have hl' := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j' hlu
      obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver p D R b N S s o 𝔞 r K (y ≫ π) _ _ hl hl'
      refine ⟨g, ?_, ?_⟩
      · have : j ≫ fg g = j' := rep_ext hlu hrep (fun z => by rw [Category.assoc, hfg]; exact hg z)
        exact congrArg (fun q => Over.Hom.left q) this
      · intro a ha
        apply hguniq
        intro z
        show j ≫ lu (levAct a z) = j' ≫ lu z
        have : j ≫ fg a = j' := by ext1; exact ha
        rw [← hfg, ← Category.assoc, this]
  · intro T t o₁ m₁ l hl
    have hl' := (GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S T s t (t ≫ s) o o₁ m₁ 𝔞 r l).mp hl
    obtain ⟨g, hg, hguniq⟩ := hrep (Over.mk t) _ hl'
    have hgw : g.left ≫ π = t := Over.w g
    have hφ : ∀ (f : T ⟶ Y) (_ : f ≫ π = t) (m₃ : GlobalTheory.UPel.HT.ObjMap o₁ o (f ≫ π)), m₃.φ = m₁.φ :=
      fun f hf m₃ => Rigid.objMap_phi_unique p D R b N hN hcop S T s (t ≫ s) o o₁ (f ≫ π) t m₃ m₁ hf
    have hgl : ∀ y, (l y).left ≫ m₁.φ = g.left ≫ (lu y).left := fun y => by
      have := congrArg (fun q => Over.Hom.left q) (hg y)
      exact this.symm
    refine ⟨g.left, ⟨hgw, ?_⟩, ?_⟩
    · obtain ⟨m₂, hm₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ
        (by rw [hgw]; exact m₁ : GlobalTheory.UPel.HT.ObjMap o₁ o (g.left ≫ π)) m
      refine ⟨m₂, fun y => ?_⟩
      apply hpb.hom_ext
      · rw [Category.assoc, hm₂, hφ _ hgw, Category.assoc, hlv, hgl]
      · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (l y), Category.assoc, hlv2,
          Category.comp_id]
        exact Category.id_comp _
    · rintro f' ⟨hf', m₂', hm₂'⟩
      obtain ⟨m₃, hm₃⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂' m
      have : (Over.homMk f' hf' : Over.mk t ⟶ Over.mk π) = g := by
        apply hguniq
        intro y
        ext1
        show f' ≫ (lu y).left = (l y).left ≫ m₁.φ
        rw [← hlv, ← Category.assoc, ← hm₂' y, Category.assoc, ← hm₃, hφ f' hf' m₃]
      exact congrArg (fun q => Over.Hom.left q) this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

set_option maxHeartbeats 1000000 in
theorem UpperTheory.Gal.FiniteEtaleModels.crtMul_holds :
    CrtMul := by
  intro p _ D R _ b N S s o 𝔞 𝔟 hab T l₁ l₂ h1 h2
  have hmon : ∀ c, IsMonHom (o.act.act c) := o.act.hom
  obtain ⟨a, ha, b', hb, habe⟩ : ∃ a ∈ 𝔞, ∃ b' ∈ 𝔟, a + b' = 1 := by
    have h1m : (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟 := by
      rw [hab]
      exact Submodule.mem_top
    obtain ⟨a, ha, b', hb, h⟩ := Submodule.mem_sup.1 h1m
    exact ⟨a, ha, b', hb, h⟩
  have split : ∀ {X : Over S} (f : X ⟶ o.A),
      f ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) * f ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') = f := by
    intro X f
    rw [← MonObj.comp_mul, ← o.act.add, ← map_add (f := _), habe, map_one, o.act.one, Category.comp_id]
  have gen : ∀ (I : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y : D.La,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D I 1 := by
    intro I c hc y
    exact Submodule.subset_span ⟨c, by simpa using hc, y, rfl⟩
  have mulsub : ∀ (I J : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y ∈ wSub D J 1,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D (I * J) 1 := by
    intro I J c hc y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c', hc', z', rfl⟩ := hz
      rw [← mul_smul, ← map_mul]
      exact gen _ _ (Ideal.mul_mem_mul hc (by simpa using hc')) z'
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul o' x _ hx =>
      rw [← mul_smul, Algebra.commutes, mul_smul]
      exact Submodule.smul_mem _ _ hx
  have wmono : ∀ (I J : Ideal (𝓞 D.F)), I ≤ J → wSub D I 1 ≤ wSub D J 1 := by
    intro I J h
    apply Submodule.span_mono
    rintro z ⟨c, hc, z', rfl⟩
    exact ⟨c, by simpa using h (by simpa using hc), z', rfl⟩
  have kill : ∀ (I : Ideal (𝓞 D.F)) (l : D.La → (T ⟶ o.A)), IsEtLevOver o I 1 l →
      ∀ {X : Over S} (P : X ⟶ T) (y : D.La) (c : 𝓞 D.F), c ∈ I →
        (P ≫ l y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro I l hl X P y c hc
    rw [Category.assoc, ← hl.2.1, hl.2.2.1 _ (gen I c hc y), MonObj.comp_one]
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · dsimp only
    rw [h1.1, h2.1]
    exact mul_mul_mul_comm _ _ _ _
  · dsimp only
    rw [h1.2.1, h2.2.1, MonObj.mul_comp]
  · dsimp only
    have hxa : x ∈ wSub D 𝔞 1 := wmono (𝔞 * 𝔟) 𝔞 (Ideal.mul_le_left : 𝔞 * 𝔟 ≤ 𝔞) hx
    have hxb : x ∈ wSub D 𝔟 1 := wmono (𝔞 * 𝔟) 𝔟 (Ideal.mul_le_right : 𝔞 * 𝔟 ≤ 𝔟) hx
    rw [h1.2.2.1 x hxa, h2.2.2.1 x hxb]
    exact mul_one 1
  · dsimp only at hy
    rw [MonObj.comp_mul] at hy
    have hu : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y = 1 := by
      have e1 := congrArg (· ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) hy
      simp only [MonObj.mul_comp, MonObj.one_comp, kill _ l₂ h2 _ _ _ hb, _root_.mul_one] at e1
      rw [← split (Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y), kill _ l₁ h1 _ _ _ ha, e1, _root_.one_mul]
    have hv : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₂ y = 1 := by
      rw [hu, _root_.one_mul] at hy
      exact hy
    have y1 := (h1.2.2.2 k x).1 y hu
    have y2 := (h2.2.2.2 k x).1 y hv
    have hsplit : y = algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b' • y := by
      rw [← add_smul, ← map_add (f := _), habe, map_one, one_smul]
    rw [hsplit]
    refine Submodule.add_mem _ (mulsub 𝔞 𝔟 a ha y y2) ?_
    have h3 := mulsub 𝔟 𝔞 b' hb y y1
    rwa [mul_comm] at h3
  · have hg' : ∀ c ∈ 𝔞 * 𝔟, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hg c (by simpa using hc)
    have hk1 : ∀ c ∈ 𝔞, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul]
      exact hg' _ (Ideal.mul_mem_mul hc hb)
    have hk2 : ∀ c ∈ 𝔟, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm]
      exact hg' _ (Ideal.mul_mem_mul ha hc)
    obtain ⟨y₁, hy₁⟩ := (h1.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))
      (fun c hc => hk1 c (by simpa using hc))
    obtain ⟨y₂, hy₂⟩ := (h2.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
      (fun c hc => hk2 c (by simpa using hc))
    have e1 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))]
      rw [hk1 a ha, _root_.one_mul]
    have e2 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))]
      rw [hk2 b' hb, _root_.mul_one]
    refine ⟨algebraMap (𝓞 D.F) D.O b' • y₁ + algebraMap (𝓞 D.F) D.O a • y₂, ?_⟩
    dsimp only
    rw [h1.1, h2.1, h1.2.2.1 _ (gen 𝔞 a ha y₂), h2.2.2.1 _ (gen 𝔟 b' hb y₁), _root_.mul_one, _root_.one_mul,
      h1.2.1, h2.2.1, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, hy₁, hy₂, e1, e2, mul_comm]
    exact split g
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.finModel_holds :
    FinCover → FinModel := by
  intro cover p _ D R _ _ b N h3 hcop 𝔞 r h𝔞 M
  haveI : Smooth M.s := M.smooth.smooth
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, q, u, mu, lev, act, hlev, hgal, hrep⟩ :=
    cover p D R b N 𝔞 r h3 hcop h𝔞 M.X M.s M.univ
  let E : EtModel b N 𝔞 r :=
    { X := Y, s := q ≫ M.s, univ := u, lv := lev, isLev := hlev
      rep := by
        intro T t o l hl
        obtain ⟨c, ⟨hc, ⟨mc⟩⟩, cuniq⟩ := M.rep T t o
        subst hc
        obtain ⟨f, ⟨hfq, m₂, hm₂⟩, funiq⟩ := hrep T c o mc l hl
        refine ⟨f, ⟨?_, m₂, hm₂⟩, ?_⟩
        · rw [← Category.assoc, hfq]
        · rintro f' ⟨hs, m', hm'⟩
          refine funiq f' ⟨?_, m', hm'⟩
          obtain ⟨mcomp⟩ := objMap_comp p D R b N T Y M.X (c ≫ M.s) (q ≫ M.s) M.s o u M.univ f' q m' mu
          exact cuniq (f' ≫ q) ⟨by rw [Category.assoc, ← hs], ⟨mcomp⟩⟩ }
  exact ⟨E, q, act, rfl, ⟨mu⟩, hgal⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPlaceOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private lemma map_eq_zero_of_mem_max {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] {k : Type} [Field k] [CharP k p] (β : O →+* k) {x : O}
    (hx : x ∈ IsLocalRing.maximalIdeal O) : β x = 0 := by
  have hprime : (RingHom.ker β).IsPrime := RingHom.ker_isPrime β
  have hp : ((p : ℕ) : O) ∈ RingHom.ker β := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  have hne : RingHom.ker β ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  have hmax : (RingHom.ker β).IsMaximal := IsPrime.to_maximal_ideal hne
  have heq : RingHom.ker β = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  rw [← heq] at hx
  exact hx

private lemma exists_map_ker {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F]
    (J : Ideal (𝓞 F)) (hJ : J.IsMaximal) (hp : (p : 𝓞 F) ∈ J) (hne : J ≠ ⊥)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ φ : 𝓞 F →+* k, RingHom.ker φ = J := by
  classical
  letI : Field (𝓞 F ⧸ J) := Ideal.Quotient.field J
  have hpr : p.Prime := Fact.out
  haveI : CharP (𝓞 F ⧸ J) p := by
    rw [CharP.charP_iff_prime_eq_zero hpr]
    rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  haveI : Finite (𝓞 F ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hne
  letI : Algebra (ZMod p) (𝓞 F ⧸ J) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI : Module.Finite (ZMod p) (𝓞 F ⧸ J) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 F ⧸ J) := Algebra.IsAlgebraic.of_finite _ _
  let ψ : (𝓞 F ⧸ J) →ₐ[ZMod p] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(ψ : (𝓞 F ⧸ J) →+* k).comp (Ideal.Quotient.mk J), ?_⟩
  rw [RingHom.ker_comp_of_injective _ (ψ : (𝓞 F ⧸ J) →+* k).injective, Ideal.mk_ker]

theorem UpperTheory.Gal.FiniteEtaleModels.placeOf_holds :
    PlaceOf := by
  intro p _ D O _ _ _ _ b r w hw hpO ha hUw htw 𝔞 h𝔞w
  have hpr : p.Prime := Fact.out
  have i0 : Fin D.a := ⟨0, by omega⟩
  have hρ : ∀ (k : Type) [Field k] [CharP k p] (β : O →+* k), β b.ρ = (r : k) := by
    intro k _ _ β
    have hm : b.t i0 (D.ω - (r : 𝓞 D.F)) ∈ IsLocalRing.maximalIdeal O :=
      htw i0 _ (hUw (sub_mem_uIdeal D r))
    have h0 := map_eq_zero_of_mem_max (p := p) β hm
    rw [map_sub, map_intCast, map_sub, map_intCast, b.t_ω, sub_eq_zero] at h0
    exact h0
  constructor
  · intro h
    obtain ⟨hne, hall⟩ := h
    have hrad : uIdeal D r ≤ 𝔞.radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro P ⟨hP𝔞, hPprime⟩
      have hPne : P ≠ ⊥ := by
        rintro rfl
        exact hne (le_bot_iff.mp hP𝔞)
      have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPne
      obtain ⟨_, hpP, _, hφ⟩ := hall P hPmax hP𝔞
      haveI : CharP (IsLocalRing.ResidueField O) p := by
        rw [CharP.charP_iff_prime_eq_zero hpr, ← map_natCast (IsLocalRing.residue O)]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr hpO
      haveI : CharP (AlgebraicClosure (IsLocalRing.ResidueField O)) p := by
        rw [CharP.charP_iff_prime_eq_zero hpr,
          ← map_natCast (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure _)),
          CharP.cast_eq_zero, map_zero]
      obtain ⟨φ, hker⟩ :=
        exists_map_ker (p := p) P hPmax hpP hPne (AlgebraicClosure (IsLocalRing.ResidueField O))
      let β : O →+* AlgebraicClosure (IsLocalRing.ResidueField O) :=
        (algebraMap _ _).comp (IsLocalRing.residue O)
      have h1 := hφ (AlgebraicClosure (IsLocalRing.ResidueField O)) β φ hker
      rw [hρ _ β] at h1
      have hsub : D.ω - (r : 𝓞 D.F) ∈ P := by
        rw [← hker, RingHom.mem_ker, map_sub, map_intCast, h1, sub_self]
      unfold uIdeal
      rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hpP
      · exact hsub
    exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  · rintro ⟨e, he⟩
    have hpe : ((p : ℕ) : 𝓞 D.F) ^ e ∈ uIdeal D r ^ e := Ideal.pow_mem_pow (p_mem_uIdeal D r) e
    refine ⟨?_, ?_⟩
    · intro h
      rw [h] at he
      have h0 := he hpe
      rw [Ideal.mem_bot] at h0
      have h00 : ((p : ℕ) : 𝓞 D.F) = 0 := eq_zero_of_pow_eq_zero h0
      exact hpr.ne_zero (by exact_mod_cast h00)
    · intro w' hw' h𝔞w'
      haveI := hw'.isPrime
      have hUw' : uIdeal D r ≤ w' := Ideal.IsPrime.le_of_pow_le (he.trans h𝔞w')
      have hne : w' ≠ w := by
        rintro rfl
        exact hw'.ne_top (top_le_iff.mp (h𝔞w ▸ sup_le h𝔞w' le_rfl))
      refine ⟨hw', hUw' (p_mem_uIdeal D r), ?_, ?_⟩
      · intro i
        by_contra hspan
        obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hspan
        have hMeq : M = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hM
        have hKtop : RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) ≠ ⊤ := RingHom.ker_ne_top _
        have hwK : w ≤ RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) := by
          intro x hx
          rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
          exact htw i x hx
        have hw'K : w' ≤ RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) := by
          intro x hx
          rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← hMeq]
          exact hle (Ideal.subset_span ⟨x, hx, rfl⟩)
        exact hne ((hw'.eq_of_le hKtop hw'K).trans (hw.eq_of_le hKtop hwK).symm)
      · intro k _ _ β φ hφ
        rw [hρ k β]
        have h2 : φ (D.ω - (r : 𝓞 D.F)) = 0 := by
          rw [← RingHom.mem_ker, hφ]
          exact hUw' (sub_mem_uIdeal D r)
        rw [map_sub, map_intCast, sub_eq_zero] at h2
        exact h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepAll
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem isEtLevOver_iff_pow (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : IsEtLevOver o 𝔞 r l ↔ IsEtLevOver o (𝔞 ^ r) 1 l := by
  simp only [IsEtLevOver, wSub, pow_one]

private theorem repLev_iff_pow (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) :
    RepLev o 𝔞 r ↔ RepLev o (𝔞 ^ r) 1 := by
  unfold RepLev
  simp only [isEtLevOver_iff_pow o 𝔞 r]

private theorem mem_wSub_top (z : D.La) : z ∈ wSub D ⊤ 1 := by
  refine Submodule.subset_span ⟨1, by simp, z, ?_⟩
  simp

private theorem repLev_top (o : Obj b N s) : RepLev o ⊤ 1 := by
  refine ⟨S, 𝟙 S, fun _ => 1, inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨fun _ _ => (mul_one 1).symm, fun c _ => ?_, fun _ _ => by rfl, fun k _ _ x => ⟨fun y _ => mem_wSub_top y, fun g hg => ⟨0, ?_⟩⟩⟩
    · haveI := o.act.hom c
      exact (MonObj.one_comp _).symm
    · have h1 := hg 1 (by simp)
      rw [map_one, o.act.one, Category.comp_id] at h1
      rw [h1, MonObj.comp_one]
  · intro T l hl
    refine ⟨Over.mkIdTerminal.from T, fun y => ?_, fun f _ => Over.mkIdTerminal.hom_ext _ _⟩
    rw [MonObj.comp_one, hl.2.2.1 y (mem_wSub_top y)]

theorem repAll_holds : IdealInd → RepMul → RepAll := by
  intro hI hM p _ D R _ b N 𝔞 r hN h𝔞 S _ s o
  have key : ∀ k, RepLev o 𝔞 k := by
    refine hI (𝓞 D.F) (fun w => IsEtPlace b w) (fun 𝔟 => ∀ k, RepLev o 𝔟 k) ?_ ?_ ?_ 𝔞 h𝔞.1 h𝔞.2
    · intro k
      rw [repLev_iff_pow, Ideal.top_pow]
      exact repLev_top o
    · intro w j _ hQ k
      rw [repLev_iff_pow, ← pow_mul]
      exact (repLev_iff_pow o w (j * k)).mp (GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels p D R b N w (j * k) hN hQ S s o)
    · intro 𝔞' 𝔟 hcop h1 h2 k
      rw [repLev_iff_pow, mul_pow]
      refine hM p D R b N S s o (𝔞' ^ k) (𝔟 ^ k) ?_
        ((repLev_iff_pow o 𝔞' k).mp (h1 k)) ((repLev_iff_pow o 𝔟 k).mp (h2 k))
      exact Ideal.pow_sup_eq_top (Ideal.sup_pow_eq_top hcop)
  exact key r

end UpperTheory.Gal.FiniteEtaleModels
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private lemma smul_mem_prod {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {𝔞 𝔟 : Ideal (𝓞 D.F)}
    {e : 𝓞 D.F} (he : e ∈ 𝔟) {x : D.La} (hx : x ∈ wSub D 𝔞 1) :
    algebraMap (𝓞 D.F) D.O e • x ∈ wSub D (𝔞 * 𝔟) 1 := by
  rw [wSub] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, z', rfl⟩ := hz
    rw [smul_smul, ← map_mul]
    refine Submodule.subset_span ⟨e * c, ?_, z', rfl⟩
    rw [pow_one] at hc ⊢
    rw [mul_comm]
    exact Ideal.mul_mem_mul he hc
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_smul, Algebra.commutes, mul_smul]
    exact Submodule.smul_mem _ c ha

private lemma mem_of_mem_mul {A : Type} [CommRing A] {I J : Ideal A} {c : A} (h : c ∈ I * J) : c ∈ I :=
  Ideal.mul_le_left h

private lemma wSub_mul_le {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (𝔞 𝔟 : Ideal (𝓞 D.F)) :
    wSub D (𝔞 * 𝔟) 1 ≤ wSub D 𝔞 1 := by
  refine Submodule.span_mono ?_
  rintro z ⟨c, hc, z', rfl⟩
  rw [pow_one] at hc
  exact ⟨c, by rw [pow_one]; exact mem_of_mem_mul hc, z', rfl⟩

theorem UpperTheory.Gal.FiniteEtaleModels.crtProj_holds :
    CrtProj := by
  intro p _ D R _ b N S s o 𝔞 𝔟 e he he' T l h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hcomm : ∀ (c : D.O) (x : D.La), algebraMap (𝓞 D.F) D.O e • c • x =
      c • algebraMap (𝓞 D.F) D.O e • x := fun c x => by
    rw [smul_smul, Algebra.commutes, mul_smul]
  have he1 : 1 - e ∈ 𝔞 ^ 1 := by rwa [pow_one]
  unfold IsEtLevOver
  beta_reduce
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => h3 _ (smul_mem_prod he hx),
    fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · rw [smul_add, h1]
  · rw [hcomm, h2]
  · have hE := wSub_mul_le D 𝔞 𝔟 ((h4 k x).1 _ hy)
    have hy' : y = algebraMap (𝓞 D.F) D.O (1 - e) • y + algebraMap (𝓞 D.F) D.O e • y := by
      rw [← add_smul, ← map_add (f := _), sub_add_cancel, map_one, one_smul]
    rw [hy']
    exact Submodule.add_mem _ (Submodule.subset_span ⟨1 - e, he1, y, rfl⟩) hE
  · obtain ⟨y, hy⟩ := (h4 k x).2 g (fun c hc => hg c (by
      rw [pow_one] at hc ⊢
      exact mem_of_mem_mul hc))
    refine ⟨y, ?_⟩
    rw [h2, ← Category.assoc, hy]
    have key : g = (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (1 - e))) *
        (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O e)) := by
      rw [← MonObj.comp_mul, ← o.act.add, ← map_add (f := _), sub_add_cancel, map_one, o.act.one,
        Category.comp_id]
    rw [hg (1 - e) he1, _root_.one_mul] at key
    exact key.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.repMul_holds :
    CrtMul → CrtProj → RepMul := by
  intro hM hP p _ D R _ b N S s o 𝔞 𝔟 hab h₁ h₂
  obtain ⟨Y₁, π₁, lu₁, hf₁, he₁, hl₁, hu₁⟩ := h₁
  obtain ⟨Y₂, π₂, lu₂, hf₂, he₂, hl₂, hu₂⟩ := h₂
  haveI := hf₁
  haveI := hf₂
  haveI := he₁
  haveI := he₂
  obtain ⟨ea, hea, eb, heb, hsum⟩ :=
    Submodule.mem_sup.1 (show (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟 by rw [hab]; exact Submodule.mem_top)
  have kill : ∀ {𝔠 : Ideal (𝓞 D.F)} {T : Over S} {l : D.La → (T ⟶ o.A)}, IsEtLevOver o 𝔠 1 l →
      ∀ e ∈ 𝔠, ∀ y, l (algebraMap (𝓞 D.F) D.O e • y) = 1 := fun h e he y =>
    h.2.2.1 _ (Submodule.subset_span ⟨e, by simpa using he, y, rfl⟩)
  have dec : ∀ y : D.La, algebraMap (𝓞 D.F) D.O ea • y + algebraMap (𝓞 D.F) D.O eb • y = y := by
    intro y
    rw [← add_smul, ← map_add (f := _), hsum, map_one, one_smul]
  have r₁ : ∀ y, lu₁ (algebraMap (𝓞 D.F) D.O eb • y) = lu₁ y := by
    intro y
    conv_rhs => rw [← dec y, hl₁.1, kill hl₁ ea hea, _root_.one_mul]
  have r₂ : ∀ y, lu₂ (algebraMap (𝓞 D.F) D.O ea • y) = lu₂ y := by
    intro y
    conv_rhs => rw [← dec y, hl₂.1, kill hl₂ eb heb, _root_.mul_one]
  let π : pullback π₁ π₂ ⟶ S := pullback.fst π₁ π₂ ≫ π₁
  let f₁ : Over.mk π ⟶ Over.mk π₁ := Over.homMk (pullback.fst π₁ π₂) rfl
  let f₂ : Over.mk π ⟶ Over.mk π₂ := Over.homMk (pullback.snd π₁ π₂) pullback.condition.symm
  refine ⟨pullback π₁ π₂, π, fun y => (f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y), inferInstance, inferInstance, ?_, ?_⟩
  · exact hM p D R b N S s o 𝔞 𝔟 hab _ _ _ (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 1 _ _ lu₁ f₁ hl₁)
      (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔟 1 _ _ lu₂ f₂ hl₂)
  · intro T l hl
    have hA := hP p D R b N S s o 𝔞 𝔟 eb heb (by rw [← hsum, add_sub_cancel_right]; exact hea) T l hl
    have hB := hP p D R b N S s o 𝔟 𝔞 ea hea (by rw [← hsum, add_sub_cancel_left]; exact heb) T l
      (by rwa [_root_.mul_comm])
    obtain ⟨g₁, hg₁, hv₁⟩ := hu₁ T _ hA
    obtain ⟨g₂, hg₂, hv₂⟩ := hu₂ T _ hB
    have hg₁' : ∀ y, g₁ ≫ lu₁ y = l (algebraMap (𝓞 D.F) D.O eb • y) := hg₁
    have hg₂' : ∀ y, g₂ ≫ lu₂ y = l (algebraMap (𝓞 D.F) D.O ea • y) := hg₂
    have hw : g₁.left ≫ π₁ = g₂.left ≫ π₂ := (Over.w g₁).trans (Over.w g₂).symm
    let f : T ⟶ Over.mk π := Over.homMk (pullback.lift g₁.left g₂.left hw) (by
      show pullback.lift g₁.left g₂.left hw ≫ pullback.fst π₁ π₂ ≫ π₁ = T.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w g₁)
    have c₁ : f ≫ f₁ = g₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ hw)
    have c₂ : f ≫ f₂ = g₂ := Over.OverMorphism.ext (pullback.lift_snd _ _ hw)
    refine ⟨f, ?_, ?_⟩
    · intro y
      show f ≫ ((f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y)) = l y
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, c₁, c₂, hg₁', hg₂', ← hl.1,
        add_comm, dec]
    · intro f' hf'
      have hf'' : ∀ y, f' ≫ ((f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y)) = l y := hf'
      have a₁ : f' ≫ f₁ = g₁ := hv₁ _ (fun y => by
        have := hf'' (algebraMap (𝓞 D.F) D.O eb • y)
        rw [kill hl₂ eb heb, r₁, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, _root_.mul_one,
          ← Category.assoc] at this
        exact this)
      have a₂ : f' ≫ f₂ = g₂ := hv₂ _ (fun y => by
        have := hf'' (algebraMap (𝓞 D.F) D.O ea • y)
        rw [kill hl₁ ea hea, r₂, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, _root_.one_mul,
          ← Category.assoc] at this
        exact this)
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
      · have := congrArg (fun u => u.left) (a₁.trans c₁.symm)
        simpa [f₁] using this
      · have := congrArg (fun u => u.left) (a₂.trans c₂.symm)
        simpa [f₂] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PGrpFin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem quot_finite {p : ℕ} [Fact p.Prime] (D : Datum p) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) (h𝔞 : 𝔞 ≠ ⊥) :
    Finite (D.La ⧸ wSub D 𝔞 r) := by
  have hr : 𝔞 ^ r ≠ ⊥ := pow_ne_zero r h𝔞
  have hN0 : Ideal.absNorm (𝔞 ^ r) ≠ 0 := fun h => hr (Ideal.absNorm_eq_zero_iff.mp h)
  have hNmem : ((Ideal.absNorm (𝔞 ^ r) : ℕ) : 𝓞 D.F) ∈ 𝔞 ^ r := Ideal.absNorm_mem _
  haveI hLa : AddGroup.FG D.La := Module.Finite.iff_addGroup_fg.mp D.finLa
  haveI : AddGroup.FG (D.La ⧸ wSub D 𝔞 r) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ (wSub D 𝔞 r)).toAddMonoidHom)
      (Submodule.mkQ_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (wSub D 𝔞 r) x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Ideal.absNorm (𝔞 ^ r), Nat.pos_of_ne_zero hN0, ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  refine ⟨((Ideal.absNorm (𝔞 ^ r) : ℕ) : 𝓞 D.F), hNmem, z, ?_⟩
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

theorem UpperTheory.Gal.FiniteEtaleModels.grpFin_holds :
    GrpFin := by
  intro p _ D 𝔞 r h𝔞
  haveI hQ : Finite (D.La ⧸ wSub D 𝔞 r) := quot_finite D 𝔞 r h𝔞
  refine ⟨hQ, ?_⟩
  exact Finite.of_injective
    (fun e : (D.La ⧸ wSub D 𝔞 r) ≃ₗ[D.O] D.La ⧸ wSub D 𝔞 r => (e : D.La ⧸ wSub D 𝔞 r → D.La ⧸ wSub D 𝔞 r))
    (fun a b h => LinearEquiv.ext (congrFun h))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PIdealInd
namespace UpperTheory.Gal.FiniteEtaleModels

theorem idealInd_holds : IdealInd := by
  intro A _ _ Q P htop hpow hmul 𝔞
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact fun h => absurd rfl h
  | h1 hx =>
    rename_i x
    intro _ _
    rw [Ideal.isUnit_iff.1 hx]
    exact htop
  | hpr i hp =>
    rename_i w
    intro _ hQ
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]
      exact htop
    · have hmax : w.IsMaximal :=
        (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
      exact hpow w i hmax (hQ w hmax (Ideal.pow_le_self hi.ne'))
  | hcp hxy hx hy =>
    rename_i x y
    intro hne hQ
    have hx0 : x ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.bot_mul y)
    have hy0 : y ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.mul_bot x)
    have hsup : x ⊔ y = ⊤ :=
      Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))
    exact hmul x y hsup
      (hx hx0 fun w hw hle => hQ w hw (Ideal.mul_le_left.trans hle))
      (hy hy0 fun w hw hle => hQ w hw (Ideal.mul_le_right.trans hle))

end UpperTheory.Gal.FiniteEtaleModels
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovMain
namespace UpperTheory.Gal.Int.Geo.CovMain

set_option linter.unusedVariables false

theorem splitQ_of (I : MIn) : SplitQ := UpperTheory.rational_splitting_exists

theorem baseEx_of (I : MIn) : BaseEx := UpperTheory.baseExtension_holds

theorem powProj_of (I : MIn) : PowProj := UpperTheory.power_projector_exists

theorem siteEx_of (I : MIn) : SiteEx := UpperTheory.site_exists_of_splitting_and_power_projector I (splitQ_of I) (baseEx_of I) (powProj_of I)

theorem genEx_of (I : MIn) : GenEx := UpperTheory.exists_generic_moduli_point

theorem numEx_of (I : MIn) : NumEx := UpperTheory.exists_number_field_point_of_generic (genEx_of I)

theorem latGen_of (I : MIn) : LatGen := UpperTheory.lattice_generation

theorem gPull_of (I : MIn) : GPull := UpperTheory.group_scheme_pullback_exists

theorem powCart_of (I : MIn) : PowCart := UpperTheory.power_map_cartesian

theorem qObj_of (I : MIn) : QObj := UpperTheory.quotient_moduli_object_exists

theorem qComp_of (I : MIn) : QComp := UpperTheory.quotient_map_comp

theorem qUniq_of (I : MIn) : QUniq := UpperTheory.quotient_unique_of_comp (qComp_of I)

theorem qIso_of (I : MIn) : QIso := UpperTheory.quotient_moduli_iso

theorem qLev_of (I : MIn) : QLev := UpperTheory.quotient_level_of_lattice_generation (latGen_of I)

theorem clsEx_of (I : MIn) : ClsEx := UpperTheory.isogeny_class_exists_of_quotient (qObj_of I) (qComp_of I) (qUniq_of I) (qLev_of I)

theorem trEta_of (I : MIn) : TrEta := UpperTheory.trace_eta_identity

theorem trEtaPt_of (I : MIn) : TrEtaPt := UpperTheory.trace_eta_pointwise

theorem multUnit_of (I : MIn) : MultUnit := UpperTheory.multiplier_is_unit

theorem trBack_of (I : MIn) : TrBack := UpperTheory.trace_pullback_identity

theorem trUnit_of (I : MIn) : TrUnit := UpperTheory.trace_unit_of_pullback_multiplier (trBack_of I) (multUnit_of I)

theorem trTj_of (I : MIn) : TrTj := UpperTheory.trace_identity_of_tjElement

theorem congCRT_of (I : MIn) : CongCRT := UpperTheory.congruenceCRT_of_latticeGen (latGen_of I)

theorem grpLat_of (I : MIn) : GrpLat := UpperTheory.congruenceSubgroup_isLattice_statement

theorem grpCong_of (I : MIn) : GrpCong := UpperTheory.arithmeticGroup_congruenceSubgroupProperty

theorem baseInv_of (I : MIn) : BaseInv := UpperTheory.quotient_invariant_of_trace_unit_crt (numEx_of I) (qComp_of I) (qIso_of I) (clsEx_of I) (trEta_of I) (trUnit_of I) (congCRT_of I)

theorem piInv_of (I : MIn) : PiInv := UpperTheory.tower_invariant_of_base_invariant_powerCartesian (baseInv_of I) (powCart_of I)

theorem baseSep_of (I : MIn) : BaseSep := UpperTheory.quotient_separated_of_trace_unit_crt (gPull_of I) (qComp_of I) (qIso_of I) (qUniq_of I) (trEta_of I) (trEtaPt_of I) (trUnit_of I) (congCRT_of I)

theorem piZero_of (I : MIn) : PiZero := UpperTheory.tower_trivial_of_quotient_trace_powerCartesian I (qObj_of I) (qComp_of I) (qIso_of I) (qUniq_of I) (trEta_of I) (trUnit_of I) (powCart_of I)

theorem piFet_of (I : MIn) : PiFet := UpperTheory.tower_finiteEtale_of_trivial_powerCartesian (piZero_of I) (powCart_of I)

theorem piSep_of (I : MIn) : PiSep := UpperTheory.tower_separated_of_trivial_powerCartesian (piZero_of I) (baseSep_of I) (powCart_of I)

theorem splitOf_of (I : MIn) : SplitOf := UpperTheory.integralGeometricGalois_splitting

theorem kSCover_of (I : MIn) : KSCover := UpperTheory.tower_covering_of_invariant_finiteEtale_separated (piInv_of I) (piFet_of I) (piSep_of I) (splitOf_of I)

theorem tjIsog_of (I : MIn) : TjIsog := UpperTheory.heckeCorrespondence_isogeny_of_trace_crt (trEta_of I) (trBack_of I) (trTj_of I) (multUnit_of I) (congCRT_of I)

theorem liftEx_of (I : MIn) : LiftEx := UpperTheory.hecke_lift_exists_of_quotient_level (numEx_of I) (qObj_of I) (qComp_of I) (qUniq_of I) (qLev_of I) (tjIsog_of I) (trEta_of I) (congCRT_of I)

theorem liftSep_of (I : MIn) : LiftSep := UpperTheory.hecke_lift_separated_of_lattice_congruence (numEx_of I) (baseInv_of I) (trEta_of I) (trEtaPt_of I) (congCRT_of I) (grpLat_of I) (grpCong_of I)

theorem count_of (I : MIn) : Count := UpperTheory.tower_point_count_statement

theorem tjLies_of (I : MIn) : TjLies := UpperTheory.heckeCorrespondence_lies_in_tower_of_lift_count I (numEx_of I) (clsEx_of I) (powCart_of I) (piInv_of I) (piFet_of I) (liftEx_of I) (liftSep_of I) (count_of I)

theorem stdEx_of (I : MIn) : StdEx := UpperTheory.standard_datum_exists

theorem kSCong_of (I : MIn) : KSCong := UpperTheory.tower_covering_congruence_of_hecke_lies I (siteEx_of I) (numEx_of I) (clsEx_of I) (kSCover_of I) (tjLies_of I)

end UpperTheory.Gal.Int.Geo.CovMain
end

namespace UpperTheory.Gal.Int.Geo.CovMain

open UpperTheory.Gal.FiniteEtaleModels in
theorem mIn : MIn :=
  { ex := @GlobalTheory.T.harrisTaylorIntegralModel_nonempty,
    proj := @GlobalTheory.UPel.HT.Model.isProjOver_of_compactB,
    cmp := @GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre,
    finModel := finModel_holds (finCover_holds
      (repAll_holds idealInd_holds (repMul_holds crtMul_holds crtProj_holds))
      (ptAll_holds idealInd_holds crtMul_holds) grpFin_holds),
    placeOf := placeOf_holds,
    cong := crystallineComparison.Mod.congKS_link,
    corr := crystallineComparison.Mod.corrBC_holds crystallineComparison.Mod.quotObj_link }

theorem ksCong_holds : KSCong := kSCong_of mIn
theorem stdEx_holds : StdEx := stdEx_of mIn
theorem ksCover_holds : KSCover := kSCover_of mIn

end UpperTheory.Gal.Int.Geo.CovMain
