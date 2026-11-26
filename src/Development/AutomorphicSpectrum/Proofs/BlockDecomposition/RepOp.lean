module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepOp
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem repOp : CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp := by
  intro _ hConc hBasic hOp S R _ _ I J ρ X n x a hRep
  obtain ⟨α, hα, hmk⟩ := (hConc S I X n a).2.1 x hRep
  have hcl : Sec.map (J.d n (n + 1)) (ρ.app X n a) = 0 := by
    rw [ρ.comm X n (n + 1) a, (hBasic S I X n).2.1 x a hRep (n + 1), map_zero]
  obtain ⟨β, hβ⟩ := (hConc R J X n (ρ.app X n a)).1 hcl
  have himg : ρ.IsImage α.1 β.1 := by
    intro p s h U y
    cases p with
    | zero =>
      have hs : n = s := by omega
      subst hs
      rw [hβ.1 U y, hα.1 U y]
      exact ρ.nat y n a
    | succ p =>
      rw [hβ.2 p s h U y, hα.2 p s h U y, map_zero]
  refine ⟨β, ?_, ?_⟩
  · rw [← hOp S R I J ρ (sch.obj X) n α β himg, hmk]
  · rw [hβ.1 X (𝟙 X)]
    change ((J.X n).obj.map (𝟙 (op X))).hom (ρ.app X n a) = ρ.app X n a
    rw [CategoryTheory.Functor.map_id]
    rfl

end GlobalTheory.CompanionTheory.EdgeRep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassCompatibleSystem
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ChernSys

theorem inv_cech (hpt : CrystallineSemistableComparison.E.CechPt) (l : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (hl : IsUnit (l : Γ(X, ⊤))) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (cech f) := by
  rintro U ⟨z⟩
  obtain ⟨x, y, h, -⟩ := (hpt Y X f 0 U).1 z
  have h1 : IsUnit (l : Γ(U, ⊤)) := by
    have := hl.map x.appTop.hom
    rwa [map_natCast] at this
  rw [Nat.cast_pow]
  exact h1.pow n

theorem chern_class_compatible_system (hpt : CrystallineSemistableComparison.E.CechPt) : CrystallineSemistableComparison.E.FirstChernCompatibleSystem := by
  intro a2 a11 l _ Y X f _ _ hl L
  have hinv := inv_cech hpt l f hl
  have hne : ∀ n, NeZero (l ^ n) := fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨hinv, ?_⟩
  have hb : ∀ n, Function.Bijective (pull (ZMod (l ^ n)) (GlobalTheory.EtC.cechAug f) (tw (l ^ n) 1) 2) :=
    fun n => a2 (ZMod (l ^ n)) f (tw (l ^ n) 1) 2
  choose x hx using fun n => (hb n).2 (c1 (l ^ n) L)
  refine ⟨⟨x, fun k => ?_⟩, hx⟩
  apply (hb k).1
  have e := ((a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) (cech f)).2.1 (hinv (k + 1))).2 L
  have e2 := pull_red (l ^ (k + 1)) (l ^ k) (GlobalTheory.EtC.cechAug f) 2 1 (x (k + 1))
  exact e2.trans ((congrArg _ (hx (k + 1))).trans (e.trans (hx k).symm))

end GlobalTheory.CompanionTheory.ChernSys
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResSplit
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ResSplitProof

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun k => ModuleCat.Hom.hom k x) h

theorem resSplit : CrystallineSemistableComparison.E.ResLoc → CrystallineSemistableComparison.E.LocSplit → CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.ResSplit := by
  intro hRL hLS hLC R _ F U hU s x
  constructor
  · intro hx
    obtain ⟨ι, f, hf⟩ := hLS U hU _ (hRL R F s U x hx)
    obtain ⟨W, j, hj, -, -, hglue⟩ := hLC U ι f
    have hP : ∀ a, ∃ y, Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y = Sec.res (j a) x :=
      fun a => hf (W a) (j a) a (hj a)
    choose y hy using hP
    obtain ⟨z, hz, -⟩ := hglue R _ y
    obtain ⟨w, -, huniq⟩ := hglue R _ (fun a => Sec.res (j a) x)
    refine ⟨z, ?_⟩
    have h1 := huniq (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) z)
      (fun a => by rw [← map_res, hz a, hy a])
    have h2 := huniq x (fun a => rfl)
    exact h1.trans h2.symm
  · rintro ⟨y, rfl⟩
    have h := (GlobalTheory.EtC.res R F).d_comp_d (↑s) (↑(s + 1)) (↑(s + 1 + 1))
    calc Sec.map ((GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1)))
          (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y)
        = Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1)) ≫ (GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1))) y := rfl
      _ = Sec.map 0 y := by rw [h]
      _ = 0 := by first | rfl | simp [Sec.map]

end GlobalTheory.CompanionTheory.ResSplitProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecMapRes
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRes

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom y) h

theorem resGood : CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapBij → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.ResSplit → CrystallineSemistableComparison.E.ResGood := by
  intro hS hB hZ hX hgen q _ C _ P i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c c' φ x
    have h1 := (hS q i (P.U c) (P.ζ c) x).2.2 (P.U c') (P.S.map φ).unop
    rw [P.ζ_nat φ] at h1
    have h2 := sec_map_res (resι _ (tw q i)) (P.S.map φ).unop (kap i (P.ζ c) x)
    rw [h1] at h2
    exact h2
  · intro s c c' φ x
    exact sec_map_res ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (P.S.map φ).unop x
  · intro c a b h
    exact (hB hgen q i (P.U c) (P.ζ c)).1 ((hZ _ (tw q i) (P.U c)).1 h)
  · intro c y
    have h := (hZ _ (tw q i) (P.U c)).2.1 y
    constructor
    · intro h0
      obtain ⟨t, ht⟩ := h.1 h0
      obtain ⟨f, hf⟩ := (hB hgen q i (P.U c) (P.ζ c)).2 t
      exact ⟨f, by rw [← ht, ← hf]; rfl⟩
    · rintro ⟨f, rfl⟩
      exact h.2 ⟨_, rfl⟩
  · intro s c
    exact hX _ (tw q i) (P.U c) (P.split c) s

end GlobalTheory.CompanionTheory.EdgeRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepBasic
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtEdge

theorem repBasic : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic := by
  intro hExt hNat hIn
  unfold CrystallineSemistableComparison.E.InSch at hIn
  unfold CrystallineSemistableComparison.E.RepBasic
  intro R _ I X n
  unfold CrystallineSemistableComparison.E.Rep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩ m
    by_cases hm : n + 1 = m
    · exact ((hIn R X I (n - 1) n m (by omega) hm).2 α).1
    · rw [HomologicalComplex.shape I n m (by simpa using hm)]
      simp [GlobalTheory.EtC.Sec.map]
  · rintro x y a b ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    have hs := (hExt R (sch.obj X) I n α β).2 0 n (by simp) X (𝟙 X : X ⟶ X)
    exact ⟨⟨α + β, rfl, hs.1⟩, ⟨α - β, rfl, hs.2.1⟩⟩
  · rintro a ⟨α, h0, rfl⟩ k hk
    exact ((hIn R X I k n (n + 1) hk rfl).2 α).2.1 h0
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨GlobalTheory.EtC.zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h2 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) Y).2 (sch.obj Y) (sch.map f)
      (𝟙 Y : Y ⟶ Y)
    have h1 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) X).1 Y f (𝟙 X : X ⟶ X)
    have e : (Sx.map (sch.map f) (𝟙 Y : Y ⟶ Y) : Sx (sch.obj X) 0 Y) = Sx.res f (𝟙 X : X ⟶ X) := by
      show 𝟙 Y ≫ f = f ≫ 𝟙 X
      simp
    refine h2.trans ?_
    rw [e]
    exact h1

end GlobalTheory.CompanionTheory.EtEdge
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapNsmulTwGen
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.CstE.KapRedP

theorem up_smul_eq {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (r : ZMod q) (c : ℕ)
    (h : (c : ZMod q) = r) (m : M) : (ULift.up r : ULift.{1} (ZMod q)) • m = c • m := by
  have e : (ULift.up r : ULift.{1} (ZMod q)) = ((c : ℕ) : ULift.{1} (ZMod q)) := by
    ext; rw [ULift.down_natCast, h]
  rw [e, Nat.cast_smul_eq_nsmul]

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := congrArg (fun ψ => ψ.hom x) (φ.hom.naturality g.op)
  exact h.symm

theorem map_nsmul_twGen {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (c : ℕ) :
    Sec.map (resι _ (tw q i)) (c • twGen i ζ) = c • resGen i ζ :=
  map_nsmul _ _ _

theorem kapRed : CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapRed := by
  intro hLc _ hKap hRed Q q _ _ h i U ζ ξ hξ f
  obtain ⟨W, j, hj, -, -, hG⟩ := hLc U (ZMod Q) f
  refine (hG (ZMod q) ((GlobalTheory.EtC.res _ (tw q i)).X 0)
    (fun a => Sec.res (j a) (Sec.map (resι _ _) (kap i ξ (f.map (ZMod.castHom h (ZMod q))))))).unique
    (fun a => ?_) (fun a => rfl)
  have hξ' : (primRes (j a) ξ).1 = (primRes (j a) ζ).1 ^ (Q / q) := by
    change (j a).appTop.hom ξ.1 = ((j a).appTop.hom ζ.1) ^ (Q / q)
    rw [hξ, map_pow]
  have hL : Sec.res (j a) (kap i ζ f) = a.val • twGen i (primRes (j a) ζ) := by
    rw [(hKap Q i U ζ f).1 (W a) (j a) a (hj a)]
    exact up_smul_eq a a.val (ZMod.natCast_zmod_val a) _
  have hR : Sec.res (j a) (kap i ξ (f.map (ZMod.castHom h (ZMod q)))) = a.val • twGen i (primRes (j a) ξ) := by
    rw [(hKap q i U ξ (f.map (ZMod.castHom h (ZMod q)))).1 (W a) (j a) (ZMod.castHom h (ZMod q) a)
      (fun v => by simp [hj a v])]
    exact up_smul_eq _ a.val (by rw [ZMod.castHom_apply, ZMod.natCast_val]) _
  rw [(redMap Q q i).nat (j a) 0, res_map, res_map, hL, hR, map_nsmul_twGen, map_nsmul_twGen, map_nsmul,
    hRed Q q h i (W a) (primRes (j a) ζ) (primRes (j a) ξ) hξ']

end GlobalTheory.CompanionTheory.CstE.KapRedP
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepConcOfInputs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem repConc_of_inputs : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc := by
  intro hEv hSch hRep R _ I X n a
  have hS := hSch R X I (n - 1) n (n + 1) (by ring) rfl
  have hR := hRep R I X n
  have hconc : Sec.map (I.d n (n + 1)) a = 0 →
      ∃ α : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.IsConc α.1 a := by
    intro ha
    obtain ⟨α, h0, h1⟩ := hS.1 a ha
    refine ⟨α, ?_⟩
    unfold CrystallineSemistableComparison.E.IsConc
    exact ⟨h0, h1⟩
  have huniq : ∀ x y : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.Rep x a → CrystallineSemistableComparison.E.Rep y a → x = y := by
    intro x y hx hy
    have hxy : CrystallineSemistableComparison.E.Rep (x - y) (a - a) := (hR.2.2.1 x y a a hx hy).2
    rw [sub_self] at hxy
    obtain ⟨γ, hγ, hγa⟩ := hxy
    have h00 : CrystallineSemistableComparison.E.Rep (0 : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n) 0 := by
      have h := (hR.2.2.1 x x a a hx hx).2
      rwa [sub_self, sub_self] at h
    obtain ⟨b, hb⟩ := hR.2.2.2.1 0 h00 (n - 1) (by ring)
    have hγ0 : CochainComplex.HomComplex.CohomologyClass.mk γ = 0 := ((hS.2 γ).2).2 ⟨b, by rw [hb, hγa]⟩
    rw [← sub_eq_zero, ← hγ, hγ0]
  refine ⟨hconc, fun x hx => ?_, huniq⟩
  have hx' := hx
  obtain ⟨β, hβ, hβa⟩ := hx'
  have ha : Sec.map (I.d n (n + 1)) a = 0 := by
    have h := (hS.2 β).1
    rwa [hβa] at h
  obtain ⟨α, hα⟩ := hconc ha
  have hα' := hα
  unfold CrystallineSemistableComparison.E.IsConc at hα'
  obtain ⟨hα1, -⟩ := hα'
  have hRα : CrystallineSemistableComparison.E.Rep (CochainComplex.HomComplex.CohomologyClass.mk α) a := by
    unfold CrystallineSemistableComparison.E.Rep
    refine ⟨α, rfl, ?_⟩
    rw [hα1 X (𝟙 X)]
    simp [GlobalTheory.EtC.Sec.res]
  exact ⟨α, hα, huniq _ _ hRα hx⟩

end GlobalTheory.CompanionTheory.EdgeMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSubsingleton
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwZeroGen

theorem sec_subsingleton (hLc : LcCover) (V : Scheme.{0}) [IsEmpty V] {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton (Sec G V) := by
  let f : LocallyConstant V Empty :=
    ⟨isEmptyElim, fun s => by rw [Set.eq_empty_of_isEmpty (isEmptyElim ⁻¹' s)]; exact isOpen_empty⟩
  obtain ⟨W, j, -, -, -, hG⟩ := hLc V Empty f
  constructor
  intro a b
  exact (hG R G (fun e => e.elim)).unique (fun e => e.elim) (fun e => e.elim)

private theorem twGen_zero_eq_of_eq_pow {q : ℕ} {V : Scheme.{0}} (η θ : Prim q ↑(V.presheaf.obj (op ⊤)))
    (b : (ZMod q)ˣ) (h : η.1 = θ.1 ^ (b : ZMod q).val) : twGen 0 η = twGen 0 θ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨θ, η, b, h, ?_⟩)
  rw [zpow_zero]
  rfl

theorem twZero : RootPow → LcCover → RepRoot → TwZero := by
  intro hR hL hP hIn q _ U ζ ξ
  obtain ⟨f, hf, hu⟩ := (hR q U ζ).2 ξ
  obtain ⟨W, j, hWf, -, -, hG⟩ := hL U (ZMod q) f
  have key : ∀ a, Sec.res (j a) (twGen 0 ζ) = Sec.res (j a) (twGen 0 ξ) := by
    intro a
    rw [((hP q 0 U ζ).1 (W a) (j a)).1, ((hP q 0 U ξ).1 (W a) (j a)).1]
    by_cases ha : IsUnit a
    · symm
      apply twGen_zero_eq_of_eq_pow _ _ ha.unit
      have hpw := hf (W a) (j a) a (hWf a)
      have e : (primRes (j a) ξ).1 = (CommRingCat.Hom.hom (Scheme.Hom.appTop (j a))) ξ.1 := rfl
      rw [IsUnit.unit_spec, e]
      exact hpw
    · haveI : IsEmpty (W a) := ⟨fun v => by
        have hv := hu (j a v)
        rw [hWf a v] at hv
        exact ha hv⟩
      exact (sec_subsingleton hL (W a) (tw q 0)).elim _ _
  obtain ⟨y, -, hy⟩ := hG (ZMod q) (tw q 0) (fun a => Sec.res (j a) (twGen 0 ζ))
  exact (hy _ (fun a => rfl)).trans (hy _ (fun a => (key a).symm)).symm

end GlobalTheory.CompanionTheory.TwZeroGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapOneEqTwGen
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRoot

theorem kap_one_eq_twGen (hRep : CrystallineSemistableComparison.E.RepRoot) (hKap : CrystallineSemistableComparison.E.KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : kap i ζ 1 = twGen i ζ := by
  refine ((hKap q i U ζ 1).2.1 (twGen i ζ) ?_).symm
  intro V g a h
  rw [((hRep q i U ζ).1 V g).1]
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    have ha : (1 : ZMod q) = a := h v
    subst ha
    exact (one_smul _ _).symm
  · have hV' : IsEmpty V := not_nonempty_iff.1 hV
    have h0 := (hKap q i U ζ 1).1 V g 0 (fun v => hV'.elim v)
    have h1 := (hKap q i U ζ 1).1 V g 1 (fun v => hV'.elim v)
    have hz : twGen i (primRes g ζ) = 0 := by
      have e : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) =
          (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) := h1.symm.trans h0
      have e1 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = twGen i (primRes g ζ) :=
        one_smul _ _
      have e0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = 0 := zero_smul _ _
      rw [e1, e0] at e
      exact e
    rw [hz, smul_zero]

theorem d_one_eq_zero {C : Type 1} [Category.{0} C] {R : Type} [CommRing R] (A : C ⥤ CommAlgCat.{0} R) :
    d (modF A) 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem etRoot_of_spec : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.EtRoot := by
  intro hEt hRep hKap hGen q _ C _ P X Y ζ hζ i
  refine ((hEt hGen q C P X Y i 0 (rootClass i ζ)).2 _ ?_).symm
  refine ⟨resGen i ζ, (hRep q i X ζ).2, ?_⟩
  refine ⟨fun s => (1 : (lcF P.S q).obj (s.obj (Fin.last 0))), d_one_eq_zero (lcF P.S q), ?_, rfl⟩
  refine ⟨rfl, ?_⟩
  funext s
  change Sec.map (resι _ (tw q i)) (kap i (P.ζ (s.obj (Fin.last 0))) 1) = Sec.res (Y.y (s.obj (Fin.last 0))) (resGen i ζ)
  rw [kap_one_eq_twGen hRep hKap, ((hRep q i X ζ).1 _ _).2, hζ]
  rfl

end GlobalTheory.CompanionTheory.EdgeRoot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCol
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

theorem stCol : CrystallineSemistableComparison.E.StCol := by
  intro R _ C _ F T hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k z
    funext s
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K 0).map (GlobalTheory.CatH.toLast i s)).hom (T.ι _ (z (GlobalTheory.CatH.face i s))) =
      T.ι _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        (F.map (GlobalTheory.CatH.toLast i s)).hom (z (GlobalTheory.CatH.face i s)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.ι_nat]
  · intro s k a
    funext t
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K (s + 1)).map (GlobalTheory.CatH.toLast i t)).hom (T.dv s _ (a (GlobalTheory.CatH.face i t))) =
      T.dv s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K s).map (GlobalTheory.CatH.toLast i t)).hom (a (GlobalTheory.CatH.face i t)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.dv_nat]
  · intro k x y h
    funext s
    exact hG.inj _ (congrFun h s)
  · intro k x
    constructor
    · intro h
      have hz : ∀ s, ∃ z, T.ι _ z = x s := fun s => (hG.ex0 _ (x s)).1 (congrFun h s)
      choose z hz using hz
      exact ⟨z, funext hz⟩
    · rintro ⟨z, rfl⟩
      funext s
      exact (hG.ex0 _ _).2 ⟨_, rfl⟩
  · intro s k x
    constructor
    · intro h
      have hz : ∀ t, ∃ a, T.dv s _ a = x t := fun t => (hG.ex s _ (x t)).1 (congrFun h t)
      choose a ha using hz
      exact ⟨a, funext ha⟩
    · rintro ⟨a, rfl⟩
      funext t
      exact (hG.ex s _ _).2 ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.EdgeStair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsKumPow
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KumPowProof

theorem isKum_pow {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v : (Γ(U, ⊤))ˣ) (k : ℕ) :
    ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ k * v → t U w = t U v + k • resGen 1 ζ := by
  induction k with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw, zero_smul, add_zero]
  | succ k ih =>
    intro w hw
    have hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v) := by rw [hw]; ring
    obtain ⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v) := isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)
    rw [ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]

theorem res_smap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun m => m.hom x) h).symm

theorem kumPow : LcCover → RepRoot → KapSpec → PrimAlg → KumPow := by
  intro hL _ hK _ hKum q _ U ζ f r v hr
  have ht : IsKum q (kumT q) := hKum q
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  obtain ⟨W, j, hf, -, -, hG⟩ := hL U (ZMod q) f
  obtain ⟨y, -, huniq⟩ := hG (ZMod q) ((res _ (tw q 1)).X 0) (fun a => Sec.res (j a) (kumT q U (r * v)))
  refine (huniq _ fun a => rfl).trans (huniq _ fun a => ?_).symm
  have hra : (j a).appTop.hom r.val = (primRes (j a) ζ).1 ^ a.val := hr (W a) (j a) a (hf a)
  have hlc : Sec.res (j a) (kap 1 ζ f) = (ULift.up a : ULift.{1} (ZMod q)) • twGen 1 (primRes (j a) ζ) :=
    (hK q 1 U ζ f).1 (W a) (j a) a (hf a)
  have hup : (ULift.up a : ULift.{1} (ZMod q)) = a.val • (1 : ULift.{1} (ZMod q)) :=
    ULift.ext (by change a = a.val • (1 : ZMod q); simp)
  have hsm : Sec.res (j a) (kap 1 ζ f) = a.val • twGen 1 (primRes (j a) ζ) := by
    rw [hlc, hup, smul_assoc, one_smul]
  have hkey := isKum_pow ht (primRes (j a) ζ) (Units.map (j a).appTop.hom.toMonoidHom v) a.val
    (Units.map (j a).appTop.hom.toMonoidHom (r * v)) (by
      change (j a).appTop.hom (r.val * v.val) = _ * (j a).appTop.hom v.val
      rw [map_mul, hra])
  have e1 : Sec.res (j a) (kumT q U (r * v)) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom (r * v)) :=
    ht.1 _ _ (j a) _ hq
  have e2 : Sec.res (j a) (kumT q U v) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom v) :=
    ht.1 _ _ (j a) _ hq
  have e3 : Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = a.val • resGen 1 (primRes (j a) ζ) := by
    rw [res_smap, hsm]
    exact map_nsmul _ _ _
  have e0 : Sec.res (j a) (kumT q U v + Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) =
      Sec.res (j a) (kumT q U v) + Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) := map_add _ _ _
  rw [e0, e1, e2, e3, hkey]

end GlobalTheory.CompanionTheory.KumPowProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocSplit
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LocSplitProof

theorem locSplit : CrystallineSemistableComparison.E.LocSplit := by
  intro U hU P hP
  obtain ⟨S, hS, hSP⟩ := hP
  rw [Scheme.etaleTopology, Scheme.mem_grothendieckTopology_iff] at hS
  obtain ⟨𝒰, h𝒰⟩ := hS
  have hsurj : Surjective (Limits.Sigma.desc 𝒰.f) := by
    constructor
    intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    refine ⟨(Limits.Sigma.ι 𝒰.X i) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc, hy]
  have het : Etale (Limits.Sigma.desc 𝒰.f) := by
    have := 𝒰.sigma.map_prop ⟨⟩
    simpa [Scheme.Cover.sigma_f] using this
  obtain ⟨s, hs⟩ := hU _ (Limits.Sigma.desc 𝒰.f) het hsurj
  have hlc : IsLocallyConstant (fun u : U => ((sigmaMk 𝒰.X).symm (s u)).1) := by
    intro t
    have hfst : IsOpen (Sigma.fst ⁻¹' t : Set (Σ i, 𝒰.X i)) := by
      rw [isOpen_sigma_iff]
      intro i
      by_cases hi : i ∈ t
      · convert isOpen_univ
        ext
        simp [hi]
      · convert isOpen_empty
        ext
        simp [hi]
    exact hfst.preimage ((sigmaMk 𝒰.X).symm.continuous.comp s.continuous)
  refine ⟨𝒰.I₀, ⟨fun u => ((sigmaMk 𝒰.X).symm (s u)).1, hlc⟩, ?_⟩
  intro V g a hg
  have hrange : Set.range (g ≫ s) ⊆ Set.range (Limits.Sigma.ι 𝒰.X a) := by
    rintro _ ⟨v, rfl⟩
    have h1 : ((sigmaMk 𝒰.X).symm (s (g v))).1 = a := hg v
    rcases hq : (sigmaMk 𝒰.X).symm (s (g v)) with ⟨i, y⟩
    rw [hq] at h1
    subst h1
    refine ⟨y, ?_⟩
    have h2 : sigmaMk 𝒰.X ⟨i, y⟩ = s (g v) := by rw [← hq]; simp
    rw [sigmaMk_mk] at h2
    rw [h2, Scheme.Hom.comp_apply]
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Limits.Sigma.ι 𝒰.X a = g ≫ s :=
    ⟨_, IsOpenImmersion.lift_fac (Limits.Sigma.ι 𝒰.X a) (g ≫ s) hrange⟩
  have hgl : g = l ≫ 𝒰.f a := by
    have h3 : l ≫ 𝒰.f a = l ≫ Limits.Sigma.ι 𝒰.X a ≫ Limits.Sigma.desc 𝒰.f := by simp
    rw [h3, ← Category.assoc, hl, Category.assoc, hs, Category.comp_id]
  rw [hgl]
  exact hSP V _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk a)) l)

end GlobalTheory.CompanionTheory.LocSplitProof
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCZsmul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMapPull

universe w w' w₁ w₁' u v u' v'

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w'} R} {F' : C' ⥤ ModuleCat.{w₁'} R'}
  {T : Res.{w} F} {T' : Res.{w₁} F'} {m : Mor F F' σ}

theorem d_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    d (T'.K s) k (n.pullC s k x) = n.pullC s (k + 1) (d (T.K s) k x) := by
  funext t
  change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T'.K s).map (GlobalTheory.CatH.toLast i t)).hom
      (n.τ s _ (x (GlobalTheory.CatH.face i t ⋙ m.G))) =
    n.τ s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((T.K s).map (m.G.map (GlobalTheory.CatH.toLast i t))).hom (x (GlobalTheory.CatH.face i t ⋙ m.G)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, n.nat]

theorem dvC_pullC (n : ResMor T T' m) (s k : ℕ) (x : Cn (T.K s) k) :
    T'.dvC s k (n.pullC s k x) = n.pullC (s + 1) k (T.dvC s k x) :=
  funext fun t => (n.dv s _ (x (t ⋙ m.G))).symm

theorem ιC_pullC (n : ResMor T T' m) (k : ℕ) (z : Cn F k) :
    T'.ιC k (m.pullC k z) = n.pullC 0 k (T.ιC k z) :=
  funext fun t => (n.ι _ (z (t ⋙ m.G))).symm

theorem pullC_zsmul (n : ResMor T T' m) (s k : ℕ) (c : ℤ) (x : Cn (T.K s) k) :
    n.pullC s k (c • x) = c • n.pullC s k x :=
  funext fun t => map_zsmul (n.τ s _) c (x (t ⋙ m.G))

theorem st_pullC (n : ResMor T T' m) {j : ℕ} (z : Cn F j) :
    ∀ (s k : ℕ) (x : Cn (T.K s) k), T.St z s k x → T'.St (m.pullC j z) s k (n.pullC s k x) := by
  intro s
  induction s with
  | zero =>
    intro k x h
    simp only [Res.St] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, ιC_pullC n j z⟩
  | succ s ih =>
    intro k x h
    simp only [Res.St] at h ⊢
    obtain ⟨a, rfl, ha⟩ := h
    refine ⟨n.pullC s k a, dvC_pullC n s k a, ?_⟩
    have := ih (k + 1) _ ha
    rwa [pullC_zsmul, ← d_pullC] at this

end GlobalTheory.CompanionTheory.EdgeMapPull


open GlobalTheory.CompanionTheory.EdgeMapPull in
theorem GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap : CrystallineSemistableComparison.E.EdgeMap := by
  intro R R' _ _ σ C C' _ _ F F' T T' m n j x h hE
  obtain ⟨z, hz, hS, rfl⟩ := hE
  exact ⟨m.pullC j z, by rw [m.d_pullC, hz, map_zero], st_pullC n z j 0 x hS, rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignCancel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.Staircase

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem term_ιC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) {p n : ℕ}
    (s : ComposableArrows C n) (z : Cn F p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K 0) s (T.ιC p z) g hg = T.ι _ (term F s z g hg) :=
  (hT.ι_nat _ _).symm

theorem term_dvC {F : C ⥤ ModuleCat.{0} R} (T : Res.{1} F) (hT : T.Good) (t : ℕ) {p n : ℕ}
    (s : ComposableArrows C n) (a : Cn (T.K t) p) (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (T.K (t + 1)) s (T.dvC t p a) g hg = T.dv t _ (term (T.K t) s a g hg) :=
  (hT.dv_nat t _ _).symm

theorem sign_cancel {i k r : ℕ} (h : i + k = r) : (-1 : ℤ) ^ r * (-1 : ℤ) ^ i = (-1 : ℤ) ^ k := by
  subst h
  rw [pow_add, mul_comm ((-1 : ℤ) ^ i), mul_assoc, ← mul_pow]
  simp

theorem stCupB : CupLeib.{1} → StCol → StCupB := by
  intro hL hC R _ C _ F₁ F₂ F₃ T₁ T₂ T₃ P μ g₁ g₂ i j n hn z z' hz t
  induction t with
  | zero =>
    intro k r h y hy
    obtain ⟨rfl, rfl⟩ := hy
    subst h
    subst hn
    refine ⟨rfl, ?_⟩
    funext s
    change T₃.ι _ (P.μ _ (term F₁ s z _ _) (term F₂ s z' _ _)) =
      (μ.μ 0 0 0 (zero_add 0)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K 0) s (T₂.ιC _ z') _ _)
    rw [term_ιC T₁ g₁, term_ιC T₂ g₂]
    exact (μ.ι _ _ _).symm
  | succ t ih =>
    intro k r h y hy
    obtain ⟨a, rfl, ha⟩ := hy
    have hd : d (T₁.K 0) i (T₁.ιC i z) = 0 := by
      rw [(hC R C F₁ T₁ g₁).1, hz, map_zero]
    refine ⟨(μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a, ?_, ?_⟩
    · funext s
      change T₃.dv t _ ((μ.μ 0 t t (zero_add t)).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _) (term (T₂.K t) s a _ _)) =
        (μ.μ 0 (t + 1) (t + 1) (zero_add (t + 1))).μ _ (term (T₁.K 0) s (T₁.ιC i z) _ _)
          (term (T₂.K (t + 1)) s (T₂.dvC t k a) _ _)
      rw [μ.leib 0 t t (zero_add t), term_dvC T₂ g₂, term_ιC T₁ g₁,
        (g₁.ex0 _ _).mpr ⟨_, rfl⟩, map_zero, LinearMap.zero_apply, zero_add, pow_zero, one_smul]
    · have e := hL R C (T₁.K 0) (T₂.K t) (T₃.K t) (μ.μ 0 t t (zero_add t)) i k r h (T₁.ιC i z) a
      have key := ih (k + 1) (r + 1) (by omega) ((-1 : ℤ) ^ k • d (T₂.K t) k a) ha
      have e' : (-1 : ℤ) ^ r • d (T₃.K t) r ((μ.μ 0 t t (zero_add t)).cupC h (T₁.ιC i z) a) =
          (μ.μ 0 t t (zero_add t)).cupC (show i + (k + 1) = r + 1 by omega) (T₁.ιC i z)
            ((-1 : ℤ) ^ k • d (T₂.K t) k a) := by
        rw [e, hd, map_zero, LinearMap.zero_apply, zero_add, smul_smul, sign_cancel h, map_zsmul]
      rw [e']
      exact key

end GlobalTheory.CompanionTheory.Staircase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecPairApply
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeProduct

variable {q : ℕ} {C : Type 1} [Category.{0} C]

def secPair (P : Probe C q) (i i' : ℤ) (s t r : ℕ) (h : s + t = r) :
    Pairing ((P.res i).K s) ((P.res i').K t) ((P.res (i + i')).K r) where
  μ c := LinearMap.mk₂ ℤ
    (fun (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (s : ℤ)) (P.U c)) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (t : ℤ)) (P.U c)) =>
      (twPair q i i').mul (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) a b)
    (fun a a' b => by simp)
    (fun n a b => by simp)
    (fun a b b' => by simp)
    (fun n a b => by simp)
  nat {c c'} φ x y := ((twPair q i i').nat (P.S.map φ).unop (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y).symm

def resPair [NeZero q] (hK : KapMul) (hT : InTw) (P : Probe C q) (i i' : ℤ) :
    ResPair (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q)) where
  μ := secPair P i i'
  ι c x y := hK hT q i i' (P.U c) (P.ζ c) x y
  leib s t r h c x y := by
    have e := (twPair q i i').leibniz (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y
    have e2 : ((s : ℤ).negOnePow : ℤˣ) • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) =
        (-1 : ℤ) ^ s • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) := by
      rw [Units.smul_def, Int.coe_negOnePow_natCast]
    rw [e2] at e
    exact e

theorem res_res {R : Type} [CommRing R] {G : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem term_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i : ℤ) (j : ℕ)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin 1 → Fin (n + 1)) (hg : Monotone g) :
    term ((P.res i).K j) s (Y.glob i j a) g hg = Sec.res (Y.y (s.obj (Fin.last n))) a := by
  simp only [CH.term, Probe.Pts.glob, Probe.res, secF]
  show Sec.res _ (Sec.res _ a) = _
  rw [res_res]
  congr 1
  exact Y.nat _

theorem cupC_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i i' : ℤ) (j j' n : ℕ) (h : j + j' = n)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (j' : ℤ)) X) :
    (secPair P i i' j j' n h).cupC (add_zero 0) (Y.glob i j a) (Y.glob i' j' b) =
      Y.glob (i + i') n ((twPair q i i').mul X (j : ℤ) (j' : ℤ) (n : ℤ) (by omega) a b) := by
  simp only [CH.Pairing.cupC, secPair]
  funext s
  simp only [LinearMap.mk₂_apply, term_glob]
  rw [← (twPair q i i').nat]
  rfl

theorem cast_cup {E : Spc} {n m k i j : ℤ} (h : n + m = k) (hc : n + m = k) (x : Ht q E n i) (y : Ht q E m j) :
    Ht.cast hc rfl (GlobalTheory.EtC.cup q x y) = (twPair q i j).cup E h x y := by
  subst hc
  rfl

theorem etCup : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.EdgeCup → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepCup →
    CrystallineSemistableComparison.E.KapMul → CrystallineSemistableComparison.E.EtCup := by
  intro hSpec hGood hEdge hBasic hRC hK hG hT q _ C _ P X Y i i' i'' hi j j' j'' hj x y
  subst hi
  have h : (j : ℤ) + (j' : ℤ) = (j'' : ℤ) := by omega
  rw [cast_cup h]
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i)) X (j : ℤ)).1 x
  obtain ⟨b, hb⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i')) X (j' : ℤ)).1 y
  have hab := hRC (ZMod q) _ _ _ (twPair q i i') X _ _ _ h x y a b ha hb
  have ea := (hSpec hG q C P X Y i j x).1 a ha
  have eb := (hSpec hG q C P X Y i' j' y).1 b hb
  have e := hEdge ℤ C P.L P.L P.L (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q))
    (resPair hK hT P i i') (hGood hG q C P i) (hGood hG q C P i') j j' j'' hj
    (Y.glob i j a) (Y.glob i' j' b) (Y.et i j x) (Y.et i' j' y) ea eb
  have e' := (congrArg (fun z => (P.res (i + i')).Edge z
    ((mulP (lcF P.S q)).cup hj (Y.et i j x) (Y.et i' j' y))) (cupC_glob P Y i i' j j' j'' hj a b)).mp e
  exact ((hSpec hG q C P X Y (i + i') j'' _).2 _ ⟨_, hab, e'⟩).symm

end GlobalTheory.CompanionTheory.EdgeProduct
end
end
