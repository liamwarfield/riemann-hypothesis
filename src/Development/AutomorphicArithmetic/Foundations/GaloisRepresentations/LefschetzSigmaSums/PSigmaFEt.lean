module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaFEt
open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaFEt_of :
    SigmaFEt := by
  intro Y Z s _ _ I _
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y k
  let i : (∐ fun _ : I => Y) ≅ ∐ fun _ : Fin k => Y :=
    Sigma.whiskerEquiv (f := fun _ : I => Y) (g := fun _ : Fin k => Y) e fun _ => Iso.refl Y
  have hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y) ≫ s := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolPull
open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

private theorem isSquare_square_compatible_homs {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A']
    [IsCommMonObj A'] (ψ : A ⟶ A') : Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.LocalSmoothExtension.polPull_of :
    PolPull := by
  intro G R _ _ b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hc c ⟨h⟩
  letI := o'.grp
  letI := o'.comm
  letI := o''.grp
  letI := o''.comm
  letI := o₁'.grp
  letI := o₁'.comm
  letI := o₁''.grp
  letI := o₁''.comm
  have hsq : Hecke.sq2 ψ₁ ≫ m''.φ₂ = m'.φ₂ ≫ Hecke.sq2 ψ := by
    apply MapComp.isSquare_unique (MapComp.isSquare_comp (isSquare_square_compatible_homs ψ₁) m''.sq)
    rw [hc]
    exact MapComp.isSquare_comp m'.sq (isSquare_square_compatible_homs ψ)
  have hp : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
  have hp₁ : (Hecke.lbPow o₁'.P c).IsLB := LB.isLB_linComb o₁'.isLB _ _
  have hq : (o''.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o''.isLB _
  have hA := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol
  have hB := (GlobalTheory.CechPic.cls_eq_iff o₁''.isLB (pull_isLB o''.isLB m''.φ₂)).2 m''.pol
  have hC := (GlobalTheory.CechPic.cls_eq_iff hp hq).2 h
  refine ⟨(GlobalTheory.CechPic.cls_eq_iff hp₁ (pull_isLB o₁''.isLB _)).1 ?_⟩
  rw [GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB, hA, GlobalTheory.CechPic.cls_pull o'.isLB,
    GlobalTheory.CechPic.cls_pull o₁''.isLB, hB, GlobalTheory.CechPic.cls_pull o''.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
    GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o''.isLB (Hecke.sq2 ψ) hq, ← hC,
    GlobalTheory.BirigidPow.cls_lbPow o'.isLB, map_nsmul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMapEq
open UpperTheory.Gal.LocalSmoothExtension

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory.UPel.HT.MapComp

theorem UpperTheory.Gal.LocalSmoothExtension.mapEq_of :
    MapEq := by
  intro G R _ _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₂
  refine ⟨fun m₁ => ?_, fun m => ?_⟩
  · refine ⟨⟨m₁.φ ≫ m₂.φ, m₁.φ₂ ≫ m₂.φ₂, IsGrpPullback.comp m₁.cart m₂.cart,
      isSquare_comp m₁.sq m₂.sq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
        (lbIso_pull_comp m₂.pol m₁.φ₂ rfl), fun y => ?_⟩, rfl⟩
    · rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
    · rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]
  · have hw : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by
      rw [Category.assoc]; exact m.cart.1.w
    let φ : o₁.A.left ⟶ o₂.A.left := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) hw
    have h₁ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
    have h₂ : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
    obtain ⟨φ₂, hsq⟩ := exists_isSquare h₂
    have h₃ : φ₂ ≫ m₂.φ₂ = m.φ₂ := by
      have := isSquare_comp hsq m₂.sq
      rw [h₁] at this
      exact isSquare_unique this m.sq
    have hc : IsGrpPullback o₁.A o₂.A f φ :=
      IsGrpPullback.cancel m₂.cart (by rw [h₁]; exact m.cart) h₂
    refine ⟨⟨φ, φ₂, hc, hsq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
        (lbIso_pull_comp m₂.pol φ₂ h₃.symm).symm, fun y => ?_⟩, h₁⟩
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.act, Category.assoc, m₂.act, ← Category.assoc, h₁]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, h₂, ← Category.assoc, Over.w]
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.eta, Category.assoc, Category.assoc, m₂.eta]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, ← Category.assoc, Over.w]
        simp

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLegBc
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.Gen.BaseChange (down exists_gObjMap_pull spMap_comp')
open UpperTheory.Gal.Int.Geo (IsTrans)
open UpperTheory.Gal.LocalSmoothExtension

private theorem objMap_along {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj b N s'} {o : GObj b N s} {f g : S' ⟶ S}
    (e : f = g) (n : GObjMap o' o f) : ∃ n' : GObjMap o' o g, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

theorem UpperTheory.Gal.LocalSmoothExtension.legBc_of :
    MapEq → TransPull → LegBc := by
  intro hME hTP p _ D G L R₁ R₂ _ _ _ _ τ gb₁ gb₂ hρ ht N N' M M' P P' f f' hf hf' m m' h π o ψ φ hπ hψ
  have hw : (f' ≫ π) ≫ M.s = P'.s ≫ spMap τ := by
    rw [Category.assoc, hπ]
    exact hf'.w
  obtain ⟨π₁, hπf, hπs⟩ : ∃ π₁ : P'.X ⟶ P.X, π₁ ≫ f = f' ≫ π ∧ π₁ ≫ P.s = P'.s :=
    ⟨hf.lift (f' ≫ π) P'.s hw, hf.lift_fst _ _ _, hf.lift_snd _ _ _⟩
  obtain ⟨o₁, ⟨φ₁⟩⟩ : ∃ o₁ : GObj gb₂ N P'.s, Nonempty (GObjMap o₁ P.univ π₁) := by
    have key := exists_gObjMap_pull π₁ P.univ
    rw [hπs] at key
    exact key
  let d₁ : GObj gb₁ N (P'.s ≫ spMap τ) := down hρ ht rfl o₁
  let φd : GObjMap d₁ (down hρ ht rfl P.univ) π₁ :=
    ⟨φ₁.φ, φ₁.φ₂, φ₁.cart, φ₁.sq, φ₁.act, φ₁.pol, φ₁.eta⟩
  obtain ⟨n, hn⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ (down hρ ht rfl P.univ) M.univ π₁ f m).1 φd
  obtain ⟨n', hn'⟩ := objMap_along hπf n
  obtain ⟨m'', hm''⟩ := (hME D.toG R₁ gb₁ N _ _ _ _ _ _ d₁ o M.univ f' π φ).2 n'
  obtain ⟨ψ₁, hψ₁, hT⟩ := hTP p D G L R₁ gb₁ N N' _ _ M'.s (P'.s ≫ spMap τ) f' hf'.w M'.univ o
    (down hρ ht rfl P'.univ) d₁ m' m'' h ψ hψ
  obtain ⟨t₁, t₂, t₃, t₄, t₅⟩ := hT
  refine ⟨π₁, o₁, ψ₁, φ₁, hπs, ⟨t₁, t₂, t₃, t₄, fun k _ _ t β hβ => ?_⟩, hπf, ?_⟩
  · exact t₅ k t (β.comp τ) (by rw [spMap_comp', ← Category.assoc, hβ])
  · have e : φ₁.φ ≫ m.φ = m''.φ ≫ φ.φ := by
      rw [hm'', hn', hn]
      rfl
    calc (ψ₁.left ≫ φ₁.φ) ≫ m.φ = ψ₁.left ≫ φ₁.φ ≫ m.φ := Category.assoc _ _ _
      _ = ψ₁.left ≫ m''.φ ≫ φ.φ := congrArg (fun z => ψ₁.left ≫ z) e
      _ = (ψ₁.left ≫ m''.φ) ≫ φ.φ := (Category.assoc _ _ _).symm
      _ = m'.φ ≫ ψ.left ≫ φ.φ := by rw [hψ₁, Category.assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaSplit
open UpperTheory.Gal.LocalSmoothExtension
open AlgebraicGeometry CategoryTheory Limits

private lemma UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

theorem UpperTheory.Gal.LocalSmoothExtension.sigmaSplit_of :
    SigmaFEt → UpperTheory.Gal.G3.SplitsPts → UpperTheory.Gal.G3.PtsOfSplits → SigmaSplit := by
  intro hF hSP hPS Y Z W s _ _ I _ c Δ _ σ hs
  obtain ⟨hF1, hF2⟩ := hF Y Z s I
  obtain ⟨hsc, hiso⟩ := hs
  have hne : ∀ (Ω : Type) [Field Ω], Nonempty (UpperTheory.Gal.G3.sp Ω) := fun Ω _ =>
    inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  have hpt : ∀ (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ ∐ fun _ : I => Y),
      ∃ i : I, ∃ y' : UpperTheory.Gal.G3.sp Ω ⟶ Y, y' ≫ Sigma.ι (fun _ : I => Y) i = y := by
    intro Ω _ y
    haveI := UpperTheory.Gal.LocalSmoothExtension.sp_subsingleton Ω
    obtain ⟨p⟩ := hne Ω
    obtain ⟨⟨i, a⟩, ha⟩ := (sigmaMk (fun _ : I => Y)).surjective (y.base p)
    rw [sigmaMk_mk] at ha
    refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => Y) i) y ?_,
      IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    exact ⟨a, by rw [Subsingleton.elim q p]; exact ha⟩
  refine hSP _ c (I × Δ) _ ?_ ?_
  · intro z
    simp [hsc]
  · intro Ω _ _ x y hy
    obtain ⟨i, y', rfl⟩ := hpt Ω y
    have hy' : y' ≫ s = x ≫ c := by simpa using hy
    obtain ⟨δ, hδ, hδu⟩ := hPS s c Δ σ ⟨hsc, hiso⟩ Ω x y' hy'
    refine ⟨(i, δ), ?_, ?_⟩
    · show x ≫ (σ δ ≫ _) = _
      rw [← hδ, Category.assoc]
    · rintro ⟨i', δ'⟩ h
      change x ≫ (σ δ' ≫ Sigma.ι (fun _ : I => Y) i') = y' ≫ Sigma.ι (fun _ : I => Y) i at h
      by_cases hii : i' = i
      · subst hii
        have hx : x ≫ σ δ' = y' := by
          rw [← Category.assoc] at h
          exact (cancel_mono _).1 h
        rw [hδu δ' hx]
      · haveI := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) (a := x ≫ σ δ') (b := y')
          ⟨by rw [Category.assoc]; exact h⟩ hii
        obtain ⟨p⟩ := hne Ω
        exact isEmptyElim p
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTatePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.tatePull_of :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R]
      (b : GBase D.toG R) (N : ℕ) (S S₁ : Scheme.{0})
      (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S)
      (o : GObj b N s) (o₁ : GObj b N s₁) (m : GObjMap o₁ o f)
      (k : Type) [Field k] (t : Sp k ⟶ S₁) (I : UpperTheory.Gal.Int.Geo.TIso o (t ≫ f)),
      ∃ I₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t, ∀ n y,
        (I₁.ev n y).left ≫ m.φ = (I.ev n y).left := by
  intro p _ D R _ _ b N S S₁ s s₁ f o o₁ m k _ t I
  letI := o.grp
  letI := o₁.grp
  letI := o.comm
  have hl : ∀ x : Over.mk t ⟶ o₁.A,
      Over.Hom.left (pushHom m.cart (Over.mk t) x) = Over.Hom.left x ≫ m.φ := fun _ => rfl
  let E := MulEquiv.ofBijective (pushHom m.cart (Over.mk t))
    ⟨push_injective m.cart _, push_surjective m.cart _⟩
  have key : ∀ q, Over.Hom.left (E.symm q) ≫ m.φ = Over.Hom.left q := fun q => by
    rw [← hl]
    exact congrArg Over.Hom.left (E.apply_symm_apply q)
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n y => E.symm (I.ev n y),
            add := fun n x y => by simp only [I.add, map_mul],
            lin := fun n c x => ?_,
            ker := fun n hn x => by
              rw [← I.ker n hn x]
              exact E.symm.map_eq_one_iff,
            onto := fun n hn q => ?_,
            tower := fun n j hn hj x => by rw [← map_pow, I.tower n j hn hj x],
            isom := fun n hn x y => ?_ }, fun n y => key (I.ev n y)⟩
  · have h1 := push_comp m.cart (m.act c) (Over.mk t) (E.symm (I.ev n x))
    have h2 : pushHom m.cart (Over.mk t) (E.symm (I.ev n x)) = I.ev n x := E.apply_symm_apply _
    rw [h2] at h1
    apply E.injective
    rw [E.apply_symm_apply, I.lin]
    exact h1.symm
  · constructor
    · intro hq
      obtain ⟨x, hx⟩ := (I.onto n hn (E q)).1 (by rw [← map_pow, hq, map_one])
      exact ⟨x, by rw [hx, E.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨x, rfl⟩, map_one]
  · exact (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o₁.isLB _)
      m.cart (diag_iso m.sq m.pol) (Over.mk t) _ _ _ _ _ _ (key _).symm (key _).symm).2
      (I.isom n hn x y)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.LevelIsPullback
open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.G3 (bcMap bcMap_fst bcMap_snd)
open UpperTheory.Gal.Int.Geo (KS Lv)

private theorem level_isPullback {S S' B B' Z : Scheme.{0}} {A : Over S} {A' : Over S'} {s : S ⟶ B'} {s' : S' ⟶ B}
    {f : S' ⟶ S} {g : B ⟶ B'} {φ : A'.left ⟶ A.left} (hφ : φ ≫ A.hom = A'.hom ≫ f)
    (H : IsPullback φ A'.hom A.hom f) (hf : IsPullback f s' s g) (k : ℕ) {q : Z ⟶ B'}
    (e : Z ≅ (GlobalTheory.KS.pow A k).left) (he : e.hom ≫ (GlobalTheory.KS.pow A k).hom ≫ s = q) :
    IsPullback (GlobalTheory.KS.powMap f φ hφ k ≫ e.inv) ((GlobalTheory.KS.pow A' k).hom ≫ s') q g := by
  have P := (GlobalTheory.KS.PowPB.powMap_isPullback S S' A A' f φ hφ H k).paste_vert hf
  have Q : IsPullback e.inv ((GlobalTheory.KS.pow A k).hom ≫ s) q (𝟙 B') := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← he, Category.comp_id, Iso.inv_hom_id_assoc]
  have R := P.paste_horiz Q
  rw [Category.comp_id] at R
  exact R

private theorem pow_square (pc : PowComp) {S₁ S₂ S₁' S₂' : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {f₁ : S₁' ⟶ S₁} {f₂ : S₂' ⟶ S₂} {π : S₂ ⟶ S₁} {π' : S₂' ⟶ S₁'} {φ₁ : A₁'.left ⟶ A₁.left}
    {φ₂ : A₂'.left ⟶ A₂.left} {χ : A₂.left ⟶ A₁.left} {χ' : A₂'.left ⟶ A₁'.left}
    (h₁ : φ₁ ≫ A₁.hom = A₁'.hom ≫ f₁) (h₂ : φ₂ ≫ A₂.hom = A₂'.hom ≫ f₂)
    (hχ : χ ≫ A₁.hom = A₂.hom ≫ π) (hχ' : χ' ≫ A₁'.hom = A₂'.hom ≫ π')
    (hπ : π' ≫ f₁ = f₂ ≫ π) (hc : χ' ≫ φ₁ = φ₂ ≫ χ) (k : ℕ) :
    GlobalTheory.KS.powMap π' χ' hχ' k ≫ GlobalTheory.KS.powMap f₁ φ₁ h₁ k = GlobalTheory.KS.powMap f₂ φ₂ h₂ k ≫ GlobalTheory.KS.powMap π χ hχ k := by
  have h₃ : (φ₂ ≫ χ) ≫ A₁.hom = A₂'.hom ≫ (f₂ ≫ π) := by
    rw [Category.assoc, hχ, ← Category.assoc, h₂, Category.assoc]
  rw [pc _ _ _ A₂' A₁' A₁ π' f₁ (f₂ ≫ π) χ' φ₁ (φ₂ ≫ χ) hχ' h₁ h₃ hπ hc k,
    pc _ _ _ A₂' A₂ A₁ f₂ π (f₂ ≫ π) φ₂ χ (φ₂ ≫ χ) h₂ hχ h₃ rfl rfl k]

private theorem level_tr {S₁ S₂ S₁' S₂' B B' Z₁ Z₂ : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {q₁ : Z₁ ⟶ B'} {q₂ : Z₂ ⟶ B'} {g : B ⟶ B'} {k : ℕ} {s₁' : S₁' ⟶ B} {s₂' : S₂' ⟶ B}
    {Φ₁ : (GlobalTheory.KS.pow A₁' k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Φ₂ : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₂ k).left}
    {Ψ : (GlobalTheory.KS.pow A₂ k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Ψ' : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₁' k).left}
    {π' : S₂' ⟶ S₁'} (hΨ' : Ψ' ≫ (GlobalTheory.KS.pow A₁' k).hom = (GlobalTheory.KS.pow A₂' k).hom ≫ π') (hs : π' ≫ s₁' = s₂')
    (hsq : Ψ' ≫ Φ₁ = Φ₂ ≫ Ψ) (e₁ : Z₁ ≅ (GlobalTheory.KS.pow A₁ k).left) (e₂ : Z₂ ≅ (GlobalTheory.KS.pow A₂ k).left)
    (t : Z₂ ⟶ Z₁) (ht : t ≫ q₁ = q₂) (he : t ≫ e₁.hom = e₂.hom ≫ Ψ)
    (P₁ : IsPullback (Φ₁ ≫ e₁.inv) ((GlobalTheory.KS.pow A₁' k).hom ≫ s₁') q₁ g)
    (P₂ : IsPullback (Φ₂ ≫ e₂.inv) ((GlobalTheory.KS.pow A₂' k).hom ≫ s₂') q₂ g) :
    bcMap g t ht ≫ P₁.isoPullback.symm.hom = P₂.isoPullback.symm.hom ≫ Ψ' := by
  have hΨ : Ψ ≫ e₁.inv = e₂.inv ≫ t := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply P₁.hom_ext
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst, bcMap_fst]
    rw [reassoc_of% hsq, hΨ, ← Category.assoc Φ₂ e₂.inv t, IsPullback.isoPullback_inv_fst_assoc]
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd, bcMap_snd]
    rw [reassoc_of% hΨ', hs, IsPullback.isoPullback_inv_snd]

theorem UpperTheory.Gal.LocalSmoothExtension.kSBc_of :
    ModelBc → LegBc → PowComp → KSBc := by
  intro hmod hleg pc p _ D G L R _ _ gb k T τ gb' hρ ht
  have ht' : ∀ i, gb'.t i = τ.comp (gb.t i) := fun i => RingHom.ext fun c => ht i c
  have hM := fun N : Lv p => hmod D.toG R ℂ τ gb gb' hρ ht' (↑N) (T.M N)
  choose M' f hpb hm using hM
  let m := fun N => (hm N).some
  have hφ : ∀ N, (m N).φ ≫ (T.M N).univ.A.hom = (M' N).univ.A.hom ≫ f N := fun N => (m N).cart.1.w
  have P : ∀ N, IsPullback (GlobalTheory.KS.powMap (f N) (m N).φ (hφ N) k ≫ (T.e N).inv)
      ((GlobalTheory.KS.pow (M' N).univ.A k).hom ≫ (M' N).s) (T.X.q (T.lev N)) (Spec.map (CommRingCat.ofHom τ)) :=
    fun N => level_isPullback (hφ N) (m N).cart.1 (hpb N) k (T.e N) (T.e_q N)
  refine ⟨UpperTheory.Gal.Int.Geo.KS.mk (towerBc T.X (Spec.map (CommRingCat.ofHom τ))) T.lev T.K_eq T.Δ_eq M'
    (fun N => (P N).isoPullback.symm) ?_ ?_, rfl, HEq.rfl⟩
  · intro N
    exact (P N).isoPullback_inv_snd
  · intro N' N h a b
    obtain ⟨π₀, o₀, ψ₀, φ₀, hw₀, hs₀, htr₀, he₀⟩ := T.tr_eq N' N h a b
    obtain ⟨π₁, o₁, ψ₁, φ₁, hs₁, htr₁, hπ, hc⟩ := hleg p D G L R ℂ τ gb gb' hρ ht' N N' (T.M N) (T.M N')
      (M' N) (M' N') (f N) (f N') (hpb N) (hpb N') (m N) (m N') h π₀ o₀ ψ₀ φ₀ hs₀ htr₀
    have hw₁ : (Over.Hom.left ψ₁ ≫ φ₁.φ) ≫ (M' N).univ.A.hom = (M' N').univ.A.hom ≫ π₁ := by
      rw [Category.assoc, φ₁.cart.1.w, ← Category.assoc, Over.w]
    refine ⟨π₁, o₁, ψ₁, φ₁, hw₁, hs₁, htr₁, ?_⟩
    exact level_tr (GlobalTheory.KS.PowPB.powMap_w π₁ _ hw₁ k) hs₁
      (pow_square pc (hφ N) (hφ N') hw₀ hw₁ hπ hc k) (T.e N) (T.e N') _ (T.X.tr_q _ _ h a b) he₀ (P N) (P N')
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntSum
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cntSum_of :
    CntSum := by
  classical
  intro Γ _ K K' M h hMK hKK' hnorm hconj _ Δ _ r hrK hr V _ _ P hP
  have hPM : ∀ c ∈ K', ∀ u ∈ M, P (h * c * u) = P (h * c) := by
    intro c hc u hu
    have e := hP _ (hconj c hc u hu) c hc
    rw [← e]
    congr 1
    group
  let φ : (K' ⧸ K.subgroupOf K') × Δ → K' ⧸ M.subgroupOf K' := fun z =>
    QuotientGroup.mk (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨a, x⟩ ⟨a', x'⟩ he
      simp only [φ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at he
      push_cast at he
      have hK : (↑(Quotient.out a) : Γ)⁻¹ * ↑(Quotient.out a') ∈ K := by
        have e := K.mul_mem (K.mul_mem (hrK x) (hMK he)) (K.inv_mem (hrK x'))
        convert e using 1
        group
      have ha : a = a' := by
        rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a', QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        push_cast
        exact hK
      subst ha
      have hx1 : r x' * (r x')⁻¹ ∈ M := by simpa using M.one_mem
      have hx2 : r x' * (r x)⁻¹ ∈ M := by
        have e := hnorm (r x) (hKK' (hrK x)) _ he
        convert e using 1
        group
      obtain ⟨x0, _, hu⟩ := hr (r x') (hrK x')
      rw [hu x hx2, hu x' hx1]
    · intro b
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf K') c
      have hκ : (↑(Quotient.out (QuotientGroup.mk c : K' ⧸ K.subgroupOf K')) : Γ)⁻¹ * ↑c ∈ K := by
        rw [hk]
        push_cast
        have e := K.inv_mem (Subgroup.mem_subgroupOf.1 k.2)
        convert e using 1
        group
      obtain ⟨x, hx, -⟩ := hr _ hκ
      refine ⟨(QuotientGroup.mk c, x), ?_⟩
      simp only [φ]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      push_cast
      have e := hnorm (r x)⁻¹ (K'.inv_mem (hKK' (hrK x))) _ hx
      convert e using 1
      group
  haveI : Finite (K' ⧸ M.subgroupOf K') := Finite.of_surjective φ hφ.2
  letI : Fintype (K' ⧸ M.subgroupOf K') := Fintype.ofFinite _
  have hL : ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out z.1) * r z.2)
      = ∑ z : (K' ⧸ K.subgroupOf K') × Δ, P (h * ↑(Quotient.out (φ z))) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K')
      (Quotient.out z.1 * ⟨r z.2, hKK' (hrK z.2)⟩)
    simp only [φ]
    rw [hu]
    push_cast
    have hc : (↑(Quotient.out z.1) : Γ) * r z.2 ∈ K' :=
      K'.mul_mem (Quotient.out z.1).2 (hKK' (hrK z.2))
    have e := hPM _ hc _ (Subgroup.mem_subgroupOf.1 u.2)
    rw [mul_assoc h, ← e]
    congr 1
    group
  let g : K' ⧸ M.subgroupOf K' → Γ ⧸ K := fun b => QuotientGroup.mk (h * ↑(Quotient.out b))⁻¹
  have hcnt : ∀ y : Γ ⧸ K, cntFn K K' M h (Quotient.out y)
      = ((Finset.univ.filter (fun b => g b = y)).card : ℂ) := by
    intro y
    have hset : (Finset.univ.filter fun b : K' ⧸ M.subgroupOf K' =>
        h * ↑(Quotient.out b) * Quotient.out y ∈ K) = Finset.univ.filter fun b => g b = y := by
      refine Finset.filter_congr fun b _ => ?_
      simp only [g]
      conv_rhs => rw [← QuotientGroup.out_eq' y]
      rw [QuotientGroup.eq, inv_inv]
    unfold cntFn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset]
  have hsupp : (Function.support fun y : Γ ⧸ K =>
      cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹) ⊆ ↑(Finset.univ.image g) := by
    intro y hy
    rw [Function.mem_support, hcnt] at hy
    by_contra hyn
    apply hy
    have e : Finset.univ.filter (fun b => g b = y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hyn (Finset.mem_coe.2 (Finset.mem_image.2 ⟨b, Finset.mem_univ _, hb⟩))
    simp [e]
  have hR : ∑ y ∈ Finset.univ.image g, cntFn K K' M h (Quotient.out y) • P (Quotient.out y)⁻¹
      = ∑ b, P (Quotient.out (g b))⁻¹ := by
    rw [Finset.sum_comp (fun y => P (Quotient.out y)⁻¹) g]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hcnt, Nat.cast_smul_eq_nsmul]
  have hR4 : ∑ b, P (Quotient.out (g b))⁻¹ = ∑ b : K' ⧸ M.subgroupOf K', P (h * ↑(Quotient.out b)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (h * ↑(Quotient.out b))⁻¹
    simp only [g]
    rw [hk, show ((h * ↑(Quotient.out b))⁻¹ * (↑k : Γ))⁻¹ = (↑k)⁻¹ * (h * ↑(Quotient.out b)) by group]
    exact hP _ (K.inv_mem k.2) _ (Quotient.out b).2
  rw [hL, Fintype.sum_bijective φ hφ (fun z => P (h * ↑(Quotient.out (φ z))))
    (fun b => P (h * ↑(Quotient.out b))) (fun _ => rfl), finsum_eq_sum_of_support_subset _ hsupp, hR, hR4]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PullCongr
open UpperTheory.Gal.LocalSmoothExtension

open CategoryTheory Limits AlgebraicGeometry in
private theorem pull_congr' {B : Scheme.{0}} {R : Type} [Field R] (Θ : UpperTheory.Gal.G3.Th.{0} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (hf : f ≫ p = q) (hf' : f' ≫ p = q) (x : Θ.H p) :
    Θ.pull f hf x = Θ.pull f' hf' x := by
  subst e
  rfl


open CategoryTheory Limits AlgebraicGeometry in
private theorem pull_base {B : Scheme.{0}} {R : Type} [Field R] (Θ : UpperTheory.Gal.G3.Th.{0} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} (c : W ⟶ Z) {J : Type} [Fintype J] (f : J → (W ⟶ Z')) (A : Θ.H p' →ₗ[R] Θ.H p)
    (r : W ⟶ B) (hc : c ≫ p = r) (hf : ∀ j, f j ≫ p' = r)
    (H : ∀ x, Θ.pull c hc (A x) = ∑ j, Θ.pull (f j) (hf j) x) (hf' : ∀ j, f j ≫ p' = c ≫ p) (x : Θ.H p') :
    Θ.pull c rfl (A x) = ∑ j, Θ.pull (f j) (hf' j) x := by
  subst hc
  exact H x


open CategoryTheory Limits AlgebraicGeometry in
private theorem op_core (hFn : CntFn) (hSum : CntSum) (hSig : SigmaFEt) (hSpl : SigmaSplit)
    (hGal : UpperTheory.Gal.G3.TwGal) (hEx : UpperTheory.Gal.G3.HopEx.{0})
    {B : Scheme.{0}} {Γ : Type} [Group Γ] (X : UpperTheory.Gal.G3.Tower B Γ) (i m : X.ι) (K K' M : Subgroup Γ) (h : Γ)
    (hK : X.K i = K) (hM : X.K m = M) (hMK : M ≤ K) (hKK : K ≤ K')
    (hn : ∀ k ∈ K', ∀ u ∈ M, k * u * k⁻¹ ∈ M) (hidx : M.relIndex K' ≠ 0)
    (hadm : ∀ k ∈ K', ∀ u ∈ M, h * k * u * (h * k)⁻¹ ∈ K) (hΔ : ∀ k ∈ K', h * k ∈ X.Δ)
    (a1 : (1 : Γ) ∈ X.Δ) (b1 : ∀ u ∈ X.K m, (1 : Γ) * u * 1⁻¹ ∈ X.K i)
    (aT : ∀ c : K' ⧸ K.subgroupOf K', h * (c.out : Γ) ∈ X.Δ)
    (bT : ∀ c : K' ⧸ K.subgroupOf K', ∀ u ∈ X.K m, h * (c.out : Γ) * u * (h * (c.out : Γ))⁻¹ ∈ X.K i) :
    X.IsFn i (cntFn K K' M h) ∧
    IsFinite (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1) ∧
    Etale (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1) ∧
    ∀ Θ : UpperTheory.Gal.G3.Th.{0} B ℂ, Θ.Good → Θ.IsOp (X.q i) (X.q i)
      (Sigma.desc fun _ : K' ⧸ K.subgroupOf K' => X.tr m i 1 a1 b1)
      (Sigma.desc fun c : K' ⧸ K.subgroupOf K' => X.tr m i (h * (c.out : Γ)) (aT c) (bT c))
      (X.hecke Θ i (cntFn K K' M h)) := by
  subst hK hM
  have hcnt := hFn Γ (X.K i) K' (X.K m) h hKK hn hidx hadm
  have hIsFn : X.IsFn i (cntFn (X.K i) K' (X.K m) h) := by
    refine ⟨fun k hk g => hcnt.1 k hk g, fun g hg => ?_, hcnt.2.2⟩
    obtain ⟨k, hk, c, hc, e⟩ := hcnt.2.1 g hg
    rw [e]
    exact X.Δ.mul_mem (X.K_le i k hk) (hΔ c hc)
  have hne : (X.K i).relIndex K' ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_of_le_left K' hMK
    rw [h0] at hd
    exact hidx (Nat.eq_zero_of_zero_dvd hd)
  haveI : ((X.K i).subgroupOf K').FiniteIndex := ⟨hne⟩
  haveI : IsFinite (X.tr m i 1 a1 b1) := X.fin m i a1 b1
  haveI : Etale (X.tr m i 1 a1 b1) := X.etale m i a1 b1
  have hsig := hSig (X.Z m) (X.Z i) (X.tr m i 1 a1 b1) (K' ⧸ (X.K i).subgroupOf K')
  refine ⟨hIsFn, hsig.1, hsig.2, fun Θ hΘ => ?_⟩
  obtain ⟨Γ₀, _, _, r, cadm, hr, huq, hgal⟩ :=
    hGal X m i ⟨a1, b1⟩ (fun k hk u hu => hn k (hKK hk) u hu)
  letI : Fintype Γ₀ := Fintype.ofFinite Γ₀
  letI : Fintype (K' ⧸ (X.K i).subgroupOf K') := Fintype.ofFinite _
  have HarishChandraLabels : ∀ c ∈ K', X.admitted m i (h * c) := fun c hc => ⟨hΔ c hc, fun u hu => hadm c hc u hu⟩
  have adm : ∀ z : (K' ⧸ (X.K i).subgroupOf K') × Γ₀, X.admitted m i (h * (z.1.out : Γ) * r z.2) :=
    fun z => UpperTheory.Gal.G3.Tower.admitted.mul (cadm z.2) (HarishChandraLabels _ z.1.out.2)
  have ecomp : ∀ z : (K' ⧸ (X.K i).subgroupOf K') × Γ₀,
      (X.tr m m (r z.2) (cadm z.2).1 (cadm z.2).2 ≫
          Sigma.ι (fun _ : K' ⧸ (X.K i).subgroupOf K' => X.Z m) z.1) ≫
        Sigma.desc (fun c : K' ⧸ (X.K i).subgroupOf K' => X.tr m i (h * (c.out : Γ)) (aT c) (bT c)) =
      X.tr m i (h * (z.1.out : Γ) * r z.2) (adm z).1 (adm z).2 := by
    intro z
    rw [Category.assoc, Sigma.ι_desc]
    exact X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  have hspl := hSpl (X.Z m) (X.Z i) (X.Z m) (X.tr m i 1 a1 b1) (K' ⧸ (X.K i).subgroupOf K')
    (X.tr m i 1 a1 b1) Γ₀ (fun x => X.tr m m (r x) (cadm x).1 (cadm x).2) hgal.2.2.2.2.2
  refine ⟨X.Z m, X.tr m i 1 a1 b1, Γ₀, inferInstance, inferInstance,
    fun x => X.tr m m (r x) (cadm x).1 (cadm x).2, (K' ⧸ (X.K i).subgroupOf K') × Γ₀, inferInstance,
    fun z => X.tr m m (r z.2) (cadm z.2).1 (cadm z.2).2 ≫
      Sigma.ι (fun _ : K' ⧸ (X.K i).subgroupOf K' => X.Z m) z.1,
    fun z => by rw [ecomp z, X.tr_q, X.tr_q], hgal, hspl, fun y => ?_⟩
  refine pull_base Θ _ _ _ (X.q m) (X.tr_q m i 1 a1 b1) (fun z => by rw [ecomp z, X.tr_q])
    (fun y => ?_) _ y
  have hHop := (hEx X Θ hΘ i (cntFn (X.K i) K' (X.K m) h) hIsFn).1
  have hop := hHop m hMK (fun g hg => by
    obtain ⟨k, hk, c, hc, e⟩ := hcnt.2.1 g hg
    rw [e]
    exact UpperTheory.Gal.G3.Tower.admitted.mul (HarishChandraLabels c hc) (X.tower_admissible_self hk)) y
  have hsum := hSum Γ (X.K i) K' (X.K m) h hMK hKK hn hadm Γ₀ r hr huq (Θ.H (X.q m))
    (fun g => X.pl Θ m i g y) (fun k hk c hc => X.pl_left Θ (HarishChandraLabels c hc) hk y)
  refine ((by rw [X.pl_eq Θ (show X.admitted m i 1 from ⟨a1, b1⟩)] :
      Θ.pull (X.tr m i 1 a1 b1) (X.tr_q m i 1 a1 b1) (X.hecke Θ i (cntFn (X.K i) K' (X.K m) h) y) =
        X.pl Θ m i 1 (X.hecke Θ i (cntFn (X.K i) K' (X.K m) h) y))).trans
      (hop.trans (hsum.symm.trans (Finset.sum_congr rfl fun z _ => ?_)))
  beta_reduce
  rw [X.pl_eq Θ (adm z)]
  exact pull_congr' Θ (ecomp z).symm _ _ y

theorem UpperTheory.Gal.LocalSmoothExtension.memOp2_of :
    KNNormal → CntFn → CntSum → SigmaFEt → SigmaSplit → UpperTheory.Gal.G3.TwGal → UpperTheory.Gal.G3.HopEx.{0} → MemOp := by
  intro hKN hFn hSum hSig hSpl hGal hEx p _ D G L R _ _ gb k T N J g j
  have hMN : L.KN ↑(g j).M ≤ L.KN ↑N := UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd
  have hMK' : L.KN ↑(g j).M ≤ (g j).K := hMN.trans (g j).le
  have hnorm := hKN p D G L ↑(g j).M
  have hpos : 0 < (↑(g j).M : ℕ) := by
    have := (g j).M.2.1
    omega
  have hidx : (L.KN ↑(g j).M).relIndex (g j).K ≠ 0 := by
    intro h0
    apply hnorm.2 hpos
    rw [← Subgroup.relIndex_mul_relIndex (hHK := hMK') (hKL := (g j).le_one), h0, zero_mul]
  have hΔ : ∀ c ∈ (g j).K, (g j).h * c ∈ T.X.Δ := fun c hc =>
    (T.Δ_eq _).2 (UpperTheory.Gal.Int.Geo.Integ.mul (g j).int
      (UpperTheory.Gal.Int.Geo.integ_of_mem ((g j).le_one hc)))
  have a1 : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have b1 : ∀ u ∈ T.X.K (T.lev (g j).M), (1 : G.GAf) * u * 1⁻¹ ∈ T.X.K (T.lev N) := by
    intro u hu
    rw [T.K_eq] at hu ⊢
    simpa using hMN hu
  have aT : ∀ c : (g j).K ⧸ (L.KN ↑N).subgroupOf (g j).K, (g j).h * (c.out : G.GAf) ∈ T.X.Δ :=
    fun c => hΔ _ c.out.2
  have bT : ∀ c : (g j).K ⧸ (L.KN ↑N).subgroupOf (g j).K, ∀ u ∈ T.X.K (T.lev (g j).M),
      (g j).h * (c.out : G.GAf) * u * ((g j).h * (c.out : G.GAf))⁻¹ ∈ T.X.K (T.lev N) := by
    intro c u hu
    rw [T.K_eq] at hu ⊢
    exact (g j).adm _ c.out.2 u hu
  exact op_core hFn hSum hSig hSpl hGal hEx T.X (T.lev N) (T.lev (g j).M) (L.KN ↑N) (g j).K
    (L.KN ↑(g j).M) (g j).h (T.K_eq N) (T.K_eq _) hMN (g j).le
    (fun c hc u hu => hnorm.1 c ((g j).le_one hc) u hu) hidx (g j).adm hΔ a1 b1 aT bT
end
