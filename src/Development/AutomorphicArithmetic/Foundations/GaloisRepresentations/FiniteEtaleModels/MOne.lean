module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.MOne
open NumberField GlobalTheory.UPel.HT

theorem UpperTheory.Gal.FiniteEtaleModels.O.mOne :
    UpperTheory.Gal.FiniteEtaleModels.O.MOne := by
  intro q _ D hm
  haveI := D.freeLa
  haveI := D.finLa
  have hb : Function.Bijective (algebraMap (𝓞 D.F) D.O) :=
    ⟨D.algebraMap_injective hm, Datum.algebraMap_surjective_of_m_eq_one q D hm⟩
  have hfin : Module.Finite D.O D.La := Module.Finite.of_restrictScalars_finite ℤ D.O D.La
  refine ⟨hb, ?_, hfin⟩
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective _ hb
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (r : 𝓞 D.F) (x : D.La), r • x = algebraMap (𝓞 D.F) D.O r • x :=
    fun _ _ => rfl
  haveI : IsScalarTower ℤ (𝓞 D.F) D.La :=
    ⟨fun n r x => by rw [hsmul, hsmul, map_zsmul, smul_assoc]⟩
  have htors : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨r, hr⟩, hx⟩
    have hx' : r • x = 0 := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {r}))
    have hN : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr0
    have hz : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = 0 := by
      have h1 : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x =
          ((Ideal.absNorm (Ideal.span {r}) : ℕ) : 𝓞 D.F) • x := by
        rw [natCast_zsmul]
        exact (Nat.cast_smul_eq_nsmul (𝓞 D.F) _ x).symm
      rw [h1, ← hs, mul_smul, hx', smul_zero]
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hN)
  haveI : Module.Flat (𝓞 D.F) D.La := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htors
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.FinitePresentation (𝓞 D.F) D.La := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 D.F) D.La := Module.Flat.projective_of_finitePresentation
  haveI h1 : RingHomInvPair (e : 𝓞 D.F →+* D.O) (e.symm : D.O →+* 𝓞 D.F) :=
    RingHomInvPair.of_ringEquiv e
  haveI h2 : RingHomInvPair (e.symm : D.O →+* 𝓞 D.F) (e : 𝓞 D.F →+* D.O) :=
    RingHomInvPair.symm _ _
  let f : D.La ≃ₛₗ[(e : 𝓞 D.F →+* D.O)] D.La :=
    { AddEquiv.refl D.La with map_smul' := fun _ _ => rfl }
  exact Module.Projective.of_equiv f
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BLevOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bLev_of :
    LatB → EtaPtB → UpperTheory.Gal.crystallineComparison.Mod.EtInj → BLev := by
  intro hLat hEta hInj p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hle hb _ h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂
    C₁ C₂ W f mf _ e _ _ Tj P Ω _ _ x x' hj hy
  have atq' : AtPrime D q r 𝔴' := { S.atq with max := hmax, le := hle }
  refine hInj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M 𝔟₂ 1 X₂.Y X₂.π X₂.ov X₂.mπ _ _ _ ?_ ?_
  · have e₁ : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ X₂.π = z ≫ P.y ≫ Tj.t := fun z => by
      rw [P.yt]; simp only [Category.assoc]
    rw [e₁, e₁, reassoc_of% hy]
  · intro y₀
    obtain ⟨x₀, v, hv, e₀⟩ := hLat p D G L q r 𝔴' 𝔟₁ 𝔟₂ i h atq' htj hint hb X₁.lev.2.2.2.2 M₁ M₂ a₁ a₂ n₁.2 n₂.2 y₀
    have key : ∀ z : Sp Ω ⟶ (T.M M₁).X, (z ≫ W.π ≫ C₂.j) ≫ (X₂.Y.lv y₀).left ≫ X₂.mπ.φ =
        (z ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa) ≫ Tj.ψ.left ≫ Tj.mt.φ := fun z => by
      have h1 := congrArg (fun g => g.left) (hEta p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω z
        (algebraMap (𝓞 D.F) D.O a₁ • x₀) (algebraMap (𝓞 D.F) D.O a₂ • y₀) ⟨v, hv, e₀⟩)
      have ht : (toUnit (Over.mk z)).left = z := by simpa using Over.w (toUnit (Over.mk z))
      simp only [Over.comp_left, ht] at h1
      have h2 := W.φ.eta (algebraMap (𝓞 D.F) D.O a₂ • y₀)
      have h3 := C₂.lv y₀
      simp only [Category.assoc]
      rw [reassoc_of% P.sq, P.mt, reassoc_of% h1, reassoc_of% h2, reassoc_of% h3]
    have sec : ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ (T.M M₁).univ.A.hom = 𝟙 _ := by
      simpa using Over.w ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀))
    have hA : x ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa =
        x' ≫ ((T.M M₁).univ.eta (algebraMap (𝓞 D.F) D.O a₁ • x₀)).left ≫ P.fa := by
      refine Tj.ms.cart.1.hom_ext ?_ ?_
      · have h4 := C₁.lv x₀
        simp only [Category.assoc]
        rw [P.ms, reassoc_of% h4, reassoc_of% hj]
      · simp only [Category.assoc]
        rw [P.ca.1.w, reassoc_of% sec, hy]
    rw [key x, key x', hA]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepBOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.stepB_of :
    TjExG → BRead → BKer → BLev → DescExt → BaseFet → BaseOnto → UpperTheory.Gal.crystallineComparison.Mod.PulledEx → StepB := by
  intro hTj hRead hKer hLev hDesc hFet hOnto hPul p _ D G L sc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj
    M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ _ C₁ C₂ W
  have hq : q.Prime := Fact.out
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := X₂.M.rep _ _ X₁.Y.univ
  have hqw : (q : 𝓞 D.F) ∈ 𝔴' := hu (Ideal.subset_span (Set.mem_insert _ _))
  have hd : Ideal.absNorm 𝔴' ∣ q ^ Module.finrank ℤ (𝓞 D.F) := by
    have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem 𝔴').2 hqw)
    rwa [Ideal.absNorm_span_natCast] at this
  obtain ⟨f', -, hf'⟩ := (Nat.dvd_prime_pow hq).1 hd
  have hpos : 0 < f' := Nat.pos_of_ne_zero fun h0 => hmax.ne_top (Ideal.absNorm_eq_one_iff.1 (by simpa [h0] using hf'))
  have he : Ideal.absNorm 𝔴' ^ i = q ^ (f' * i) := by rw [hf', pow_mul]
  have he' : 0 < i → 0 < f' * i := fun h => Nat.mul_pos hpos h
  obtain ⟨Tj⟩ := hTj q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 S.std.pmem S.std.m1 r 𝔴' i (f' * i) hmax hu hi he' X₂.M
  obtain ⟨B⟩ := hRead p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj
  have k1 := hKer p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  have k2 := hLev p D G L sc E gb w q r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W f mf hf
    _ he he' Tj B
  obtain ⟨hfin, het⟩ := hFet p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have honto := hOnto p D G L sc E gb w q r 𝔴 _ X₁.site k T M₁ c₁ a₁ n₁ C₁
  have hsm : Smooth X₁.Y.s := by
    haveI := X₁.M.smooth
    haveI : Smooth X₁.M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) X₁.M.s
    haveI := X₁.et
    rw [← X₁.ov]
    infer_instance
  obtain ⟨y', hy, hys⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto f Tj.s B.y Tj.fin B.ys k1
  obtain ⟨P⟩ := hPul q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 X₂.M r 𝔴' i _ Tj _ f _ hf X₁.Y.univ mf y' hys
  obtain ⟨t, ht, htπ⟩ := hDesc (Ow w) E _ _ _ _ X₁.Y.s _ C₁.j C₁.ov hsm hfin het honto (y' ≫ Tj.t) X₂.π (W.π ≫ C₂.j) X₂.fin
    (by rw [← Category.assoc C₁.j, hy, B.yt, Category.assoc]) fun Ω _ _ x x' e => k2 Ω x x' e (k1 Ω x x' e)
  have hw : (P.ψ.left ≫ P.m'.φ ≫ Tj.mt.φ) ≫ X₂.M.univ.A.hom = (X₁.Y.univ.A.hom ≫ t) ≫ X₂.π := by
    rw [Category.assoc, Category.assoc, Tj.mt.cart.1.w, ← Category.assoc P.m'.φ, P.m'.cart.1.w, Category.assoc, ← Category.assoc,
      Over.w P.ψ, Category.assoc, htπ]
  have hfa : C₁.m.φ ≫ P.m₀.φ = B.fa := Tj.ms.cart.1.hom_ext
    (by rw [Category.assoc, P.tri, B.ms])
    (by rw [Category.assoc, P.m₀.cart.1.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, hy, B.ca.1.w])
  refine ⟨⟨t, ?_, X₂.mπ.cart.1.lift _ _ hw, X₂.mπ.cart.1.lift_snd _ _ _⟩, ht, X₂.mπ.cart.1.hom_ext ?_ ?_⟩
  · rw [← X₂.ov, ← Category.assoc, htπ, Category.assoc, ← Tj.st, ← Category.assoc, hys, hf]
  · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc P.ψ.left, ← P.sq, Category.assoc, ← Category.assoc, hfa,
      ← Category.assoc, B.sq, Category.assoc, B.mt]
    simp only [Category.assoc]
  · rw [Category.assoc, IsPullback.lift_snd, ← Category.assoc, C₁.m.cart.1.w, Category.assoc, ht]
    simp only [Category.assoc]
    rw [C₂.m.cart.1.w, ← Category.assoc W.φ.φ, W.φ.cart.1.w, Category.assoc, ← Category.assoc W.ψ.left, Over.w W.ψ]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.TjExGOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.tjExG_of :
    UpperTheory.Gal.crystallineComparison.Mod.EsNorm → UpperTheory.Gal.crystallineComparison.Mod.EsGen → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → UpperTheory.Gal.crystallineComparison.Mod.PullIsog → UpperTheory.Gal.crystallineComparison.Mod.PullKer → TjExG := by
  intro hN hG hT hPI hPK p _ D R _ _ _ _ b N h3 hcp hpm hm1 r w j e hw hle hj he M
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, hst, hfs, -, -, -, hiso, htj, hu⟩ :=
    hN p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, hgse, -, -, hiso0, htj0, hu0⟩ :=
    hG p D R b N h3 hcp hpm r w j (p ^ e) hw hle hj ⟨e, rfl, he⟩ hm1 M
  let U := M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))
  let V := s ⁻¹ᵁ U
  have het : Etale (s ∣_ U) := by
    have hpU : IsUnit ((p : ℕ) : Γ(U.toScheme, ⊤)) := by
      have h := GlobalTheory.EtC.PairDich.isUnit_ι_appTop U ((p : ℕ) : Γ(M.X, ⊤)) le_rfl
      rwa [map_natCast] at h
    have hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := by
      simpa only [map_natCast] using hpU.map gs.appTop.hom
    have hpV : IsUnit ((p : ℕ) : Γ(V.toScheme, ⊤)) := by
      simpa only [map_natCast] using hpU.map (s ∣_ U).appTop.hom
    have hPB := isPullback_morphismRestrict s U
    obtain ⟨oV, ⟨mV⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N
      M.X V.toScheme M.s (V.ι ≫ s) M.univ
    obtain ⟨mVo, -⟩ := (hT p D R b N h3 hcp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ V.ι s).2
      _ rfl mV ms
    obtain ⟨oV', mV', ψV, isoV, sqV⟩ := hPI p D R b N Y V.toScheme (s ≫ M.s) _ V.ι
      (Category.assoc _ _ _).symm (p ^ e) o o' ψ hiso oV mVo
    have tjV := (hPK p D R b N Y _ (s ≫ M.s) _ V.ι o o' oV oV' mVo mV' ψ ψV sqV).2 r w j htj
    obtain ⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩ := hu Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ hiso0 htj0
    obtain ⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩ := hu0 _ (V.ι ≫ s) oV oV' mV ψV hpV isoV tjV
    have hvy : v ≫ y₀ = V.ι := by
      apply (hu _ (V.ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique
      · refine ⟨by rw [Category.assoc, hy₀, hv], ?_⟩
        obtain ⟨a, ha⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y
        obtain ⟨a', ha'⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y
        refine ⟨a, a', ?_⟩
        rw [ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv,
          Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]
      · exact ⟨rfl, mVo, mV', sqV⟩
    let u : Y₀ ⟶ V.toScheme := hPB.lift gs y₀ (by rw [hgs, hy₀])
    have hu₁ : u ≫ s ∣_ U = gs := hPB.lift_fst _ _ _
    have hu₂ : u ≫ V.ι = y₀ := hPB.lift_snd _ _ _
    have hvg : v ≫ gs = s ∣_ U := by
      rw [← cancel_mono U.ι, Category.assoc, hgs, hv, morphismRestrict_ι]
    have hvu : v ≫ u = 𝟙 _ := by
      apply hPB.hom_ext
      · rw [Category.assoc, hu₁, hvg, Category.id_comp]
      · rw [Category.assoc, hu₂, hvy, Category.id_comp]
    have huv : u ≫ v = 𝟙 Y₀ := by
      apply (hu0 Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ hiso0 htj0).unique
      · refine ⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩
        have hc : (u ≫ v) ≫ y₀ = y₀ := by rw [Category.assoc, hvy, hu₂]
        obtain ⟨a, ha⟩ := (hT p D R b N h3 hcp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y
        obtain ⟨a', ha'⟩ := (hT p D R b N h3 hcp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2
          y₀ hc m₁y m₁y
        refine ⟨a, a', ?_⟩
        apply m₁y.cart.1.hom_ext
        · rw [Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀,
            Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']
        · have e1 := a.cart.1.w
          have e2 := a'.cart.1.w
          calc (a.φ ≫ Over.Hom.left ψ₀) ≫ o₀'.A.hom = a.φ ≫ o₀.A.hom := by rw [Category.assoc a.φ, Over.w]
            _ = o₀.A.hom ≫ (u ≫ v) := e1
            _ = (Over.Hom.left ψ₀ ≫ o₀'.A.hom) ≫ (u ≫ v) := by rw [Over.w]
            _ = (Over.Hom.left ψ₀ ≫ a'.φ) ≫ o₀'.A.hom := by
              rw [Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2,
                Category.assoc (Over.Hom.left ψ₀) a'.φ]
      · refine ⟨Category.id_comp _, ?_⟩
        have existsId {S S₃ : Scheme.{0}} {s : S ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
            {o : Obj b N s} {o₃ : Obj b N s₃} {g : S ⟶ S₃} (m : ObjMap o o₃ g) :
            ∃ i : ObjMap o o (𝟙 S), i.φ = 𝟙 _ := by
          obtain ⟨i, hi⟩ := (hT p D R b N h3 hcp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g
            (Category.id_comp g) m m
          refine ⟨i, m.cart.1.hom_ext ?_ ?_⟩
          · rw [hi, Category.id_comp]
          · rw [i.cart.1.w, Category.comp_id, Category.id_comp]
        obtain ⟨i, hi⟩ := existsId ms₀
        obtain ⟨i', hi'⟩ := existsId m₁y
        exact ⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩
    have : IsIso v := ⟨⟨u, hvu, huv⟩⟩
    rw [← hvg]
    infer_instance
  exact ⟨⟨Y, s, t, hst, o, o', ms, mt, ψ, hfs, het, hiso, htj, hu⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BSecInj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt Pulled UKer)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.secInjG_of :
    UpperTheory.Gal.crystallineComparison.Mod.PulledEx → UpperTheory.Gal.crystallineComparison.Mod.PulledRead → UpperTheory.Gal.crystallineComparison.Mod.PullKer → UpperTheory.Gal.crystallineComparison.Mod.KerFromU → UpperTheory.Gal.crystallineComparison.Mod.IsoOfKer → SecInjG := by
  intro hPE hPR hPK hKU hIK p _ D R _ b N hN hNp hm r w j e hw hu hj he M T K _ _ _ x y y' hy hy' hK
  have hpK0 : IsUnit ((p : ℕ) : K) := by
    refine IsUnit.mk0 _ ?_
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpK : IsUnit ((p : ℕ) : Γ(Sp K, ⊤)) := by
    have := hpK0.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp K) M.s x M.univ
  obtain ⟨P⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y hy
  obtain ⟨P'⟩ := hPE p D R b N hN hNp M r w j (p ^ e) T (Sp K) x (x ≫ M.s) rfl o₁ m₁ y' hy'
  have hc : ∃ e', p ^ e = p ^ e' ∧ (0 < j → 0 < e') := ⟨e, rfl, he⟩
  have kernel_imp (z z' : Sp K ⟶ T.Y) (hz : z ≫ T.s = x) (hz' : z' ≫ T.s = x)
      (hpoint : ∀ a : Over.mk x ⟶ M.univ.A,
        ES.KilledBy M.univ w a → KerAt T z a.left → KerAt T z' a.left)
      (Q : Pulled T m₁ z) (Q' : Pulled T m₁ z') (U : Over (Sp K)) (g : U ⟶ o₁.A)
      (hg : UKer r o₁ Q.ψ U g) : UKer r o₁ Q'.ψ U g := by
    obtain ⟨S, -, i, -, -, hfin, het, -, -, hiff⟩ :=
      ES.KerUPart.exists_kerUPart p D R b N hN hNp hm r w j (p ^ e)
        hw hu hj hc (Sp K) (x ≫ M.s) hpK o₁ Q.o' Q.ψ Q.isog Q.tj
    refine ⟨?_, hg.2⟩
    obtain ⟨v, rfl⟩ := (hiff U g).1 hg
    suffices hi : i ≫ Q'.ψ = 1 by
      rw [Category.assoc, hi]
      simp
    have : IsReduced S.left := by
      have : IsAffine S.left := isAffine_of_isAffineHom S.hom
      have hE : (Scheme.Hom.appTop S.hom).hom.Etale :=
        HasRingHomProperty.appTop @Etale S.hom het
      have hF : IsField Γ(Sp K, ⊤) :=
        MulEquiv.isField (Field.toIsField K)
          (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
      let : Field Γ(Sp K, ⊤) := hF.toField
      let := (Scheme.Hom.appTop S.hom).hom.toAlgebra
      have : Algebra.Etale Γ(Sp K, ⊤) Γ(S.left, ⊤) := hE.toAlgebra
      have : _root_.IsReduced Γ(S.left, ⊤) :=
        Algebra.FormallyUnramified.isReduced_of_field Γ(Sp K, ⊤) Γ(S.left, ⊤)
      exact isReduced_of_isAffine_isReduced S.left
    have : IsProper Q'.o'.A.hom := IsAbelianScheme.proper (self := Q'.o'.ab)
    have : Smooth Q'.o'.A.hom := IsAbelianScheme.smooth (self := Q'.o'.ab)
    have : LocallyOfFiniteType ((i ≫ Q'.ψ).left ≫ Q'.o'.A.hom) := by
      rw [Over.w]
      infer_instance
    apply Over.OverMorphism.ext
    refine ext_of_apply_eq Q'.o'.A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ ?_ ?_
    · intro pt _ hpt
      let aK : 𝟙_ (Over (Sp K)) ⟶ S :=
        Over.homMk (pointOfClosedPoint S.hom pt hpt) (pointOfClosedPoint_comp S.hom pt hpt)
      let a := aK ≫ i
      have ha : UKer r o₁ Q.ψ _ a := (hiff _ _).2 ⟨aK, rfl⟩
      have hR := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z hz Q a).1
      have hR' := (hPR p D R b N M r w j (p ^ e) T (Sp K) x (x ≫ M.s) o₁ m₁ z' hz' Q' a).1
      have hkw : ES.KilledBy o₁ w a := (Q.tj K (𝟙 _)).1 a ha.1 ha.2
      have hbase : (a.left ≫ m₁.φ) ≫ M.univ.A.hom = x := by
        rw [Category.assoc, m₁.cart.1.w, ← Category.assoc, Over.w a]
        exact Category.id_comp x
      let a₀ : Over.mk x ⟶ M.univ.A := Over.homMk (a.left ≫ m₁.φ) hbase
      have htransport := (hPK p D R b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m₁ m₁
        (𝟙 _) (𝟙 _) (by simp)).1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl a a₀ (by
          rw [eqToHom_refl, Category.id_comp]
          rfl)
      have hzero : a ≫ Q'.ψ = 1 := hR'.2 (hpoint a₀ ((htransport.2.2 w).1 hkw) (hR.1 ha.1))
      have hclosed : aK.left (IsLocalRing.closedPoint K) = pt := pointOfClosedPoint_apply S.hom pt hpt _
      have heq : aK ≫ (i ≫ Q'.ψ) = aK ≫ (1 : S ⟶ Q'.o'.A) := by
        rw [← Category.assoc, show aK ≫ i = a from rfl, hzero]
        simp
      rw [← hclosed]
      exact congrArg (fun f : 𝟙_ (Over (Sp K)) ⟶ Q'.o'.A => f.left (IsLocalRing.closedPoint K)) heq
    · rw [Over.w, Over.w]
  have k1 := kernel_imp y y' hy hy' (fun g hg => (hK g hg).1) P P'
  have k2 := kernel_imp y' y hy' hy (fun g hg => (hK g hg).2) P' P
  have hker : ∀ (U : Over (Sp K)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := by
    intro U g
    constructor
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog
        (fun U g => ⟨k1 U g, k2 U g⟩) U g
    · exact hKU p D R b N r w hw.ne_top hu K (x ≫ M.s) (p ^ e) o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog
        (fun U g => ⟨k2 U g, k1 U g⟩) U g
  obtain ⟨m, hm'⟩ := hIK p D R b N K (x ≫ M.s) (p ^ e) o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hker
  obtain ⟨m'', hm''⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m P'.m'
  have hU := T.univ (Sp K) x o₁ P.o' m₁ P.ψ hpK P.isog P.tj
  have fix : ∀ (f : Sp K ⟶ T.Y) (_ : f = y') (n : GlobalTheory.UPel.HT.ObjMap P.o' T.o' f),
      ∃ n' : GlobalTheory.UPel.HT.ObjMap P.o' T.o' y', n'.φ = n.φ := by
    rintro f rfl n
    exact ⟨n, rfl⟩
  obtain ⟨n', hn'⟩ := fix _ (Category.id_comp y') m''
  refine hU.unique ⟨hy, P.m₀, P.m', P.sq⟩ ⟨hy', P'.m₀, n', ?_⟩
  rw [hn', hm'', ← Category.assoc, hm', P'.sq]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.KerAtLift
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private theorem pt_one_iff (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (e : x₀.left = x.left ≫ φ) : x = 1 ↔ x₀ = 1 := by
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (by rw [e, GlobalTheory.GlueGrpLaw.one_left h T])
  · intro h0
    refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
    · rw [← e, h0, GlobalTheory.GlueGrpLaw.one_left h T]
    · rw [Over.w x, Over.w (1 : T ⟶ G')]

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w : Ideal (𝓞 D.F)} {j c : ℕ}

private theorem kerAt_lift (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a' : Over.mk z ⟶ T.o.A) :
    KerAt T z (a'.left ≫ T.ms.φ) ↔ a' ≫ T.ψ = 1 := by
  refine ⟨fun h => h a' rfl, fun h b hb => ?_⟩
  have : b = a' := Over.OverMorphism.ext (T.ms.cart.1.hom_ext hb (by rw [Over.w b, Over.w a']))
  rw [this]; exact h

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫} {k : ℕ} {T : KS L gb k}
  {N₀ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₀ 𝔟₁} {X₂ : Ext S N₀ 𝔟₂} {𝔴' : Ideal (𝓞 D.F)} {i : ℕ} {h : G.GAf} {M₁ M₂ : Lv p}
  {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}

private theorem ker_read {C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁} {C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂} {W : Wit T h M₁ M₂}
    {f : X₁.Y.X ⟶ X₂.M.X} {mf : ObjMap X₁.Y.univ X₂.M.univ f} {c : ℕ} {Tj : TjD X₂.M r 𝔴' i c} (P : BPt C₁ C₂ W mf Tj)
    {Ω : Type} [Field Ω] (z : Sp Ω ⟶ (T.M M₁).X) (e : 𝟙_ (Over (T.M M₁).X) ⟶ (T.M M₁).univ.A) :
    KerAt Tj (z ≫ P.y) (z ≫ e.left ≫ C₁.m.φ ≫ mf.φ) ↔ toUnit (Over.mk z) ≫ e ≫ W.ψ = 1 := by
  let a' : Over.mk (z ≫ P.y) ⟶ Tj.o.A := Over.homMk (z ≫ e.left ≫ P.fa) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [P.ca.1.w, ← Category.assoc e.left, Over.w e, Over.tensorUnit_hom]
    exact congrArg (z ≫ ·) (Category.id_comp P.y))
  have h1 := kerAt_lift Tj (z ≫ P.y) a'
  have h2 : a'.left ≫ Tj.ms.φ = z ≫ e.left ≫ C₁.m.φ ≫ mf.φ := by
    simp only [a', Over.homMk_left, Category.assoc, P.ms]
  rw [h2] at h1
  rw [h1]
  refine (pt_one_iff P.cb (toUnit (Over.mk z) ≫ e ≫ W.ψ) (a' ≫ Tj.ψ) ?_).symm
  simp only [a', Over.comp_left, Over.homMk_left, Over.toUnit_left, Over.mk_hom, Category.assoc, P.sq]

end

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R} {gb : GBase D.toG R'}
  {N₀ N₁ : ℕ} {𝔟 𝔴' : Ideal (𝓞 D.F)}

private theorem cls_read (hb : 𝔟 ≤ 𝔴') (Y : EtModel b N₀ 𝔟 1) (M : Model b N₀) {f : Y.X ⟶ M.X} (mf : ObjMap Y.univ M.univ f)
    {X : Scheme.{0}} {s : X ⟶ Sp R'} {o : GObj gb N₁ s} {β : R →+* R'} {c : ℕ} {a : 𝓞 D.F} (C : Cls Y β o c a)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X) (g : Over.mk ((x ≫ C.j) ≫ f) ⟶ M.univ.A)
    (hg : ES.KilledBy M.univ 𝔴' g) :
    ∃ d : D.La, ∀ z : Sp Ω ⟶ X, z ≫ C.j = x ≫ C.j → g.left = z ≫ (o.eta d).left ≫ C.m.φ ≫ mf.φ := by
  let g₁ : Over.mk (x ≫ C.j) ⟶ Y.univ.A :=
    Over.homMk (mf.cart.1.lift g.left (x ≫ C.j) (Over.w g)) (by simp)
  have hg₁ : g₁.left ≫ mf.φ = g.left := by simp [g₁]
  have hk : ∀ c ∈ 𝔟 ^ 1, g₁ ≫ Y.univ.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
    refine (pt_one_iff mf.cart _ (g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O c)) ?_).2 (hg c (hb (by simpa using hc)))
    simp only [Over.comp_left, Category.assoc]
    rw [mf.act, ← Category.assoc, hg₁]
  obtain ⟨y, hy⟩ := (Y.isLev.2.2.2 Ω (x ≫ C.j)).2 g₁ hk
  refine ⟨algebraMap (𝓞 D.F) D.O a • y, fun z hz => ?_⟩
  have hl := C.lv y
  rw [← hg₁, ← hy, reassoc_of% hl, reassoc_of% hz]
  simp [Over.toUnit_left]

end

end UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bKer_of :
    SecInjG → TrEtaPt → BKer := by
  intro hS hT
  unfold BKer
  intro p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂ C₁ C₂ W f mf hf
    e he hpos Tj P Ω _ _ x x' hxx'
  have : CharZero Ω :=
    charZero_of_injective_ringHom (Spec.preimage (x ≫ (T.M M₁).s)).hom.injective
  have hb' : 𝔟₁ ≤ 𝔴' := hb.trans Ideal.mul_le_right
  refine hS q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 hSc.m1 r 𝔴' i e hmax hu hi hpos X₂.M Tj Ω ((x ≫ C₁.j) ≫ f)
    (x ≫ P.y) (x' ≫ P.y) ?_ ?_ ?_
  · rw [Category.assoc, Category.assoc, P.ys]
  · rw [Category.assoc, P.ys, ← Category.assoc, hxx', Category.assoc]
  intro g hg
  obtain ⟨d, hd⟩ := cls_read (D := datAt S.atq S.sp) hb' X₁.Y X₂.M mf C₁ x g hg
  have k₁ : KerAt Tj (x ≫ P.y) g.left ↔ toUnit (Over.mk x) ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x rfl]; exact ker_read P x _
  have k₂ : KerAt Tj (x' ≫ P.y) g.left ↔ toUnit (Over.mk x') ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x' hxx'.symm]; exact ker_read P x' _
  exact k₁.trans (((hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x d).1.trans
    (hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x' d).1.symm).trans k₂.symm)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsUnitNatOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem isUnit_nat_of {E : Type} [Field E] [CharZero E] {V : Scheme.{0}} (s : V ⟶ Sp E) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
  have hE : IsUnit ((n : E)) := (Nat.cast_ne_zero.mpr hn).isUnit
  have h1 : IsUnit ((n : Γ(Sp E, ⊤))) := by
    have := hE.map (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
    simpa using this
  have := h1.map s.appTop.hom
  simpa using this

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'}

private theorem qmap_cast {N₁ N c : ℕ} {V Y : Scheme.{0}} {s : V ⟶ Sp R'} {t : Y ⟶ Sp R} {a : GObj gb N₁ s} {u : Obj b N t}
    {f f' : V ⟶ Y} (h : f = f') (n : QMap a u f c) : ∃ n' : QMap a u f' c, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

private theorem rigid_of (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q) {S₁ S₂ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {f f' : S₁ ⟶ S₂}
    (m : ObjMap o₁ o₂ f) (m' : ObjMap o₁ o₂ f') (h : f = f') : m.φ = m'.φ := by
  subst h
  exact (hO q D R b N hN hNq S₁ S₂ S₂ s₁ s₂ s₂ o₁ o₂ o₂ f (𝟙 _)).1 m m'

private theorem read_tj {N : ℕ} {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c) {V : Scheme.{0}}
    (x : V ⟶ M.X) (s₀ : V ⟶ Sp R) (hx : x ≫ M.s = s₀) (o₁ o₂ : Obj b N s₀) (m : ObjMap o₁ M.univ x) (ψ₀ : o₁.A ⟶ o₂.A)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (_ : y ≫ Tj.s = x) (m₀ : ObjMap o₁ Tj.o y) (m₁ : ObjMap o₂ Tj.o' y),
      m₀.φ ≫ Tj.ψ.left = ψ₀.left ≫ m₁.φ := by
  subst hx
  obtain ⟨y, ⟨hy, m₀, m₁, h⟩, -⟩ := Tj.univ V x o₁ o₂ m ψ₀ hu hi ht
  exact ⟨y, hy, m₀, m₁, h⟩

private theorem read_core (hQ : QComp) (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N N₁ N₂ c₁ c₂ : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c)
    {V Y₁ Y₂ : Scheme.{0}} {s : V ⟶ Sp R'} {s₀ : V ⟶ Sp R} {t₁ : Y₁ ⟶ Sp R} {t₂ : Y₂ ⟶ Sp R}
    {a : GObj gb N₁ s} {a' : GObj gb N₂ s} {o₁ o₂ : Obj b N s₀} {u₁ : Obj b N t₁} {u₂ : Obj b N t₂}
    (n₁ : QMap a o₁ (𝟙 V) c₁) (n₂ : QMap a' o₂ (𝟙 V) c₂) {j₁ : V ⟶ Y₁} {j₂ : V ⟶ Y₂}
    (k₁ : QMap a u₁ j₁ c₁) (k₂ : QMap a' u₂ j₂ c₂) {f : Y₁ ⟶ M.X} {π : Y₂ ⟶ M.X}
    (mf : ObjMap u₁ M.univ f) (mπ : ObjMap u₂ M.univ π)
    (hb₁ : (j₁ ≫ f) ≫ M.s = s₀) (hb₂ : (j₂ ≫ π) ≫ M.s = s₀)
    (ψ' : a.A.left ⟶ a'.A.left) (ψ₀ : o₁.A ⟶ o₂.A) (hψ : n₁.φ ≫ ψ₀.left = ψ' ≫ n₂.φ)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (fa : a.A.left ⟶ Tj.o.A.left) (fb : a'.A.left ⟶ Tj.o'.A.left),
      y ≫ Tj.s = j₁ ≫ f ∧ y ≫ Tj.t = j₂ ≫ π ∧ IsGrpPullback a.A Tj.o.A y fa ∧ IsGrpPullback a'.A Tj.o'.A y fb ∧
      fa ≫ Tj.ψ.left = ψ' ≫ fb ∧ fa ≫ Tj.ms.φ = k₁.φ ≫ mf.φ ∧ fb ≫ Tj.mt.φ = k₂.φ ≫ mπ.φ := by
  obtain ⟨k₁', hk₁'⟩ := qmap_cast (Category.id_comp j₁).symm k₁
  obtain ⟨k₂', hk₂'⟩ := qmap_cast (Category.id_comp j₂).symm k₂
  obtain ⟨m₁, hm₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Y₁ s s₀ t₁ a o₁ u₁ (𝟙 V) j₁).2.2.1 inferInstance n₁ k₁'
  obtain ⟨m₂, hm₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Y₂ s s₀ t₂ a' o₂ u₂ (𝟙 V) j₂).2.2.1 inferInstance n₂ k₂'
  obtain ⟨mx, hmx⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mf
  obtain ⟨mz, hmz⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂ mπ
  obtain ⟨y, hy, m₀, m', hsq⟩ := read_tj Tj (j₁ ≫ f) s₀ hb₁ o₁ o₂ mx ψ₀ hu hi ht
  obtain ⟨e₁, he₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m' Tj.mt
  obtain ⟨e₀, he₀⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀ Tj.ms
  have hbt : (y ≫ Tj.t) ≫ M.s = s₀ := by
    rw [Category.assoc, ← Tj.st, ← Category.assoc, hy, hb₁]
  have yt : y ≫ Tj.t = j₂ ≫ π := (M.rep V s₀ o₂).unique ⟨hbt, ⟨e₁⟩⟩ ⟨hb₂, ⟨mz⟩⟩
  obtain ⟨p₁, hp₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Tj.Y s s₀ (Tj.s ≫ M.s) a o₁ Tj.o (𝟙 V) y).1 n₁ m₀
  obtain ⟨p₂, hp₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Tj.Y s s₀ (Tj.s ≫ M.s) a' o₂ Tj.o' (𝟙 V) y).1 n₂ m'
  have r₀ : m₀.φ ≫ Tj.ms.φ = m₁.φ ≫ mf.φ := by
    rw [← he₀, ← hmx]
    exact rigid_of hO hN hNq e₀ mx hy
  have r₁ : m'.φ ≫ Tj.mt.φ = m₂.φ ≫ mπ.φ := by
    rw [← he₁, ← hmz]
    exact rigid_of hO hN hNq e₁ mz yt
  refine ⟨y, n₁.φ ≫ m₀.φ, n₂.φ ≫ m'.φ, hy, yt, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p₁', hp₁'⟩ := qmap_cast (Category.id_comp y) p₁
    have := p₁'.cart
    rw [hp₁', hp₁] at this
    exact this
  · obtain ⟨p₂', hp₂'⟩ := qmap_cast (Category.id_comp y) p₂
    have := p₂'.cart
    rw [hp₂', hp₂] at this
    exact this
  · rw [Category.assoc, hsq, ← Category.assoc, hψ, Category.assoc]
  · rw [Category.assoc, r₀, ← Category.assoc, ← hm₁, hk₁']
  · rw [Category.assoc, r₁, ← Category.assoc, ← hm₂, hk₂']

end

theorem UpperTheory.Gal.FiniteEtaleModels.bRead_of :
    IsogG → QObj → QComp → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → BRead := by
  intro hI hQO hQC hO p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hle hin h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂
    C₁ C₂ W f mf hf e he he0 Tj
  have h3 : 3 ≤ N₀ := X₁.lev.1
  have hcq : N₀.Coprime q := X₁.lev.2.1
  have hM₁ : M₁.1 = N₀ * c₁ := hn₁.1
  have hM₂ : M₂.1 = N₀ * c₂ := hn₂.1
  have pos₁ : 0 < M₁.1 := by have := M₁.2.1; omega
  have pos₂ : 0 < M₂.1 := by have := M₂.2.1; omega
  obtain ⟨o₁, ⟨n₁⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₁.1 N₀ c₁ hM₁ pos₁ hcq _ _ (T.M M₁).univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₂.1 N₀ c₂ hM₂ pos₂ hcq _ _ W.o
  obtain ⟨ψ₀, hψ, hi, ht⟩ := hI p D G L E gb q r 𝔴 𝔴' S.atq S.sp S.std.m1 hmax hu (Ow w) S.b N₀ hcq i e he h 1 htj hint (one_mem _) M₁ M₂ c₁ c₂
    hM₁ hM₂ _ _ (T.M M₁).univ W.o W.ψ (by rw [_root_.mul_one]; exact W.trans) _ o₁ o₂ n₁ n₂
  obtain ⟨k₂, hk₂⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ (T.M M₂).X X₂.Y.X X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s
    (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2 _ (T.M M₁).s W.o W.π W.φ C₂.m
  have hb₁ : (C₁.j ≫ f) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, hf]
    exact C₁.ov
  have hb₂ : ((W.π ≫ C₂.j) ≫ X₂.π) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, Category.assoc, X₂.ov]
    refine (congrArg (W.π ≫ ·) C₂.ov).trans ?_
    simp only [← Category.assoc, W.ov]
  have hun : IsUnit ((q : ℕ) : Γ((T.M M₁).X, ⊤)) := isUnit_nat_of (T.M M₁).s q (Fact.out : q.Prime).ne_zero
  obtain ⟨y, fa, fb, ys, yt, ca, cb, sq, ms, mt⟩ := read_core hQC hO h3 hcq Tj n₁ n₂ C₁.m k₂ mf X₂.mπ hb₁ hb₂ W.ψ.left ψ₀ hψ hun hi ht
  exact ⟨⟨y, ys, by rw [yt, Category.assoc], fa, fb, ca, cb, sq, ms, by rw [mt, hk₂, Category.assoc]⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bezout
set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Form

variable {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)

private lemma skew (alt : ∀ x, B x x = 0) (x y : M) : B x y = - B y x := by
  have h := alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, alt x, alt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

private lemma bezout {e n : ℕ} (hc : e.Coprime n) : ∃ a b : ℤ, a * e + b * n = 1 :=
  Nat.isCoprime_iff_coprime.2 hc

private lemma first {n e : ℕ} (hn : 0 < n) (hc : e.Coprime n) (nd : Function.Injective B)
    (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (x : M) (h : ∀ y, (n : ℤ) ∣ B x y) :
    ∃ z, x = n • z := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let f : M →ₗ[ℤ] ℤ :=
    { toFun := fun y => B x y / n
      map_add' := fun y y' => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_right (h y')
      map_smul' := fun c y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (h y) }
  have hf : ∀ y, (n : ℤ) * f y = B x y := fun y => Int.mul_ediv_cancel' (h y)
  obtain ⟨w, hw⟩ := perf f
  have key : n • w = e • x := by
    apply nd
    ext y
    simp only [map_nsmul, LinearMap.smul_apply, hw, nsmul_eq_mul, ← hf]
    ring
  have key' : (e : ℤ) • x = (n : ℤ) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]
  refine ⟨a • w + b • x, ?_⟩
  calc x = ((a * e + b * n : ℤ)) • x := by rw [hab, one_smul]
    _ = a • ((e : ℤ) • x) + b • ((n : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = n • (a • w + b • x) := by
      rw [key', ← Nat.cast_smul_eq_nsmul ℤ n, smul_add, smul_comm a, smul_comm b]

private lemma second {n e : ℕ} (hc : e.Coprime n) (nd : Function.Injective B)
    (alt : ∀ x, B x x = 0) (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (h : M →+ M) :
    ∃ k : M →+ M, ∀ x y, (n : ℤ) ∣ B (h x) y - B x (k y) := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let F : M → M →ₗ[ℤ] ℤ := fun y => (B.flip y) ∘ₗ h.toIntLinearMap
  have hF : ∀ y x, F y x = B (h x) y := fun y x => rfl
  choose w hw using fun y => perf (F y)
  have wadd : ∀ y y', w (y + y') = w y + w y' := by
    intro y y'
    apply nd
    ext x
    simp only [map_add (f := _), LinearMap.add_apply, hw, LinearMap.smul_apply, hF, smul_add]
  let k : M →+ M := AddMonoidHom.mk' (fun y => -(a • w y)) (by
    intro y y'
    simp only [wadd, smul_add, neg_add])
  refine ⟨k, fun x y => ?_⟩
  have h1 : B x (k y) = a * (e * B (h x) y) := by
    simp only [k, AddMonoidHom.mk'_apply, map_neg, map_zsmul, smul_eq_mul, skew B alt x (w y), hw,
      LinearMap.smul_apply, hF, nsmul_eq_mul]
    ring
  rw [h1]
  exact ⟨b * B (h x) y, by linear_combination (-(B (h x) y)) * hab⟩

private lemma third {n : ℕ} (hn : 0 < n) [Module.Finite ℤ M] (g : M →+ M)
    (inj : ∀ x z, g x = n • z → ∃ w, x = n • w) (x : M) : ∃ y z, g y = x + n • z := by
  classical
  let N : AddSubgroup M := (nsmulAddMonoidHom n).range
  have memN : ∀ y, y ∈ N ↔ ∃ z, n • z = y := fun y => by
    simp [N, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  have hle : N ≤ N.comap g := by
    intro y hy
    obtain ⟨z, rfl⟩ := (memN y).1 hy
    exact (memN _).2 ⟨g z, (map_nsmul g n z).symm⟩
  let G := QuotientAddGroup.map N N g hle
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (M ⧸ N) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨y, rfl⟩
  have ginj : Function.Injective G := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hu
    obtain ⟨z, hz⟩ := (memN _).1 hu
    obtain ⟨w, hw⟩ := inj y z hz.symm
    rw [QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨w, hw.symm⟩
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.1 ginj (QuotientAddGroup.mk x)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hu
  obtain ⟨z, hz⟩ := (memN _).1 hu
  exact ⟨y, -z, by rw [smul_neg, hz]; abel⟩

end Form

theorem adj : UpperTheory.Gal.FiniteEtaleModels.O.Adj := by
  intro q _ D e
  haveI := D.finLa
  obtain ⟨e', he', perf⟩ := D.perfP
  have hc : e'.Coprime (q ^ e) := Nat.Coprime.pow_right e he'
  have hn : 0 < q ^ e := pow_pos (Fact.out : Nat.Prime q).pos e
  have fst : ∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0 := by
    intro x hx
    obtain ⟨z, hz⟩ := first D.EF hn hc D.nondeg perf x hx
    exact ⟨z, by rw [zero_add]; exact hz⟩
  refine ⟨fst, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := second D.EF hc D.nondeg D.alt perf h.toAddMonoidHom
    refine ⟨k, hk, ?_⟩
    intro c y
    obtain ⟨z, hz⟩ := fst (k (c • y) - c • k y) (by
      intro x
      obtain ⟨b', hb'⟩ : ∃ b', MulOpposite.unop (D.star b') = c := ⟨_, D.star_star c⟩
      have e1 := hk x (c • y)
      have e2 := hk (b' • x) y
      have a1 : D.EF (h.toAddMonoidHom (b' • x)) y = D.EF (h.toAddMonoidHom x) (c • y) := by
        rw [LinearMap.toAddMonoidHom_coe, map_smul, D.adj, hb']
      have a2 : D.EF (b' • x) (k y) = D.EF x (c • k y) := by rw [D.adj, hb']
      rw [a1, a2] at e2
      rw [skew D.EF D.alt, map_sub, dvd_neg]
      have h5 := dvd_sub e2 e1
      rwa [sub_sub_sub_cancel_left] at h5)
    exact ⟨z, by rw [zero_add, sub_eq_iff_eq_add'] at hz; exact hz⟩
  · intro g hg
    have ginj : ∀ x z, g x = (q ^ e) • z → ∃ w, x = (q ^ e) • w := by
      intro x z hz
      apply first D.EF hn hc D.nondeg perf x
      intro y
      have h3 := hg x y
      rw [hz, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h2 : ((q ^ e : ℕ) : ℤ) ∣ ((q ^ e : ℕ) : ℤ) * D.EF z (g y) := dvd_mul_right _ _
      have h4 := dvd_sub h2 h3
      rwa [sub_sub_cancel] at h4
    refine ⟨fun x ⟨z, hz⟩ => ?_, fun x => ?_⟩
    · obtain ⟨w, hw⟩ := ginj x z (by rw [hz, zero_add])
      exact ⟨w, by rw [zero_add]; exact hw⟩
    · obtain ⟨y, z, hyz⟩ := third hn g ginj x
      exact ⟨y, z, hyz⟩

end UpperTheory.Gal.FiniteEtaleModels.O
end
