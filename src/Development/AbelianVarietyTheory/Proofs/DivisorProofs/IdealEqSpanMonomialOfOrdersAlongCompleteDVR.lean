module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
noncomputable section

open IsLocalRing GlobalTheory.Toroidal

namespace GlobalTheory.MonoVal

theorem eq_span_monomial_of_forall_cdvr (k : Type) [Field k] [CharZero k] (m e : ℕ) (I : Ideal (ChartRing k m e))
    (a : Fin m → ℕ)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : ChartRing k m e →+* W,
      Function.Injective ψ → IsLocalHom ψ → I.map ψ = Ideal.span {ψ (∏ i, bdParam k m e i ^ a i)}) :
    I = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  set q : ChartRing k m e := ∏ i, bdParam k m e i ^ a i with hqdef
  haveI : CharZero (ChartRing k m e) := (MvPowerSeries.constantCoeff : ChartRing k m e →+* k).charZero
  obtain ⟨hN, hIC, -, -⟩ := GlobalTheory.ChartCone.isCN_chartRing k m e
  haveI := hN
  haveI := hIC
  have hX : ∀ j : Fin m ⊕ Fin e, (MvPowerSeries.X j : ChartRing k m e) ≠ 0 := by
    intro j hj
    have := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hj
    simp [MvPowerSeries.coeff_X] at this
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hX _)
  have loc_of : ∀ {V : Type} [CommRing V] [IsLocalRing V] (φ : ChartRing k m e →+* V),
      (maximalIdeal V).comap φ = maximalIdeal (ChartRing k m e) → IsLocalHom φ := by
    intro V _ _ φ hφ
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hx' : x ∈ maximalIdeal (ChartRing k m e) := hnu
    rw [← hφ, Ideal.mem_comap] at hx'
    exact hx' hx

  have hle : I ≤ Ideal.span {q} := by
    intro f hf
    rw [Ideal.mem_span_singleton]
    refine GlobalTheory.ValCrit.dvd_of_forall_cdvr _ f q hq0 fun V _ _ _ φ hV hinj hφ => ?_
    have hm := h V hV φ hinj (loc_of φ hφ)
    rw [← Ideal.mem_span_singleton, ← hm]
    exact Ideal.mem_map_of_mem φ hf
  refine le_antisymm hle ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  by_contra hqI
  let I' : Ideal (ChartRing k m e) := Submodule.comap (LinearMap.mulLeft (ChartRing k m e) q) I
  have hmemI' : ∀ g, g ∈ I' ↔ q * g ∈ I := fun g => Iff.rfl
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ψ : ChartRing k m e →+* V),
      GlobalTheory.LN.CDvr V → Function.Injective ψ → IsLocalHom ψ → False := by
    intro V _ _ _ ψ hV hinj hψ
    have hmap := h V hV ψ hinj hψ
    have hI : I = Ideal.span {q} * I' := by
      apply le_antisymm
      · intro f hf
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 (hle hf)
        exact Ideal.mem_span_singleton_mul.2 ⟨g, (hmemI' g).2 (by rwa [mul_comm]), mul_comm _ _⟩
      · rw [Ideal.span_singleton_mul_le_iff]
        intro z hz
        exact (hmemI' z).1 hz
    have hψq : ψ q ≠ 0 := (map_ne_zero_iff ψ hinj).2 hq0
    have htop : Ideal.map ψ I' = ⊤ := by
      have h2 : Ideal.span {ψ q} * Ideal.map ψ I' = Ideal.span {ψ q} * ⊤ := by
        have h3 : Ideal.map ψ (Ideal.span {q} * I') = Ideal.span {ψ q} * Ideal.map ψ I' := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
        rw [Ideal.mul_top, ← h3, ← hI, hmap]
      exact (Ideal.span_singleton_mul_right_inj hψq).1 h2
    have hI'ne : I' ≠ ⊤ := by
      intro ht
      apply hqI
      have h1 : (1 : ChartRing k m e) ∈ I' := ht ▸ Submodule.mem_top
      simpa using (hmemI' 1).1 h1
    have hle' : Ideal.map ψ I' ≤ maximalIdeal V := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' := IsLocalRing.le_maximalIdeal hI'ne hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx'
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx' (isUnit_of_map_unit ψ x hu)
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (htop ▸ hle'))
  rcases isEmpty_or_nonempty (Fin m ⊕ Fin e) with hσ | hne
  ·
    let ψ0 : ChartRing k m e →+* PowerSeries k :=
      (PowerSeries.C : k →+* PowerSeries k).comp (MvPowerSeries.constantCoeff : ChartRing k m e →+* k)
    have hc : ∀ f : ChartRing k m e, f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      intro f
      ext n
      have hn : n = 0 := Subsingleton.elim _ _
      subst hn
      simp
    have hinj : Function.Injective ψ0 := by
      intro f g hfg
      have h1 : MvPowerSeries.constantCoeff f = MvPowerSeries.constantCoeff g := by
        simpa [ψ0] using congrArg PowerSeries.constantCoeff hfg
      rw [hc f, hc g, h1]
    have hloc : IsLocalHom ψ0 := by
      refine ⟨fun f hf => ?_⟩
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      have h1 : IsUnit (PowerSeries.constantCoeff (ψ0 f)) := hf.map _
      simpa [ψ0] using h1
    exact key (PowerSeries k) ψ0 (GlobalTheory.FrameGen.cDvr_powerSeries k) hinj hloc
  · obtain ⟨j⟩ := hne
    have hdvd : (MvPowerSeries.X j : ChartRing k m e) ∣ 1 :=
      GlobalTheory.ValCrit.dvd_of_forall_cdvr _ 1 _ (hX j) fun V _ _ _ φ hV hinj hφ =>
        (key V φ hV hinj (loc_of φ hφ)).elim
    have hu := isUnit_of_dvd_one hdvd
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
    simp at hu

end GlobalTheory.MonoVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKappaLengthBounds
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.CovSz

theorem ceil_mul_le_pow {y PP Dd k m : ℝ} (hy : 2 ≤ y) (hP0 : 0 ≤ PP) (hP : PP ≤ y) (hD0 : 0 ≤ Dd) (hD : Dd ≤ y ^ 2)
    (hk0 : 0 ≤ k) (hk : k ≤ y) (hm : 1 ≤ m) : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 9 := by
  have h0 : 0 ≤ PP ^ 2 * Dd ^ 2 * k := by positivity
  have h1 : PP ^ 2 * Dd ^ 2 * k ≤ y ^ 7 := by
    calc PP ^ 2 * Dd ^ 2 * k ≤ y ^ 2 * (y ^ 2) ^ 2 * y := by gcongr
      _ = y ^ 7 := by ring
  have h2 : PP ^ 2 * Dd ^ 2 * k / m ≤ y ^ 7 := (div_le_self h0 hm).trans h1
  have h3 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) < PP ^ 2 * Dd ^ 2 * k / m + 1 :=
    Nat.ceil_lt_add_one (div_nonneg h0 (by linarith))
  have h4 : 1 ≤ y ^ 7 := one_le_pow₀ (by linarith)
  have h5 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) ≤ y ^ 8 := by
    have : y ^ 8 = y ^ 7 * y := by ring
    nlinarith
  calc (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 8 * y := by gcongr
    _ = y ^ 9 := by ring

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem kap_le {PP : ℝ} (hW : WtNum p i PP) : CovTop.kap p i ≤ (D.R.f : ℝ) * D.R.r * (4 * L.sc.b) := by
  have hc : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by
    rw [← hW.card, Nat.card_eq_fintype_card]
  have hr : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  unfold CovTop.kap sizeK
  calc _ ≤ ∑ _τ : Psi p.T.Q.H, ∑ _k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.up τ k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hc, hr]; ring

theorem kapT_at {PP A : ℝ} (hH : HostNum D L PP A 18) (hW : WtNum p i PP) :
    Real.log (CovTop.kap p i) ≤ 2 * L.sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt L.sc.b := by
  obtain ⟨-, hL, -, -⟩ := hH.big
  obtain ⟨-, hPy, hfy⟩ := hH.poly
  have hroom := hH.room
  have hlow := hH.ppLow
  set y := L.sc.x ^ A with hy
  have hroom' : y ^ 18 ≤ L.sc.b := by
    have : y ^ (18 : ℝ) = y ^ (18 : ℕ) := by exact_mod_cast Real.rpow_natCast y 18
    rwa [this] at hroom
  have hm2 := D.R.two_le_m
  have hkm := D.R.m_add_three_le_k
  have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by omega
  have hn1 : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hr1' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hn1' : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hn1
  have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
  have hm' : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hfr : (8 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have h10 : (D.R.f : ℝ) * D.R.r * 10 ≤ y := by
    refine le_trans ?_ hfy
    calc (D.R.f : ℝ) * D.R.r * 10 = (D.R.f : ℝ) * D.R.r * 1 * 10 := by ring
      _ ≤ _ := by gcongr
  have hy2 : 2 ≤ y := by linarith
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hyb : y ≤ L.sc.b := (le_self_pow₀ (by linarith) (by norm_num)).trans hroom'
  have hP0 : 0 ≤ PP := le_trans (Even.pow_nonneg (by decide) _) hlow
  refine ⟨?_, ?_⟩
  · have hk := kap_le p i hW
    have hk0 : 0 ≤ CovTop.kap p i :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hk2 : CovTop.kap p i ≤ Real.exp (2 * L.sc.L) := by
      have e : Real.exp (2 * L.sc.L) = L.sc.b * L.sc.b := by
        unfold Scale.b; rw [← Real.exp_add]; ring_nf
      rw [e]
      nlinarith
    rcases hk0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h).2 hk2
  · have hch : (D.R.r.choose 2 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow D.R.r 2
    have hD : (CompHt.dimFlag (dat p i) : ℝ) ≤ y ^ 2 := by
      rw [hW.dim]; push_cast
      calc (D.R.f : ℝ) * (D.R.r.choose 2 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 := by
            gcongr; nlinarith
        _ = ((D.R.f : ℝ) * D.R.r) ^ 2 := by ring
        _ ≤ y ^ 2 := by gcongr; linarith
    have hky : (D.R.k : ℝ) ≤ y := by nlinarith
    have h9 := ceil_mul_le_pow hy2 hP0 hPy (Nat.cast_nonneg _) hD (Nat.cast_nonneg _) hky hm'
    refine h9.trans (Real.le_sqrt_of_sq_le ?_)
    calc (y ^ 9) ^ 2 = y ^ 18 := by ring
      _ ≤ _ := hroom'

end Point

end GlobalTheory.CovTop.CovSz

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.Sat

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (s : Sp B ⟶ Sp A) : ∃ u : A →+* B, spMap u = s :=
  ⟨(Spec.preimage s).hom, Spec.map_preimage s⟩

theorem isDominant_gp (X : Scheme.{0}) [IsIntegral X] : IsDominant (gp X) := by
  constructor
  have h : genericPoint X ∈ Set.range (gp X) :=
    ⟨closedPoint (X.presheaf.stalk (genericPoint X)), Scheme.fromSpecStalk_closedPoint⟩
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_closure X
  exact h2.mono (Set.singleton_subset_iff.mpr h)

theorem pff_id {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {φ : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) φ θ) : gp Y ≫ φ = spMap θ ≫ gp X := by
  obtain ⟨l, h1, h2⟩ := h
  rw [Category.comp_id] at h1
  rw [← h1, h2]

theorem transfer (σ : Setup) (E : Emb σ) (hC : σ.Common) (x x' : Sp σ.R) (Ω : Type) [Field Ω]
    (s : Sp Ω ⟶ Sp (σ.C x).R) (s' : Sp Ω ⟶ Sp (σ.C x').R) (o : Sp Ω) (hs' : s' o = closedPoint (σ.C x').R)
    (h : s ≫ spMap (σ.ρ x) = s' ≫ spMap (σ.ρ x')) :
    (∀ t : Sp Ω ⟶ (σ.C x).G.left, t ≫ (σ.C x).G.hom = s →
      ∃ t' : Sp Ω ⟶ (σ.C x').G.left, t' ≫ (σ.C x').G.hom = s' ∧ t' ≫ E.emb x' = t ≫ E.emb x) ∧
    (∀ t' : Sp Ω ⟶ (σ.C x').G.left, t' ≫ (σ.C x').G.hom = s' →
      ∃ t : Sp Ω ⟶ (σ.C x).G.left, t ≫ (σ.C x).G.hom = s ∧ t ≫ E.emb x = t' ≫ E.emb x') := by
  obtain ⟨u, rfl⟩ := sp_surj s
  obtain ⟨u', rfl⟩ := sp_surj s'
  have hk : RingHom.ker u' = maximalIdeal _ := by
    obtain rfl : o = closedPoint Ω := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    have h1 : (maximalIdeal Ω).comap u' = maximalIdeal _ := congrArg PrimeSpectrum.asIdeal hs'
    rw [← h1, maximalIdeal_eq_bot]; rfl
  rw [sp_comp, sp_comp] at h
  obtain ⟨R', _, _, _, a, b, v, H, _, _, πa, πb, θa, θb, -, -, hab, -, hva, hvb, -, -, ⟨pa, -⟩, ⟨pb, -⟩, fa, fb, hθ⟩ :=
    hC x x' Ω u u' hk (sp_inj h)
  have key : πa ≫ E.emb x = πb ≫ E.emb x' := by
    haveI := E.sep
    haveI := isDominant_gp H.left
    obtain ⟨w, -⟩ := E.openIn x
    obtain ⟨w', -⟩ := E.openIn x'
    refine ext_of_isDominant_of_isSeparated E.p ?_ (gp H.left) ?_
    · rw [Category.assoc, Category.assoc, w, w', pa.w_assoc, pb.w_assoc, sp_comp, sp_comp, hab]
    · rw [← Category.assoc, ← Category.assoc, pff_id fa, pff_id fb, Category.assoc, Category.assoc,
        pff_id (E.ff x), pff_id (E.ff x'), ← Category.assoc, ← Category.assoc, sp_comp, sp_comp,
        ← RingHom.comp_assoc, ← RingHom.comp_assoc, hθ]
  have ea : spMap v ≫ spMap a = spMap u := by rw [sp_comp, hva]
  have eb : spMap v ≫ spMap b = spMap u' := by rw [sp_comp, hvb]
  constructor
  · intro t ht
    refine ⟨pa.lift t (spMap v) (ht.trans ea.symm) ≫ πb, ?_, ?_⟩
    · rw [Category.assoc, pb.w, pa.lift_snd_assoc, eb]
    · rw [Category.assoc, ← key, pa.lift_fst_assoc]
  · intro t ht
    refine ⟨pb.lift t (spMap v) (ht.trans eb.symm) ≫ πa, ?_, ?_⟩
    · rw [Category.assoc, pa.w, pb.lift_snd_assoc, ea]
    · rw [Category.assoc, key, pb.lift_fst_assoc]

theorem exists_field_pt {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (h : f x = g y) :
    ∃ (Ω : Type) (_ : Field Ω) (s : Sp Ω ⟶ X) (t : Sp Ω ⟶ Y) (o : Sp Ω), s ≫ f = t ≫ g ∧ s o = x ∧ t o = y := by
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y h
  let r : Sp ((pullback f g).residueField z) ⟶ pullback f g := (pullback f g).fromSpecResidueField z
  let o : Sp ((pullback f g).residueField z) := closedPoint _
  have hr : r o = z := Scheme.fromSpecResidueField_apply z _
  refine ⟨(pullback f g).residueField z, inferInstance, r ≫ pullback.fst f g, r ≫ pullback.snd f g, o, ?_, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition]
  · rw [Scheme.Hom.comp_apply, hr, h1]
  · rw [Scheme.Hom.comp_apply, hr, h2]

end GlobalTheory.Desc.Sat

namespace GlobalTheory.Desc


open Sat in
theorem Emb.fst_mem_U_iff : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ (x : Sp σ.R) (w : ↥(Limits.pullback E.p (spMap (σ.ρ x)))), (Limits.pullback.fst E.p (spMap (σ.ρ x)) w ∈ E.U ↔ ∃ y : (σ.C x).G.left, E.emb x y = Limits.pullback.fst E.p (spMap (σ.ρ x)) w ∧ (σ.C x).G.hom y = Limits.pullback.snd E.p (spMap (σ.ρ x)) w) := by
  intro σ E hC x w
  constructor
  · rintro ⟨x', y', hy', e⟩
    obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ := exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') w y' e.symm
    obtain ⟨w', -⟩ := E.openIn x'
    obtain ⟨t, h1, h2⟩ := (transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
      (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
      (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
    refine ⟨t o, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, ht, e]
    · rw [← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply, hs]
  · rintro ⟨y, e, -⟩
    rw [← e]
    let x' : Sp σ.R := ((σ.C x).G.hom ≫ spMap (σ.ρ x)) y
    have hx' : spMap (σ.ρ x') (closedPoint _) = x' := by rw [← σ.hρ]; exact (σ.C x').centre
    obtain ⟨Ω, _, t, s', o, hst, ht, hs⟩ :=
      exists_field_pt ((σ.C x).G.hom ≫ spMap (σ.ρ x)) (spMap (σ.ρ x')) y (closedPoint _) hx'.symm
    obtain ⟨t', h1, h2⟩ := (transfer σ E hC x x' Ω (t ≫ (σ.C x).G.hom) s' o hs
      (by rw [Category.assoc, hst])).1 t rfl
    refine ⟨x', t' o, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, h1, hs]
    · rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, ht]

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleOneOnThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleOneOnThickening
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

theorem exists_unit_lift_of_surj_closedImm {X X₀ : Scheme.{0}} (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i]
    (W : X.Opens) (hW : IsAffineOpen W) (u : Γ(X₀, i ⁻¹ᵁ W)ˣ) : ∃ s : Γ(X, W)ˣ, pullU i W s = u := by
  obtain ⟨v, hv⟩ := i.app_surjective W hW u.val
  have hunit : IsUnit v := X.toRingedSpace.isUnit_of_isUnit_germ W v fun x hx => by
    obtain ⟨y, rfl⟩ := Surjective.surj (f := i) x
    have h1 : IsUnit ((i.stalkMap y).hom ((X.presheaf.germ W (i y) hx).hom v)) := by
      rw [Scheme.Hom.germ_stalkMap_apply, hv]; exact u.isUnit.map _
    exact isUnit_of_map_unit _ _ h1
  exact ⟨hunit.unit, Units.ext hv⟩

theorem mul_twist_eq_of_cocycle {G : Type*} [CommGroup G] (A B C E F S T : G) (h1 : A * B = F) (h2 : C * E = F) :
    A * S = C * (S⁻¹ * B * T)⁻¹ * (E * T) := by
  rw [eq_mul_inv_of_mul_eq h1, eq_mul_inv_of_mul_eq h2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_cocycle_one_on_thickening : ∀ (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i]
    (c : Pic X), GlobalTheory.CechPic.pull i c = 0 →
    ∃ (D : LB X) (hD : D.IsLB), cls D hD = c ∧ ∀ a b, pullU i _ (D.g a b) = 1 := by
  intro X X₀ i _ _ c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL i (pull_isLB hL i)] at hc
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  let ι' := {q : X.affineOpens × L.ι // (q.1 : X.Opens) ≤ L.U q.2}
  let W : ι' → X.Opens := fun q => q.1.1
  let J : ι' → L.ι := fun q => q.1.2
  have hle : ∀ q : ι', i ⁻¹ᵁ W q ≤ (L.pull i).U (fun _ => J q) := fun q y hy => mem_pull.2 (q.2 hy)
  choose s hs using fun q : ι' =>
    exists_unit_lift_of_surj_closedImm i (W q) q.1.1.2 (res (hle q) (t.s (fun _ => J q)))
  have l1 : ∀ q q' : ι', W q ⊓ W q' ≤ L.U (J q) ⊓ L.U (J q') := fun q q' => inf_le_inf q.2 q'.2
  let gg : ∀ q q' : ι', Γ(X, W q ⊓ W q')ˣ := fun q q' =>
    (res inf_le_left (s q))⁻¹ * res (l1 q q') (L.g (J q) (J q')) * res inf_le_right (s q')
  let D : LB X := ⟨ι', W, gg⟩
  have gD : ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (q q' : ι'), f y ∈ W q → f y ∈ W q' →
      gm f y (W q ⊓ W q') (D.g q q') =
        (gm f y (W q) (s q))⁻¹ * gm f y (L.U (J q) ⊓ L.U (J q')) (L.g (J q) (J q')) * gm f y (W q') (s q') := by
    intro Y f y q q' h h'
    have hm : f y ∈ W q ⊓ W q' := ⟨h, h'⟩
    show gm f y _ ((res _ (s q))⁻¹ * res _ (L.g (J q) (J q')) * res _ (s q')) = _
    rw [map_mul, map_mul, map_inv, gm_res f y _ hm, gm_res f y _ hm, gm_res f y _ hm]
  have hD : D.IsLB := {
    cover := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨j, hj⟩ := exists_chart hL x
      obtain ⟨V, hV, hxV, hVle⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hj
      exact Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, j), hVle⟩, hxV⟩
    g_self := fun q => unit_ext fun y hy => by
      rw [gm_res _ y _ hy, gD X (𝟙 X) y q q hy hy, gm_self hL (𝟙 X) y (q.2 hy), map_one]
      group
    cocycle := fun a b c => unit_ext fun y hy => by
      have ha : y ∈ W a := hy.1.1
      have hb : y ∈ W b := hy.1.2
      have hc : y ∈ W c := hy.2
      rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gD X (𝟙 X) y a b ha hb,
        gD X (𝟙 X) y b c hb hc, gD X (𝟙 X) y a c ha hc,
        ← gm_cocycle hL (𝟙 X) y (a.2 ha) (b.2 hb) (c.2 hc)]
      group
      rfl }
  refine ⟨D, hD, ?_, fun a b => ?_⟩
  · refine (cls_eq_iff hD hL).2 ⟨⟨fun p => res (le_inf inf_le_left (inf_le_right.trans p.2.2) :
        L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2)) (L.g p.1 (J p.2)) * res inf_le_right (s p.2)⟩, ?_⟩
    refine (isGen_iff_germ _).2 fun y p p' hp hp' => ?_
    have val : ∀ p : L.ι × ι', y ∈ L.U p.1 ⊓ W p.2 → gm (𝟙 X) y (L.U p.1 ⊓ W p.2)
        (res (le_inf inf_le_left (inf_le_right.trans p.2.2) : L.U p.1 ⊓ W p.2 ≤ L.U p.1 ⊓ L.U (J p.2))
          (L.g p.1 (J p.2)) * res inf_le_right (s p.2)) =
        gm (𝟙 X) y _ (L.g p.1 (J p.2)) * gm (𝟙 X) y (W p.2) (s p.2) := fun p h => by
      rw [map_mul, gm_res _ y _ h, gm_res _ y _ h]
    show gm (𝟙 X) y (L.U p.1 ⊓ W p.2) _ = gm (𝟙 X) y (L.U p.1 ⊓ W p.2 ⊓ (L.U p'.1 ⊓ W p'.2)) ((LB.div L D).g p p') *
      gm (𝟙 X) y (L.U p'.1 ⊓ W p'.2) _
    dsimp only
    erw [val p hp, val p' hp', gm_div D L (𝟙 X) y p p' ⟨hp, hp'⟩, gD X (𝟙 X) y p.2 p'.2 hp.2 hp'.2]
    exact mul_twist_eq_of_cocycle _ _ _ _ _ _ _ (gm_cocycle hL (𝟙 X) y hp.1 (p.2.2 hp.2) (p'.2.2 hp'.2))
      (gm_cocycle hL (𝟙 X) y hp.1 hp'.1 (p'.2.2 hp'.2))
  · apply unit_ext
    intro y hy
    have hsa : ∀ q : ι', i y ∈ W q → gm i y (W q) (s q) = gm (𝟙 X₀) y _ (t.s (fun _ => J q)) := fun q h => by
      have e := gm_pull (𝟙 X₀) i y (W q) h (s q)
      rw [Category.id_comp] at e
      rw [← e, hs q, gm_res (𝟙 X₀) y (hle q) h]
    have ha : i y ∈ W a := hy.1
    have hb : i y ∈ W b := hy.2
    have eg := gm_pull_g L i (𝟙 X₀) y (fun _ => J a) (fun _ => J b) (hle a ha) (hle b hb)
    rw [Category.id_comp] at eg
    have e := gm_pull (𝟙 X₀) i y (W a ⊓ W b) hy (D.g a b)
    rw [Category.id_comp] at e
    rw [e, gD X₀ i y a b ha hb, map_one, hsa a ha, hsa b hb, ← eg,
      (isGen_iff_germ t).1 ht y _ _ (hle a ha) (hle b hb)]
    group

end GlobalTheory.CechPic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleOneOnThickeningStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechCocycle_one_on_thickening : ∀ (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] (c : Pic X), GlobalTheory.CechPic.pull i c = 0 → ∃ (D : LB X) (hD : D.IsLB), cls D hD = c ∧ ∀ a b, pullU i _ (D.g a b) = 1 := by
  first | exact @GlobalTheory.CechPic.exists_cocycle_one_on_thickening | exact GlobalTheory.CechPic.exists_cocycle_one_on_thickening | (intros; apply GlobalTheory.CechPic.exists_cocycle_one_on_thickening <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualTangentBasisPulledCotangentChartFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualTangentBasisPulledCotangentChartFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals.DualBasis

open GlobalTheory.LieVB GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.Pdiv (LieG ptMap dualScale specO)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem fst_of_isTangent {w : epsR R ⟶ G} (hw : IsTangent w) :
    ptMap (TrivSqZeroExt.fstHom R R R) ≫ (w : specO R (DualNumber R) ⟶ G) = toUnit (specO R R) ≫ η[G] := by
  have h : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  ext1
  simp only [Over.comp_left, h]
  exact hw.trans (Category.id_comp _).symm

theorem isTangent_val (x : LieG G) : IsTangent (G := G) x.1 := sec_epsZero_comp x

theorem exists_prod [QuasiSeparated G.hom] (l : List (LieG G)) :
    ∃ p : LieG G, p.1 = (l.map (·.1)).prod ∧ tangent p = (l.map tangent).sum := by
  induction l with
  | nil =>
    refine ⟨⟨1, ?_⟩, rfl, ?_⟩
    · exact comp_one _
    · refine dual_ext fun W _ s => ?_
      have e : cotMap (1 : specO R (DualNumber R) ⟶ G) (epsZero_comp ⟨1, comp_one _⟩) = 0 := cotMap_eq_zero rfl _
      rw [List.map_nil, List.sum_nil]
      exact (congr((epsIso R).hom.app W (($e).app W s))).trans (map_zero _)
  | cons x l ih =>
    obtain ⟨p, hp, hp'⟩ := ih
    refine ⟨⟨x.1 * p.1, OmegaGlobal.fst_mul x p⟩, by simp [hp], ?_⟩
    rw [tangent_mul, hp', List.map_cons, List.sum_cons]

theorem isLieComb_iff [QuasiSeparated G.hom] {n : ℕ} (a : Fin n → R) (v : Fin n → LieG G) (w : LieG G) :
    IsLieComb (G := G) a (fun i => (v i).1) w.1 ↔ tangent w = ∑ i, cst R (a i) • tangent (v i) := by
  let u : Fin n → LieG G := fun i => ⟨ptMap (dualScale (a i)) ≫ (v i).1, OmegaGlobal.fst_scale (a i) (v i)⟩
  have hu (i : Fin n) : (u i).1.left = spMap (epsScaleR (a i)) ≫ (v i).1.left := by
    have ha : (dualScale (a i)).toRingHom = epsScaleR (a i) := by
      ext y <;> simp [dualScale, epsScaleR]
    exact congrArg (fun r => spMap r ≫ (v i).1.left) ha
  obtain ⟨p, hp, hp'⟩ := exists_prod (List.ofFn u)
  rw [List.map_ofFn] at hp hp'
  rw [List.sum_ofFn] at hp'
  have hs : tangent p = ∑ i, cst R (a i) • tangent (v i) :=
    hp'.trans (Finset.sum_congr rfl fun i _ => tangent_scale (a i) (v i) _)
  constructor
  · rintro ⟨u', hu', e⟩
    obtain rfl : u' = fun i => (u i).1 := funext fun i => Over.OverMorphism.ext ((hu' i).trans (hu i).symm)
    obtain rfl : w = p := Subtype.ext (e.trans hp.symm)
    exact hs
  · intro e
    obtain rfl : w = p := tangent_injective R G (e.trans hs.symm)
    exact ⟨fun i => (u i).1, hu, hp⟩

theorem exists_dual_of_isFrame [QuasiSeparated G.hom] {n : ℕ} {e : Fin n → Γ(omega G, ⊤)} (he : IsFrame e) :
    ∃ v : Fin n → LieG G, (∀ j k, dualApp (tangent (v j)) le_top (e k) = if j = k then 1 else 0) ∧
      IsLieBasis (G := G) fun j => (v j).1 := by
  choose v hv using fun j => TangentSurj.tangent_surjective R G (he.coord j)
  refine ⟨v, fun j k => ?_, fun j => isTangent_val (v j), fun w hw => ?_⟩
  · have h := he.dualApp_coord_frame j k le_rfl
    rw [Twist.resM_self] at h
    rw [hv]
    exact h.trans (if_congr eq_comm rfl rfl)
  · have hc : Function.Bijective (cst R) := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv
    let b := he.dual.basis le_rfl
    have hb (j : Fin n) : b j = tangent (v j) := by
      rw [hv]
      exact (IsFrame.basis_apply _ _ _).trans (Twist.resM_self _ _)
    have key (a : Fin n → R) := isLieComb_iff a v ⟨w, fst_of_isTangent hw⟩
    simp only [← hb] at key
    choose a ha using fun j => hc.2 (b.repr (tangent ⟨w, fst_of_isTangent hw⟩) j)
    refine ⟨a, (key a).2 ?_, fun a' h' => funext fun j => hc.1 ?_⟩
    · simp only [ha]
      exact (b.sum_repr _).symm
    · rw [ha, (key a').1 h', b.repr_sum_self]

theorem exists_isDual : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R : Type) [CommRing R]
    (ξ : Sp R ⟶ S), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ⊤ ≤ ξ ⁻¹ᵁ c.U →
    ∃ y : Fin g → (epsR R ⟶ KeyVals.bG G ξ), KeyVals.IsDual c ξ y ∧ IsLieBasis y := by
  intro S G _ g c R _ ξ hG _ hc
  have h := isGrpPullback_pullback G ξ
  have : QuasiSeparated (bG G ξ).hom := MorphismProperty.of_isPullback h.1 inferInstance
  have h₁ := ((c.isFrame.pullback ξ).res hc).map_iso (omegaBase h)
  have hf : IsFrame (pfr c ξ hc) := by
    convert h₁ using 2 with k
    exact congrArg _ (QCoh.res_pullbackSections ξ _ le_rfl hc (c.e k)).symm
  obtain ⟨v, hv, hb⟩ := exists_dual_of_isFrame hf
  exact ⟨fun j => (v j).1, ⟨hc, fun j => ⟨v j, rfl, hv j⟩⟩, hb⟩

end GlobalTheory.KeyVals.DualBasis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualTangentBasisPulledCotangentChartFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R : Type) [CommRing R]
    (ξ : Sp R ⟶ S), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → ⊤ ≤ ξ ⁻¹ᵁ c.U →
    ∃ y : Fin g → (epsR R ⟶ KeyVals.bG G ξ), KeyVals.IsDual c ξ y ∧ IsLieBasis y := by
  first | exact @GlobalTheory.KeyVals.DualBasis.exists_isDual | exact GlobalTheory.KeyVals.DualBasis.exists_isDual | (intros; apply GlobalTheory.KeyVals.DualBasis.exists_isDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelations
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftRatios

theorem appLE_rs {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U') (y : Γ(Y, U)) :
    (f.appLE U' V' h').hom (rs Y hU y) = rs X hV ((f.appLE U V h).hom y) := by
  change (Y.presheaf.map (homOfLE hU).op ≫ f.appLE U' V' h').hom y =
    (f.appLE U V h ≫ X.presheaf.map (homOfLE hV).op).hom y
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem app_cst_comp {R : Type} [CommRing R] {X X' : Scheme.{0}} (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (V : X.Opens) (r : R) : (φ.app V).hom (cst f V r) = cst (φ ≫ f) (φ ⁻¹ᵁ V) r := by
  have e := Scheme.Hom.appLE_comp_appLE φ f ⊤ V (φ ⁻¹ᵁ V) (by simp) le_rfl
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e

theorem preimage_injective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : Surjective f) {U U' : Y.Opens}
    (h : f ⁻¹ᵁ U = f ⁻¹ᵁ U') : U = U' := by
  refine SetLike.ext fun y => ?_
  obtain ⟨z, rfl⟩ := hf.surj y
  rw [← Scheme.Hom.mem_preimage, ← Scheme.Hom.mem_preimage, h]

theorem mem_of_appLE_mem (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ)
    (V : (Y (e + 1)).left.Opens) (hV : IsAffineOpen V) (W : (Y e).left.Opens) (hW : β e ⁻¹ᵁ V = W)
    (x : Γ((Y (e + 1)).left, V)) (hx : ((β e).appLE V W hW.ge).hom x ∈ towerIdeal Y e I W) :
    x ∈ towerIdeal Y (e + 1) I V := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app] at hx
  obtain ⟨-, -, hk⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) _ _ ((Y (e + 1)).hom ≫ thick R I (e + 1)) (β e) (Y e).hom
    ((GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e)
  obtain ⟨hs, hker⟩ := hk V hV
  have hc : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hmap : Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V) = towerIdeal Y e I (β e ⁻¹ᵁ V) := by
    unfold towerIdeal
    rw [Ideal.map_map]
    congr 1
    ext r
    rw [RingHom.comp_apply, app_cst_comp, hc]
  have hx' : x ∈ Ideal.comap ((β e).app V).hom (Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V)) := by
    rw [hmap]
    exact hx
  rw [Ideal.comap_map_of_surjective _ hs] at hx'
  have hle : Ideal.comap ((β e).app V).hom ⊥ ≤ towerIdeal Y (e + 1) I V := by
    intro y hy
    have hy' : y ∈ RingHom.ker ((β e).app V).hom := hy
    rw [hker] at hy'
    exact Ideal.map_mono (Ideal.pow_le_self (Nat.succ_ne_zero e)) hy'
  exact SetLike.le_def.1 (sup_le le_rfl hle) hx'

theorem lifted_ratios_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j) ∧ (∀ e i, C.ρ e i i - 1 ∈ towerIdeal Y e I (C.D e i)) ∧ ∀ e i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i l) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ρ e j l) ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  intro R _ I Y β hβ n C
  have hsur : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
  have h1 : ∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j := by
    intro e
    induction e with
    | zero => exact C.basic
    | succ e ih =>
      intro i j
      refine preimage_injective (β e) (hsur e) ?_
      have hb := Scheme.basicOpen_appLE (β e) (C.D e i) (C.D (e + 1) i) (C.pre e i).ge (C.ρ (e + 1) i j)
      rw [C.ρ_pull, ih] at hb
      rw [Scheme.Hom.preimage_inf, C.pre, C.pre, hb]
      exact (inf_eq_right.2 ((Scheme.Hom.preimage_mono (β e) (Scheme.basicOpen_le _ _)).trans
        (C.pre e i).le)).symm
  refine ⟨h1, ?_, ?_⟩
  · intro e
    induction e with
    | zero =>
      intro i
      rw [C.ρ_self, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i
      refine mem_of_appLE_mem R I Y β hβ e _ (C.aff (e + 1) i) _ (C.pre e i) _ ?_
      rw [map_sub, map_one, C.ρ_pull]
      exact ih i
  · intro e
    induction e with
    | zero =>
      intro i j l
      rw [C.cocycle, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i j l
      have hV : IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := by
        rw [← h1 (e + 1) i j]
        exact (C.aff (e + 1) i).basicOpen _
      have hW : β e ⁻¹ᵁ (C.D (e + 1) i ⊓ C.D (e + 1) j) = C.D e i ⊓ C.D e j := by
        rw [Scheme.Hom.preimage_inf, C.pre, C.pre]
      refine mem_of_appLE_mem R I Y β hβ e _ hV _ hW _ ?_
      rw [map_sub, map_mul, appLE_rs (β e) _ inf_le_left (C.pre e i).ge, appLE_rs (β e) _ inf_le_left (C.pre e i).ge,
        appLE_rs (β e) _ inf_le_right (C.pre e j).ge, C.ρ_pull, C.ρ_pull, C.ρ_pull]
      exact ih i j l

end GlobalTheory.FormalAlg.LiftRatios
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTower_liftedRatios_projective_relations : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j) ∧ (∀ e i, C.ρ e i i - 1 ∈ towerIdeal Y e I (C.D e i)) ∧ ∀ e i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i l) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ρ e j l) ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  first | exact @GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod | exact GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod | (intros; apply GlobalTheory.FormalAlg.LiftRatios.lifted_ratios_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg.LevSurj

theorem appLE_cst {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (V : X'.Opens) (h : V ≤ g ⁻¹ᵁ U) (a : R) :
    (g.appLE U V h).hom (AbLaw.cst f U a) = AbLaw.cst (g ≫ f) V a := by
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  change ((X.presheaf.map (homOfLE le_top).op ≫ g.appLE U V h).hom) _ =
    ((g.appTop ≫ X'.presheaf.map (homOfLE le_top).op).hom) _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem appLE_of_eq {X X' : Scheme.{0}} (g : X' ⟶ X) (U : X.Opens) (V : X'.Opens) (hV : g ⁻¹ᵁ U = V)
    (h : V ≤ g ⁻¹ᵁ U) (hs : Function.Surjective (g.app U).hom) :
    Function.Surjective (g.appLE U V h).hom ∧ RingHom.ker (g.appLE U V h).hom = RingHom.ker (g.app U).hom := by
  subst hV
  have : g.appLE U (g ⁻¹ᵁ U) h = g.app U := by simp [Scheme.Hom.appLE]
  rw [this]
  exact ⟨hs, rfl⟩

end GlobalTheory.FormalAlg.LevSurj

namespace GlobalTheory.FormalAlg.LevSurj

theorem ev_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  intro R _ I Y β hβ n C
  have h1 : ∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    intro e V
    rw [towerIdeal, show thick R I e = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) from rfl,
      cst_comp_spec, ← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]
  refine ⟨h1, fun e i => ?_⟩
  induction e with
  | zero =>
    have hc : AbLaw.cst ((Y 0).hom ≫ thick R I 0) (C.D 0 i) =
        (AbLaw.cst (Y 0).hom (C.D 0 i)).comp (Ideal.Quotient.mk _) := cst_comp_spec _ _ _
    have : C.ev 0 i = (MvPolynomial.eval₂Hom (AbLaw.cst (Y 0).hom (C.D 0 i)) (C.ρ 0 i)).comp
        (MvPolynomial.map (Ideal.Quotient.mk _)) := by
      ext <;> simp [Charts.ev, hc]
    rw [this]
    exact (C.surj i).comp (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  | succ e ih =>
    have hp : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
      rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
    have hev : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom.comp (C.ev (e + 1) i) = C.ev e i := by
      rw [Charts.ev, MvPolynomial.comp_eval₂Hom, Charts.ev]
      congr 1
      · ext a
        simp only [RingHom.comp_apply]
        rw [appLE_cst]
        exact congrArg (fun q => AbLaw.cst q (C.D e i) a) (by simpa only [Category.assoc] using hp)
      · funext j
        exact C.ρ_pull e i j
    have hk := (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left ((Y (e + 1)).hom ≫ thick R I (e + 1))
      (β e) (Y e).hom ((GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e)).2.2 (C.D (e + 1) i) (C.aff (e + 1) i)
    obtain ⟨hr, hker⟩ := appLE_of_eq (β e) (C.D (e + 1) i) (C.D e i) (C.pre e i) (C.pre e i).ge hk.1
    rw [hk.2] at hker
    set r := ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom with hr_def
    set c := AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i) with hc_def
    set S := (C.ev (e + 1) i).range with hS_def
    have hsq : ∀ x y, x ∈ RingHom.ker r → y ∈ RingHom.ker r → x * y = 0 := by
      intro x y hx hy
      rw [hker] at hx hy
      have hxy := Ideal.mul_mem_mul hx hy
      rw [← Ideal.map_mul, ← pow_add] at hxy
      have hle : (I ^ (e + 1 + (e + 1))).map c ≤ (I ^ (e + 1 + 1)).map c :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      have h0 : (I ^ (e + 1 + 1)).map c = ⊥ := h1 (e + 1) (C.D (e + 1) i)
      have := hle hxy
      rw [h0] at this
      exact (Submodule.mem_bot _).1 this
    have hsplit : ∀ b, ∃ s ∈ S, b - s ∈ RingHom.ker r := by
      intro b
      obtain ⟨P, hP⟩ := ih (r b)
      refine ⟨C.ev (e + 1) i P, ⟨P, rfl⟩, ?_⟩
      rw [RingHom.mem_ker, map_sub, ← hP, ← hev, RingHom.comp_apply, sub_self]
    have hKS : ∀ x ∈ RingHom.ker r, x ∈ S := by
      intro x hx
      have hx' := hx
      rw [hker] at hx'
      change x ∈ Submodule.span _ _ at hx'
      induction hx' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, -, rfl⟩ := hy
        exact ⟨MvPolynomial.C a, by simp [Charts.ev, c]⟩
      | zero => exact S.zero_mem
      | add y z hy hz ihy ihz =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        have hz' : z ∈ RingHom.ker r := hker ▸ hz
        exact S.add_mem (ihy hy') (ihz hz')
      | smul a y hy ihy =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        obtain ⟨s, hs, has⟩ := hsplit a
        have : a • y = s * y + (a - s) * y := by rw [smul_eq_mul]; ring
        rw [this, hsq _ _ has hy', add_zero]
        exact S.mul_mem hs (ihy hy')
    intro b
    obtain ⟨s, hs, hbs⟩ := hsplit b
    have : b ∈ S := by
      have := S.add_mem hs (hKS _ hbs)
      rwa [add_sub_cancel] at this
    exact this

end GlobalTheory.FormalAlg.LevSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  first | exact @GlobalTheory.FormalAlg.LevSurj.ev_surjective | exact GlobalTheory.FormalAlg.LevSurj.ev_surjective | (intros; apply GlobalTheory.FormalAlg.LevSurj.ev_surjective <;> assumption)
end
end
