module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 2000000
namespace GlobalTheory.Mem.Col2.RatFrPt
open GlobalTheory.Mem.Col2.PtExist

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def glEquiv (γ : GL (Fin n) E) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinear (Matrix.toLin' (γ : Matrix (Fin n) (Fin n) E)) (Matrix.toLin' ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem glEquiv_apply (γ : GL (Fin n) E) (x : Sp E n) : glEquiv γ x = (γ : Matrix (Fin n) (Fin n) E) *ᵥ x := rfl

theorem glEquiv_single (γ : GL (Fin n) E) (i j : Fin n) : glEquiv γ (Pi.single j 1) i = (γ : Matrix (Fin n) (Fin n) E) i j := by
  rw [glEquiv_apply, Matrix.mulVec_single_one]
  rfl

theorem adAt_inv {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} {γ : GL (Fin n) E}
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s))
    (r s : Fin n) : adAt F P (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) r s) := by
  set M : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) with hM
  have hM' : M = (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (P.adicCompletion E)) := Matrix.ext fun a b => h a b
  have h1 : ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) * M = 1 := by
    rw [hM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E (P.adicCompletion E)) * M = 1 := by
    rw [hM', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e := (Matrix.inv_eq_left_inv h1).symm.trans (Matrix.inv_eq_left_inv h2)
  exact congrFun (congrFun e r) s

variable [StarRing E]

theorem glEquiv_mem_iff {P : HeightOneSpectrum (𝓞 E)} {g : GL (Fin n) (AfE F E)} {γ : GL (Fin n) E}
    (hN : IsSdLat (Formalism.UG.CS.globLat g (stdLat E n)))
    (h : ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s))
    (x : Sp E n) : glEquiv γ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g (stdLat E n)) ↔ x ∈ stdAt E n P := by
  have hi := adAt_inv h
  constructor
  · intro hx
    rw [GlobalTheory.Mem.ColAd.mem_stdAt_val]
    intro i
    have h1 := valued_pullV_le g hx i
    have e : adAt F P (Formalism.L2.Col.pullV g (glEquiv γ x) i) = algebraMap E (P.adicCompletion E) (x i) := by
      have e2 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ glEquiv γ x = x := by
        rw [glEquiv_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      conv_rhs => rw [← e2]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.L2.Col.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, hi, adAt_inclE]
    rwa [e] at h1
  · intro hx
    obtain ⟨f, hf⟩ := CharValCompare.exists_isFr P hN
    have hy : f.symm (glEquiv γ x) ∈ stdAt E n P := by
      rw [GlobalTheory.Mem.ColAd.mem_stdAt_val]
      intro i
      set A : Matrix (Fin n) (Fin n) E := mat f.symm * (γ : Matrix (Fin n) (Fin n) E) with hA
      have hA1 : ∀ j, Valued.v (algebraMap E (P.adicCompletion E) (A i j)) ≤ 1 := by
        intro j
        have hmem : (fun l => (g : Matrix (Fin n) (Fin n) (AfE F E)) l j) ∈
            Formalism.L2.Herm.hatL (F := F) (Formalism.UG.CS.globLat g (stdLat E n)) := by
          apply (carries_globLat g _).2
          apply (mem_latS_std _).2
          intro l
          simp only [Matrix.mulVec, dotProduct]
          rw [← Matrix.mul_apply, Units.inv_mul, Matrix.one_apply]
          split_ifs
          exacts [one_mem _, zero_mem _]
        have h2 := valued_symm_le (u := fun l => (g : Matrix (Fin n) (Fin n) (AfE F E)) l j) hf
          hmem i
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [h, ← map_mul, ← map_sum] at h2
        rw [hA, Matrix.mul_apply]
        exact h2
      have e3 : f.symm (glEquiv γ x) = A *ᵥ x := by
        funext i
        rw [← mat_mulVec, hA, ← Matrix.mulVec_mulVec, glEquiv_apply]
        rfl
      rw [e3]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul]
      exact mul_le_one' (hA1 j) ((GlobalTheory.Mem.ColAd.mem_stdAt_val.1 hx) j)
    have := (hf _).2 hy
    rwa [f.apply_symm_apply] at this
end

theorem exists_isPtOf_of_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → (∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s)) → ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g hg hQ
  choose! γ hγ using hQ
  obtain ⟨p₀, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p₀.deco.1.N := congrArg Deco.N hd
  have hlat : IsSdLat (Formalism.UG.CS.globLat g (stdLat E n)) :=
    hN ▸ ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩
  let p : DecoF E n ST SG Q := ⟨(p₀.deco, fun P => glEquiv (γ P.1)), fun P x => by
    show glEquiv (γ P.1) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p₀.deco.1.N ↔ _
    rw [← hN]
    exact glEquiv_mem_iff hlat (hγ P.1 P.2) x⟩
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    change v ∈ p₀.deco.1.N at hv
    change HasRes P.1 _ (p₀.deco.1.f P v)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · change v ∈ p₀.deco.1.N at hv
    change HasRes P.1 _ (p₀.deco.1.be P v i)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · show _ = algebraMap E _ (glEquiv (γ P.1) (Pi.single j 1) i)
    rw [glEquiv_single]
    exact hγ P.1 P.2 i j

end GlobalTheory.Mem.Col2.RatFrPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM.BaseMdl

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
  {S : Type} [CommRing S] {x' : Sp S ⟶ X'}

theorem prod_left_congr {B T : Scheme.{0}} {G : Over B} [GrpObj G] {a b : T ⟶ B} (h : a = b) {n : ℕ}
    (u : Fin n → (Over.mk a ⟶ G)) (u' : Fin n → (Over.mk b ⟶ G)) (hu : ∀ i, (u i).left = (u' i).left) :
    (List.ofFn u).prod.left = (List.ofFn u').prod.left := by
  subst h
  rw [show u = u' from funext fun i => Over.OverMorphism.ext (hu i)]

theorem epsMul_comp (c : S) :
    spMap (epsMul c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  have e : (epsMul c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
    ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← e]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem fst_comp :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext s; simp
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  simp

theorem one_push : (1 : Over.mk x' ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x' ≫ f) ⟶ t.G).left :=
  congrArg (fun q => q.left) (map_one (pushHom m.cart (Over.mk x')))

theorem prod_push {n : ℕ} (u : Fin n → (tEpsG x' ⟶ t'.G)) (u' : Fin n → (tEpsG (x' ≫ f) ⟶ t.G))
    (h : ∀ i, (u' i).left = (u i).left ≫ m.φ) :
    (List.ofFn u).prod.left ≫ m.φ = (List.ofFn u').prod.left := by
  have e : (List.ofFn u).prod.left ≫ m.φ =
      (List.ofFn fun i => pushPt m.cart.1.w (u i)).prod.left :=
    congrArg (fun q => q.left) ((map_list_prod (pushHom m.cart (tEpsG x')) _).trans (by rw [List.map_ofFn]; rfl))
  exact e.trans (prod_left_congr (Category.assoc _ _ _) _ _ fun i => (h i).symm)

theorem tan_push {v : Sp (DualNumber S) ⟶ t'.G.left}
    (hv : v ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') :
    IsTanAtG t' x' v ↔ IsTanAtG t (x' ≫ f) (v ≫ m.φ) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hv, Category.assoc]
    · rw [← Category.assoc, h.2, one_push]
  · intro h
    refine ⟨hv, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]
      exact h.2.trans (one_push m).symm
    · rw [Category.assoc, hv, ← Category.assoc, fst_comp, Category.id_comp]
      exact (Over.w (1 : Over.mk x' ⟶ t'.G)).symm

theorem exists_lift {w : Sp (DualNumber S) ⟶ t.G.left}
    (hw : w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ≫ f) :
    ∃ v : Sp (DualNumber S) ⟶ t'.G.left, v ≫ m.φ = w ∧ v ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' :=
  ⟨m.cart.1.lift w _ (hw.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩

theorem comb_push {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)}
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') (cf : Fin n → S)
    {w : Sp (DualNumber S) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') :
    IsCombAtG t' x' v cf w ↔ IsCombAtG t (x' ≫ f) (fun i => v i ≫ m.φ) cf (w ≫ m.φ) := by
  have hs : ∀ i, (spMap (epsMul (cf i)) ≫ v i) ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' := fun i => by
    rw [Category.assoc, hv, ← Category.assoc, epsMul_comp]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => Over.homMk ((u i).left ≫ m.φ) ?_, fun i => ?_, (prod_push m u _ fun i => rfl).symm⟩
    · show ((u i).left ≫ m.φ) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ≫ f
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, hu, hs, Category.assoc]
    · show (u i).left ≫ m.φ = _
      rw [hu, Category.assoc]
  · rintro ⟨u, hu, hp⟩
    let u' : Fin n → (tEpsG x' ⟶ t'.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ v i) (hs i)
    refine ⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · exact (prod_push m u' u fun i => (hu i).trans (Category.assoc _ _ _).symm).trans hp
    · exact (Over.w (List.ofFn u').prod).trans hw.symm


end Push

section Generic

theorem away_of_valuation (F : Type) [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (V : ValuationSubring F) (p : ℕ)
    (hp : p.Prime) (hV : (p : F) ∈ V.nonunits) : IsLocalization.Away ((p : ℕ) : V) F := by
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hm : ((p : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := ValuationSubring.coe_mem_nonunits_iff.1 (by simpa using hV)
  have key : ∀ x : F, ∃ (k : ℕ) (a : V), x * (p : F) ^ k = a := by
    intro x
    have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨n, hn, hi⟩ := hx.exists_integral_multiple
    have hi' : IsIntegral ℤ ((n.natAbs : ℤ) • x) := by
      rcases Int.natAbs_eq n with h | h
      · rw [← h]; exact hi
      · rw [show (n.natAbs : ℤ) = -n by omega, neg_smul]; exact hi.neg
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 hi'.tower_top
    obtain ⟨e, n', hn', he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hn) p hp.ne_one
    have hu : IsUnit ((n' : ℕ) : V) := by
      by_contra h
      have h' : ((n' : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := h
      have hc : IsCoprime ((p : ℕ) : V) ((n' : ℕ) : V) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').cast
      obtain ⟨a, b, hab⟩ := hc
      exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ h')))
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    have hw' : (w : F) * (n' : F) = 1 := by simpa using congrArg (fun z : V => (z : F)) hw
    refine ⟨e, w * y, ?_⟩
    have hy' : (y : F) = (p : F) ^ e * n' * x := by
      rw [show (y : F) = algebraMap V F y from rfl, hy, he]; simp
    push_cast
    rw [hy']
    linear_combination (-(x * (p : F) ^ e)) * hw'
  refine IsLocalization.Away.mk _ ?_ (fun s => ?_) fun a b h => ⟨0, by rw [Subtype.val_injective h]⟩
  · rw [map_natCast]; exact IsUnit.mk0 _ hp0
  · rw [map_natCast]; exact key s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isOpenImmersion_j {p : ℕ} {W : ValuationSubring ℂ} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  have := c.fin
  have hV : (p : c.F) ∈ (c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c.F.val.toRingHom (p : c.F)⁻¹ ∈ W := h
    simpa using h2
  have := away_of_valuation c.F (c.V W) p hp hV
  have : IsOpenImmersion (spMap (c.V W).subtype) := IsOpenImmersion.of_isLocalization (S := c.F) ((p : ℕ) : c.V W)
  have := Y.jQ_open
  unfold Model.j
  infer_instance

theorem dense_j {O : Type} [CommRing O] {β : O →+* c.F} (hβ : Function.Injective β) (Y : Model Xo c β) :
    Dense (Set.range Y.j) := by
  have := Y.flat
  have h1 : DenseRange (pullback.fst Y.s (spMap β)) := by
    intro x
    let q : Sp c.F := (⊥ : PrimeSpectrum c.F)
    have hs : spMap β q ⤳ Y.s x := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      show Ideal.comap β ⊥ ≤ _
      rw [Ideal.comap_bot_of_injective _ hβ]
      exact bot_le
    obtain ⟨x', hx', e⟩ := Flat.generalizingMap Y.s hs
    refine closure_mono ?_ (specializes_iff_mem_closure.1 hx')
    rw [Set.singleton_subset_iff, Scheme.Pullback.range_fst]
    exact ⟨q, e.symm⟩
  have := h1.comp Y.jQ_dense (pullback.fst Y.s (spMap β)).continuous
  refine this.mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t, Scheme.Hom.comp_apply _ _ _⟩

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

end GlobalTheory.LocM.BaseMdl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChange
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

theorem GlobalTheory.ShFam.EigFrame.exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z A B _ _ φ x fr ψ
  open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
  have h : GlobalTheory.LocM.IsFrame Z.t (ψ.comp φ) (spMap ψ ≫ x) ((fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i)) := by
    letI : Algebra c.F A := φ.toAlgebra
    letI : Algebra c.F B := (ψ.comp φ).toAlgebra
    let v : ∀ τ, Fin (Dw.mult τ) → TanM x Z.t.G := fun τ i => tanOf (fr.tan τ i)
    have eps_dual (a : A) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, smul_eq_mul, mul_comm]
    have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
        spMap (epsMul ((ψ.comp φ) (embK c τ a))) ≫ (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i := fun τ i a => by
      show (spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i
      rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
    have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
      exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
    have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM ψ (v k.1 k.2) := by
      have h := full_equiv (eB Dw).symm (full_bc ψ (full_equiv (eB Dw) h1))
      exact (funext fun k => congrArg (fun j : IxB Dw => resM ψ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
    refine ⟨fun τ i => ⟨isTan_map ψ rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
    have h3 := eig_of_full c (fun τ i => resM ψ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
      ((eig_iff c τ _).1 hwe)
    exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM ψ (v τ i)) a (tanOf hw)).2 h3
  exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj
set_option maxSynthPendingDepth 32
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet in
private theorem eigFrame_isComb_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {x : Sp S ⟶ X}
    {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → S) (w : TanM x t.G) :
    IsCombAtG t x (fun i => (tv (u i)).left) a (tv w).left ↔ w = ∑ i, a i • u i := by
  have e : tv (∑ i, a i • u i) = combT x (fun i => tv (u i)) a := by
    classical
    unfold combT
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, tv_add, ih]; rfl
  refine (isCombAtG_iff t x (fun i => tv (u i)) a _).trans ?_
  rw [← e]
  exact ⟨fun h => (tan_ext h).symm, fun h => h ▸ rfl⟩

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigFrame_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (A B : Type) [CommRing A] [CommRing B] (φ : c.F →+* A) (x : Sp A ⟶ Z.X) (fr : EigFrame Z φ x) (ψ : A →+* B), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z A B _ _ φ x fr ψ
  open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.LocM.FrameBC in
  have h : GlobalTheory.LocM.IsFrame Z.t (ψ.comp φ) (spMap ψ ≫ x) ((fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i)) := by
    letI : Algebra c.F A := φ.toAlgebra
    letI : Algebra c.F B := (ψ.comp φ).toAlgebra
    let v : ∀ τ, Fin (Dw.mult τ) → TanM x Z.t.G := fun τ i => tanOf (fr.tan τ i)
    have eps_dual (a : A) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]
    have he : ∀ τ i (a : 𝓞 E), (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i ≫ (Z.t.act.act a).left =
        spMap (epsMul ((ψ.comp φ) (embK c τ a))) ≫ (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) τ i := fun τ i a => by
      show (spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i) ≫ _ = _ ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ fr.v τ i
      rw [Category.assoc, fr.eig τ i a, ← Category.assoc, eps_dual, Category.assoc, RingHom.comp_apply]
    have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (fr.eig τ i)) fun τ n hn => by
      exact (existsUnique_congr fun a => eigFrame_isComb_iff (v τ) a n).1 (fr.basis τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
    have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM ψ (v k.1 k.2) := by
      have h := full_equiv (eB Dw).symm (full_bc ψ (full_equiv (eB Dw) h1))
      exact (funext fun k => congrArg (fun j : IxB Dw => resM ψ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
    refine ⟨fun τ i => ⟨isTan_map ψ rfl (fr.tan τ i), he τ i⟩, fun τ w hw hwe => ?_⟩
    have h3 := eig_of_full c (fun τ i => resM ψ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
      ((eig_iff c τ _).1 hwe)
    exact (existsUnique_congr fun a => eigFrame_isComb_iff (fun i => resM ψ (v τ i)) a (tanOf hw)).2 h3
  exact ⟨⟨_, fun τ i => (h.1 τ i).1, fun τ i => (h.1 τ i).2, h.2⟩, fun _ _ => rfl⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatOfQuasiFiniteOfFlatFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_quasiFinite_of_flat_fibres' : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] [Algebra.QuasiFinite A B] [Module.Flat R B], (∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C), (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) → Module.Flat A B := by
  first | exact @GlobalTheory.flat_of_quasiFinite_of_flat_fibres | exact GlobalTheory.flat_of_quasiFinite_of_flat_fibres | (intros; apply GlobalTheory.flat_of_quasiFinite_of_flat_fibres <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbMulFlat

open FibreFlat FiniteFibreFlat


set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : LocallyQuasiFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Algebra.QuasiFinite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  refine GlobalTheory.T.flat_of_quasiFinite_of_flat_fibres' R A B fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

theorem flat_and_locallyQuasiFinite_pow :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 →
      Flat ((𝟙 G) ^ q : G ⟶ G).left ∧ LocallyQuasiFinite ((𝟙 G) ^ q : G ⟶ G).left := by
  intro S G _ _ hG n hn
  change Flat (Out.mulA G n).left ∧ LocallyQuasiFinite (Out.mulA G n).left
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have hm := AbLaw.MulN.isMonHom_mulA G n
  have : LocallyOfFiniteType ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType (Out.mulA G n).left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact ((Out.mulA G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact (Out.mulA G n).left := QuasiCompact.of_comp _ G.hom
  have hq : LocallyQuasiFinite (Out.mulA G n).left :=
    locallyQuasiFinite_of_finite_geometric_ker _ G G _ hm inferInstance inferInstance fun K _ _ t => by
      simp only [IntDiv.comp_mulA]
      exact HomExt.finite_torsion_points hG t (Nat.pos_of_ne_zero hn)
  refine ⟨flat_of_flatOver_fields _ G.hom inferInstance (by rw [Over.w]; infer_instance)
    (by rw [Over.w]; infer_instance) hq fun k _ t => ?_, hq⟩
  exact flatOver_of_pullback _ _ (IntDiv.flat_fibre G _ k t)

end GlobalTheory.SemiAbMulFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_flat_locallyQuasiFinite : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 → Flat ((𝟙 G) ^ q : G ⟶ G).left ∧ LocallyQuasiFinite ((𝟙 G) ^ q : G ⟶ G).left := by
  first | exact @GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow | exact GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow | (intros; apply GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_prime (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

theorem residueCharacteristic_mem (v : HeightOneSpectrum (𝓞 F)) : ((resP v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem ioOf_le_one_iff (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (hv : (p : 𝓞 F) ∈ v.asIdeal) (ε : Ext v) :
    ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F (AlgebraicClosure F) v ε.O hv
    (GlobalTheory.TrueGeo.ExtConj.lies_over ε)
  have h : ∃ io : AlgebraicClosure F →+* ℂ_[p], ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O :=
    ⟨(algebraMap (PadicAlgCl p) ℂ_[p]).comp j, fun a => by
      rw [hj, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]⟩
  exact Classical.epsilon_spec h

theorem log_w_eq (p : ℕ) [hp : Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (io : AlgebraicClosure F →+* ℂ_[p]) (h : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) (a : AlgebraicClosure F) :
    Real.log (ε.w a) = (-Real.log (ε.w p) / Real.log p) * Real.log ‖io a‖ := by
  let u : AbsoluteValue (AlgebraicClosure F) ℝ := (NormedField.toAbsoluteValue ℂ_[p]).comp io.injective
  have hu (x) : u x = ‖io x‖ := rfl
  have he : u.IsEquiv ε.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have h1 : u x⁻¹ ≤ 1 ↔ ε.w x⁻¹ ≤ 1 := by rw [hu, h, ε.mem_O]
      rw [map_inv₀, map_inv₀, inv_le_one₀ (u.pos hx), inv_le_one₀ (ε.w.pos hx)] at h1
      rw [← not_le, ← not_le, h1]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hw (x) : Real.log (ε.w x) = c * Real.log ‖io x‖ := by
    rw [← congrFun hce x, hu]
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Real.zero_rpow hc.ne']
    · exact Real.log_rpow (norm_pos_iff.2 ((map_ne_zero io).2 hx)) c
  have hn : ‖io p‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  rw [hw, hw, hn, Real.log_inv]
  field_simp

theorem ioOf_spec : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v), ∃ hp : (resP v).Prime, haveI := Fact.mk hp; (∀ a, ‖ioOf (resP v) ε a‖ ≤ 1 ↔ a ∈ ε.O) ∧ ∀ a, Real.log (ε.w a) = (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log ‖ioOf (resP v) ε a‖ := fun _ _ _ v ε =>
  ⟨residueCharacteristic_prime v, by
    haveI := Fact.mk (residueCharacteristic_prime v)
    exact ⟨ioOf_le_one_iff _ (residueCharacteristic_mem v) ε, log_w_eq _ ε _ (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε)⟩⟩

end GlobalTheory.ShFam.Pad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.CoordComp

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)


open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem comb_comb {S : Type} [CommRing S] [IsLocalRing S] {x : Sp S ⟶ X} {m n : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j))
    {w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j))
    {u : Sp (DualNumber S) ⟶ t.G.left} (hu : IsTanAtG t x u) (B : Fin n → Fin m → S) (a : Fin n → S)
    (h1 : ∀ i, IsCombAtG t x v (B i) (w i)) (h2 : IsCombAtG t x w a u) :
    IsCombAtG t x v (fun k => ∑ j, a j * B j k) u := by
  obtain ⟨d, xc, hx⟩ := GlobalTheory.ShFam.EigLoc.exists_chart t x
  choose p hp using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hv j)
  choose q hq using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hw j)
  obtain ⟨r, rfl⟩ := GlobalTheory.LieLocBasis.vec_exists hx _ hu
  obtain rfl : v = _ := funext hp
  obtain rfl : w = _ := funext hq
  simp only [GlobalTheory.LieLocBasis.comb_iff hx] at h1 h2 ⊢
  rw [h2]
  simp only [h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem spMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := (spMap_comp' _ _).symm

theorem dualMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  by
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMap]

end GlobalTheory.ShFam.CoordComp


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.CoordComp in
theorem GlobalTheory.ShFam.CoordComp.coord_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (g : EigFrame Z φ' x') (R'' : Type) [CommRing R''] (φ'' : c.F →+* R'') (x'' : Sp R'' ⟶ Z.X) (h : EigFrame Z φ'' x'') (ψ : R →+* R') (ψ' : R' →+* R'') (A : Mat Dw.mult R') (A' : Mat Dw.mult R''), IsLocalRing R'' → f.Coord ψ g A → g.Coord ψ' h A' → f.Coord (ψ'.comp ψ) h (A' * A.map ψ') := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' g R'' _ φ'' x'' h ψ ψ' A A' hl h₁ h₂
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  subst a1 a2 b1 b2
  refine ⟨by rw [spMap_comp2, Category.assoc], rfl, fun τ i => ?_⟩
  have e : (fun k => spMap (dualMap (ψ'.comp ψ)) ≫ f.v τ k) =
      fun k => spMap (dualMap ψ') ≫ spMap (dualMap ψ) ≫ f.v τ k :=
    funext fun k => by rw [dualMap_comp2, spMap_comp2, Category.assoc]
  rw [e]
  exact comb_comb Z.t
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)))
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (g.tan τ j)) (h.tan τ i) (fun j k => ψ' (A τ j k)) (A' τ i)
    (fun j => comb_map Z.t ψ' (a3 τ j)) (b3 τ i)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesCompStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_eigenspace_frame_coordinates_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (g : EigFrame Z φ' x') (R'' : Type) [CommRing R''] (φ'' : c.F →+* R'') (x'' : Sp R'' ⟶ Z.X) (h : EigFrame Z φ'' x'') (ψ : R →+* R') (ψ' : R' →+* R'') (A : Mat Dw.mult R') (A' : Mat Dw.mult R''), IsLocalRing R'' → f.Coord ψ g A → g.Coord ψ' h A' → f.Coord (ψ'.comp ψ) h (A' * A.map ψ') := by
  first | exact @GlobalTheory.ShFam.CoordComp.coord_comp | exact GlobalTheory.ShFam.CoordComp.coord_comp | (intros; apply GlobalTheory.ShFam.CoordComp.coord_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PtComp

theorem disjoint_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hsm : Smooth f)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  refine CompSplitPfD.cspD_disj (fun x => ?_) Z Z' hZ hZ' hne
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have h1 := HasRingHomProperty.appLE (P := @Smooth) f hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp)
  let ψ : K →+* Γ(X, V) :=
    (f.appLE ⊤ V (fun p _ => by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) K) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) K) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem connectedComponent_mem {X : Type} [TopologicalSpace X] (hfin : (irreducibleComponents X).Finite)
    (hd : ∀ Z ∈ irreducibleComponents X, ∀ Z' ∈ irreducibleComponents X, Z ≠ Z' → Disjoint Z Z') (z : X) :
    connectedComponent z ∈ irreducibleComponents X ∧ IsOpen (connectedComponent z) := by
  have hV := irreducibleComponent_mem_irreducibleComponents z
  have hU : irreducibleComponent z = (⋃ W ∈ irreducibleComponents X \ {irreducibleComponent z}, W)ᶜ := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hp W hW hpW
      exact Set.disjoint_left.1 (hd _ hW.1 _ hV hW.2) hpW hp
    · intro hp
      by_contra hpZ
      exact hp _ ⟨irreducibleComponent_mem_irreducibleComponents p,
        fun h => hpZ ((show irreducibleComponent p = _ from h) ▸ mem_irreducibleComponent)⟩ mem_irreducibleComponent
  have ho : IsOpen (irreducibleComponent z) := by
    rw [hU]
    exact ((hfin.subset Set.diff_subset).isClosed_biUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents _ hW.1).isOpen_compl
  have e : connectedComponent z = irreducibleComponent z :=
    ((IsClopen.connectedComponent_subset ⟨isClosed_irreducibleComponent, ho⟩ mem_irreducibleComponent)).antisymm
      irreducibleComponent_subset_connectedComponent
  rw [e]
  exact ⟨hV, ho⟩

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem preimage_connectedComponent_mem (Z : Model Xo c β) (hsm : Smooth (genStr Z)) (z : gen Z) :
    Z.jQ ⁻¹' connectedComponent z ∈ irreducibleComponents (Xo.XF c) := by
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  obtain ⟨h1, h2⟩ := connectedComponent_mem TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => disjoint_of_smooth (genStr Z) hsm W W' hW hW') z
  have := Z.jQ_open
  exact preimage_mem_irreducibleComponents h1 Z.jQ.isOpenEmbedding
    (Z.jQ_dense.inter_open_nonempty _ h2 ⟨z, mem_connectedComponent⟩)

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem exists_equiv : ∃ q : s.Comp ≃ Comp (S.Xo κ.l) κ.c, ∀ k z,
    OnComp s k z ↔ (q k).1 = s.T.Z.jQ ⁻¹' connectedComponent z := by
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  have hne : ∀ k, ((s.U κ.σ₀).X k).dom.Nonempty := fun k => GlobalTheory.OrbitScalar.exists_mem_dom _
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp _ _ _ _ _ _ κ.σ₀ N (s.U κ.σ₀) hσ (s.unf _ hσ).1 hne s.geo
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q, fun k z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨x, hx⟩
    by_contra hn
    let pt : Sp (CAt κ.σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ (q k)
      ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩ fun e => hn (congrArg Subtype.val e)) (hq k x pt) (hx pt)
  · obtain ⟨x, hx⟩ := hne k
    refine ⟨⟨x, hx⟩, fun pt => ?_⟩
    have := hq k ⟨x, hx⟩ pt
    rw [h] at this
    exact this

theorem existsUnique_onComp (z : gen s.T.Z) : ∃! k, OnComp s k z := by
  obtain ⟨q, hq⟩ := exists_equiv s
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q.symm ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩, (hq _ _).2 (by rw [Equiv.apply_symm_apply]),
    fun k hk => ?_⟩
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext ((hq _ _).1 hk)

theorem onComp_compPt (y : Pt s) (pt : Sp Qb) : OnComp s (compPt s y) (y.y pt) := by
  obtain ⟨k, hk, -⟩ := existsUnique_onComp s (y.y pt)
  have : ∃ k, ∀ pt', OnComp s k (y.y pt') :=
    ⟨k, fun pt' => (Subsingleton.elim (α := PrimeSpectrum Qb) pt pt') ▸ hk⟩
  exact Classical.epsilon_spec this pt

end GlobalTheory.ShFam.PtComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionInvariantFrameFunction
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.KeyRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_sameLie {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {e : Ix Dw → ℤ} (he : e none = 0)
    {g : Rul Xo c} (hg : g ∈ GlobalTheory.AllWt.secZ Xo c e) {y y' : FrPt Xo c S} (h : SameLie y y') :
    evR Xo c g y' = evR Xo c g y := by
  obtain ⟨g0, a, -, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 h.1.symm
  have h1 := (GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.1 y
  let T : Ix Dw → Sˣ := fun k => k.elim a fun _ => 1
  have hb : FrBor T y y' := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 T y y').2
    ⟨fun _ => 1, fun τ i => Matrix.one_apply_eq i, fun τ i j hij => Matrix.one_apply_ne hij.ne, hc.1,
      fun τ i => h.2 τ i ▸ h1.2.1 τ i, hc.2.2⟩
  rw [GlobalTheory.FlagTan.evR_frBor hg hb, Fintype.prod_option, he, zpow_zero, _root_.one_mul]
  simp [T]

end GlobalTheory.ShFam.KeyRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntFam

def IntegralCharts {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι) : Prop :=
  ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
    p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))

end GlobalTheory.IntFam
end
end
