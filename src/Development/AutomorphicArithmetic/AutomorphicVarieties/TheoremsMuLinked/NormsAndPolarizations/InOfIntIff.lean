module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.OElRep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.InOfIntIff
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem inOf_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem inOf_div {l : ℕ} [Fact l.Prime] (c : Coef l) (a b : c.O) (hb : (b : PadicAlgCl l) ≠ 0)
    (h : ‖(a : PadicAlgCl l)‖ ≤ ‖(b : PadicAlgCl l)‖) : (a : PadicAlgCl l) / b ∈ c.O := by
  refine (coefSup l).2.2.2 c _ ((inOf_intIff _).2 ?_) ⟨a, b, hb, div_mul_cancel₀ _ hb⟩
  rw [norm_div]
  exact div_le_one_of_le₀ h (norm_nonneg _)

private theorem inOf_fin {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l)) (hs : ∀ x ∈ s, ‖x‖ ≤ 1) :
    ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x ∈ s, x ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨d, hd, hd'⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    obtain ⟨e, he, he'⟩ := (coefSup l).2.2.1 d a ((inOf_intIff _).2 (hs a (Finset.mem_insert_self _ _)))
    refine ⟨e, hd.trans he, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact he'
    · exact he (hd' x hx)

theorem UpperTheory.V.Th.Nm.inOf :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l), (∀ (ι : Type) [Finite ι] (x : ι → Qbar l), (∀ i, ‖x i‖ ≤ 1) → ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ i, x i ∈ c'.O) ∧ (∀ x ∈ c.O, ‖x‖ ≤ 1) ∧ (∀ x ∈ c.O, ‖x‖ = 1 → ∀ h : x ∈ c.O, IsUnit (⟨x, h⟩ : c.O)) ∧ ∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → c.O), (Continuous fun g => (f g : Qbar l)) → AdicCont (maximalIdeal c.O) f := by
  intro l _ c
  have hle : ∀ x ∈ c.O, ‖x‖ ≤ 1 := by
    intro x hx
    haveI := c.fin
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
    exact (inOf_intIff x).mp (hi.map c.O.val)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    have e := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at e
    rw [e, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hlO : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
    haveI := c.dvr
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 : ((u : c.O) : PadicAlgCl l) * ((u⁻¹ : c.Oˣ) : c.O) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have hb := hle _ ((u⁻¹ : c.Oˣ) : c.O).2
    rw [hu] at h1
    have := congrArg norm h1
    rw [norm_mul, norm_one, SubringClass.coe_natCast] at this
    have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg ((l : ℕ) : PadicAlgCl l))
    linarith
  refine ⟨?_, hle, ?_, ?_⟩
  · intro ι _ x hx
    classical
    haveI := Fintype.ofFinite ι
    obtain ⟨c', hc', hs⟩ := inOf_fin c (Finset.univ.image x) (by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hx i)
    exact ⟨c', hc', fun i => hs _ (Finset.mem_image_of_mem x (Finset.mem_univ i))⟩
  · intro x _ hn h
    have hx0 : (x : PadicAlgCl l) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    have hinv := inOf_div c 1 ⟨x, h⟩ hx0 (by simp [hn])
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.ext
    simp [hx0]
  · intro Γ _ f hf N
    haveI := c.dvr
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hr : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ ^ N := by
      apply pow_pos
      rw [norm_pos_iff]
      exact_mod_cast (Fact.out : l.Prime).ne_zero
    filter_upwards [hf.continuousAt.eventually (Metric.ball_mem_nhds _ hr)] with g hg
    rw [dist_eq_norm] at hg
    rw [Ideal.Quotient.eq]
    set t : c.O := ((l : ℕ) : c.O) ^ N
    have ht0 : (t : PadicAlgCl l) ≠ 0 := by
      simp only [t, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
      exact pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have hq := inOf_div c (f g - f g0) t ht0 (by
      simp only [t, SubmonoidClass.coe_pow, SubringClass.coe_natCast, AddSubgroupClass.coe_sub, norm_pow]
      exact hg.le)
    have he : f g - f g0 = (⟨_, hq⟩ : c.O) * t := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul]
      exact (div_mul_cancel₀ _ ht0).symm
    rw [he]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hlO N)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.RegArith
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem norm_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  have key : ∀ t, ‖(ψ t : K)‖ ≤ 1 := fun t => by
    obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
    refine not_lt.1 fun hlt => ?_
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC ⟨t ^ m, rfl⟩
    simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact absurd hm (not_lt.2 h1)
  refine le_antisymm (key s) ?_
  have h2 := key s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h2

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem emb_ne (H : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion L)ˣ} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) :
    Nonempty (Emb l w) := by
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  have hεc : Continuous ε := ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val
  have hε : ∀ s : Weil h, (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * Hi.algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha
  by_contra hE
  haveI : IsEmpty (Emb l w) := not_nonempty_iff.1 hE
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have h1 := norm_one ε (Units.continuous_val.comp hεc) (inc (frob h))
  rw [hε, deg_frob, zpow_one, Hi.algPow, finprod_of_isEmpty, mul_one, GlobalTheory.Pst.normV_eq_pow (l := l) hw, Nat.cast_pow, norm_pow] at h1
  have h2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (fun h0 => by
    have := GlobalTheory.WeilDeligne.one_lt_normV w
    rw [GlobalTheory.Pst.normV_eq_pow (l := l) hw, h0] at this
    exact lt_irrefl _ this)).1 h1
  exact (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne h2

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands in
private theorem main (H : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {w : Plc F} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {a : Weil h →* (w.adicCompletion F)ˣ} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) {n : ℕ}
    (wt : Fin n → Emb l w → ℤ) (hm : ∀ τ, StrictMono fun j => wt j τ) (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ)
    (hψ : ∀ j, IsLocAlg h (ψ j) (wt j)) : ∃ g, Function.Injective fun i => ψ i g := by
  haveI := emb_ne H hw ha
  haveI : Finite (Emb l w) := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (Emb l w)
  haveI : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  choose ph hph using hψ
  let U : Subgroup (Ine (F := F) A) := ⨅ j, (ph j).ker
  have hU : IsOpen (U : Set (Ine (F := F) A)) := by
    simp only [U, Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun j => (hph j).1
  haveI : Finite (Ine (F := F) A ⧸ U) := U.quotient_finite_of_isOpen hU
  have hN : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hl : ValuativeRel.valuation (w.adicCompletion F) (l : w.adicCompletion F) < 1 := by
    have e : (ValuativeRel.valuation (w.adicCompletion F)).IsEquiv (Valued.v : Valuation (w.adicCompletion F) _) := by
      haveI := Valuation.Compatible.ofValuation (Valued.v : Valuation (w.adicCompletion F) _)
      exact ValuativeRel.isEquiv _ _
    rw [e.lt_one_iff_lt_one, ← map_natCast (algebraMap (𝓞 F) (w.adicCompletion F)),
      IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
    erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (w.valuation_lt_one_iff_mem _).2 hw
  have hu : ValuativeRel.valuation (w.adicCompletion F) (1 + l : w.adicCompletion F) = 1 :=
    (ValuativeRel.valuation (w.adicCompletion F)).map_one_add_of_lt hl
  have hu0 : (1 + l : w.adicCompletion F) ≠ 0 := fun h => by simp [h] at hu
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 _ hu0)
  have hd : deg s = 0 := by
    have h2 := ha.ord_eq s
    rw [hs, GlobalTheory.SmGL.ord_eq_zero_iff.2 hu] at h2
    omega
  have hI : (s : G F Ω) ∈ Ine (F := F) A := actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hd))
  let σ : Ine (F := F) A := ⟨s, hI⟩
  haveI : U.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hmem : σ ^ U.index ∈ U := U.pow_index_mem σ
  have e : ((a (ineIncl h (σ ^ U.index)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = (1 + l) ^ U.index := by
    rw [map_pow, map_pow, show ineIncl h σ = s from rfl, hs]
    simp
  let q : ℕ := (1 + l) ^ U.index
  have hq : 1 < q := Nat.one_lt_pow hN (by have := (Fact.out : l.Prime).pos; omega)
  have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp : ∀ (T : Finset (Emb l w)) (c : Emb l w → ℤ), ∏ j ∈ T, (q : Qbar l) ^ c j = (q : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hq0]
  have key : ∀ j, ((ψ j (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index))) : (Qbar l)ˣ) : Qbar l) =
      (q : Qbar l) ^ ∑ τ, -wt j τ := fun j => by
    have h3 := (hph j).2 a ha (σ ^ U.index)
    rw [show ph j (σ ^ U.index) = 1 from Subgroup.mem_iInf.1 hmem j, finprod_eq_prod_of_fintype, e, mul_one] at h3
    rw [h3, ← hp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [q]
  refine ⟨Subgroup.inclusion (Weil_le_Dec h) (ineIncl h (σ ^ U.index)), fun i j hij => ?_⟩
  have h4 : (q : Qbar l) ^ ∑ τ, -wt i τ = (q : Qbar l) ^ ∑ τ, -wt j τ := by
    rw [← key, ← key]
    exact congrArg Units.val hij
  have h5 : (q : ℚ) ^ ∑ τ, -wt i τ = (q : ℚ) ^ ∑ τ, -wt j τ := by
    apply Rat.cast_injective (α := Qbar l)
    simpa using h4
  have h6 := zpow_right_injective₀ (a := (q : ℚ)) (by positivity) (by exact_mod_cast hq.ne') h5
  have hs : StrictAnti fun j => ∑ τ, -wt j τ := fun i j hij =>
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun τ _ => neg_lt_neg (hm τ hij)
  exact hs.injective h6

theorem UpperTheory.V.Th.Nm.regArith :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (h : s.Wt n) (v : Vl l L) (ψ : Fin n → Dec (F := L) (s.A v) →* (Qbar l)ˣ), h.Incr → (∀ j, IsLocAlg (s.hw v) (ψ j) (h v j)) → ∃ g, Function.Injective fun i => ψ i g := by
  intro H l _ L Ω _ _ _ _ _ _ s n h v ψ hI hψ
  obtain ⟨a, ha⟩ := UpperTheory.V.Loc.localArtinReciprocity H (s.hw v)
  have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
  exact main H.aut.art (s.hw v) ((s.hw v.1 _).1 (by simpa using h1)) ha (h v) (hI v) ψ hψ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.PairOfRep
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp
open UpperTheory.V.AlgebraTools.Det

private theorem pairOfRep_cont {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (h : ∀ a b, AdicCont I fun g => ρ g a b) : (GDet.ofRep ρ).IsCont I := by
  intro i N
  have hl : IsLocallyConstant (fun g : G => fun a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    letI : TopologicalSpace (A ⧸ I ^ N) := ⊥
    haveI : DiscreteTopology (A ⧸ I ^ N) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    exact continuous_pi fun a => continuous_pi fun b => (IsLocallyConstant.iff_continuous _).1 (h a b N)
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))) =
      (fun M : Fin n → Fin n → A ⧸ I ^ N =>
        Ideal.Quotient.mk (I ^ N) ((-1 : A) ^ i) * (Matrix.of M).charpoly.coeff (n - i)) ∘
        (fun g a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    funext g
    simp only [Function.comp_apply, GDet.lam, (repApi ρ).2.1, map_mul]
    congr 1
    rw [← Polynomial.coeff_map, ← Matrix.charpoly_map]
    rfl
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1)))
  rw [key]
  exact hl.comp _

private theorem pairOfRep_polar {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type)
    [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (P : GL (Fin n) R) (h : F.IsForm O n r P) (i : ℕ)
    (y : MonoidAlgebra R F.G₀) : (GDet.ofRep (mat r)).lam i (F.star O R n y) = (GDet.ofRep (mat r)).lam i y := by
  have key := (formRep F O R n r P h).1 R y
  have hP : (↑P : Matrix (Fin n) (Fin n) R).map ⇑(algebraMap R R) = ↑P := by
    ext a b
    simp
  rw [hP] at key
  have e : (GDet.repAlg (mat r) R) (F.star O R n y) =
      ((P⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * ((GDet.repAlg (mat r) R) y)ᵀ *
        ((P⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    rw [inv_inv, Matrix.mul_assoc, key, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  unfold GDet.lam
  rw [(repApi (mat r)).1, (repApi (mat r)).1, e, Matrix.coe_units_inv (P⁻¹), Matrix.charpoly_units_conj,
    Matrix.charpoly_transpose]

theorem UpperTheory.V.Th.Nm.pairOfRep :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (ρ : F.G₀ →* GL (Fin n) A) (P : GL (Fin n) A) (ψ : ∀ v, Fin n → F.Gv v →* Aˣ), 1 ≤ n → (∀ i j, AdicCont (maximalIdeal A) fun g => mat ρ g i j) → (GDet.ofRep (mat ρ)).map (res O A : A →+* ResidueField O) = r.Dbar → F.IsForm O n ρ P → (∀ v i, r.IsPsi v i (ψ v i)) → (∀ v, HasFlag (ρ.comp (F.φ v)) (ψ v)) → (∀ u, ∀ g ∈ r.Ip u, ρ g = 1) → ∃ p : Pair r A, p.D = GDet.ofRep (mat ρ) ∧ p.ψ = ψ := by
  intro l _ n F O _ _ _ r A _ _ _ ρ P ψ hn hc hred hP hψ hfl hI
  refine ⟨⟨GDet.ofRep (mat ρ), ψ, pairOfRep_cont _ _ hc, hred, hψ, fun i g => pairOfRep_polar F O A n ρ P hP i _,
    fun v g h => ?_, fun u g hg h => ?_⟩, rfl, rfl⟩
  · have h2 := oElRep F O A n ρ v _ (hfl v) g
    rw [(repApi _).2.2.1 hn, map_mul, h2, mul_zero, Matrix.trace_zero]
  · have h1 : GDet.repAlg (mat ρ) A (MonoidAlgebra.single g 1 - 1) = 0 := by
      rw [map_sub, map_one]
      simp [GDet.repAlg, mat, hI u g hg]
    rw [(repApi _).2.2.1 hn, map_mul, h1, mul_zero, Matrix.trace_zero]
end
