module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSupercuspidalTypeCharacterZmodPow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocComm
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.locComm_pf :
    UpperTheory.Gal.Gen.LocComm := by
  intro E _ _ _ a w₀ x g hx hg
  obtain ⟨hxf, hxa⟩ := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  have hxi : cInf x = 1 := hxf
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
  · change cInf (x * g) = cInf (g * x)
    rw [map_mul, map_mul, hxi, one_mul, mul_one]
  · change cLoc u (x * g) = cLoc u (g * x)
    rw [map_mul, map_mul]
    by_cases hu : Apart u w₀
    · rw [hxa u hu, one_mul, mul_one]
    · rw [hg u hu, one_mul, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SatExPf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.satEx_pf :
    UpperTheory.Gal.Gen.SatEx := by
  classical
  intro E _ _ _ a K w hw hK U hU ⟨φ, hφU, hφ0, hφK⟩
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨σ, hcomp, v, hv0, hv⟩ := GlobalTheory.T.exists_localComponent_eigenvector_splitPlace E a U hU w hw (GlobalTheory.LFun.KGL w (n := a)) ho hc 1 φ hφU hφ0
    (fun x hx hxJ => by
      have := hφK x ((hK x hx).2 hxJ)
      simpa using this)
  have hfix : GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 (fun k hk => by
      have := hv ⟨k, hk⟩
      simpa using this), hv0⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hfix
  obtain ⟨z, rfl⟩ : ∃ z : Fin a → ℂˣ, Finset.univ.val.map z = B := by
    obtain ⟨l, rfl⟩ := Quotient.exists_rep B
    have hl : l.length = a := hB.card
    subst hl
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  exact ⟨z, σ, hcomp, hB⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TowerPf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tower_pf :
    UpperTheory.Gal.Gen.CongSub → UpperTheory.Gal.Gen.Tower := by
  intro hC E _ _ w a l hl hw ha N hN
  obtain ⟨m, -, J', lam, hJo, hJc, hJN, hJtf, -, -⟩ := GlobalTheory.T.exists_supercuspidal_type_character_zmod_pow E w a l hl hw ha N hN 0
  obtain ⟨J, hT, hp⟩ := hC E w a l hl hw
  obtain ⟨s, hs⟩ := hT.small _ (hJo.mem_nhds J'.one_mem)
  refine ⟨fun n => J (s + n), ⟨fun n => hT.isOpen _, fun n => hT.compact _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact hT.anti (Nat.add_le_add_left hij s)
  · intro n g hg x hx
    exact hT.normal (s + n) g (hT.anti (Nat.zero_le (s + 0)) hg) x hx
  · intro M hM
    obtain ⟨n, hn⟩ := hT.small M hM
    exact ⟨n, fun x hx => hn (hT.anti (Nat.le_add_left n s) hx)⟩
  · exact fun x hx => hJN (hs hx)
  · exact fun g hg ho => hJtf g (hs hg) ho
  · intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ, pow_mul]
      exact hp (s + n) _ ih
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SmoothAt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.smoothAt_pf :
    UpperTheory.Gal.Gen.SmoothAt := by
  intro E _ _ _ a w₀ hw W f
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let p : GL (Fin a) (w₀.adicCompletion E) → finU (E := E) (n := a) := fun y =>
    ⟨(e.symm y).1, (Subgroup.mem_inf.1 (e.symm y).2).1⟩
  have hp : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp e.symm.continuous) _
  have hp1 : p 1 = 1 := by
    apply Subtype.ext
    simp [p]
  have hS : IsOpen {k : finU (E := E) (n := a) | algRep W k f = f} := GlobalTheory.DefU.isSmooth_algRep W f
  refine ⟨p ⁻¹' {k : finU (E := E) (n := a) | algRep W k f = f},
    (hS.preimage hp).mem_nhds (by simp [hp1]), fun x hx hxN v g => ?_⟩
  have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
    rw [← he ⟨x, hx⟩]
    exact e.symm_apply_apply _
  have h2 : algRep W (p (cLoc w₀ x)) f = f := hxN
  have h3 : (p (cLoc w₀ x)).1 = x := by
    simp only [p, h1]
  have h4 := congrArg (fun F : algForms W => F.1 v g) h2
  change f.1 v (g * (p (cLoc w₀ x)).1) = f.1 v g at h4
  rwa [h3] at h4
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Restrict
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.restrict_pf :
    UpperTheory.Gal.Gen.Restrict := by
  classical
  intro k _ _ J J' i θ S h ε hε
  obtain ⟨s, c, hs, hc⟩ := h ε hε
  refine ⟨s.image (fun x => x ∘ i), fun ζ => ∑ η ∈ s with η ∘ i = ζ, c η, ?_, ?_⟩
  · intro ζ hζ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hζ
    obtain ⟨η, hη, rfl⟩ := hζ
    exact ⟨η, hs hη, rfl⟩
  · intro P
    have key : ∀ η : J' → k,
        MvPolynomial.aeval (η ∘ i) P = MvPolynomial.aeval η (MvPolynomial.rename i P) := by
      intro η
      rw [MvPolynomial.aeval_rename]
    calc _ = ‖MvPolynomial.aeval θ (MvPolynomial.rename i P)
          - ∑ η ∈ s, c η * MvPolynomial.aeval η (MvPolynomial.rename i P)‖ := by
          congr 2
          · exact key θ
          · rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image (fun x => x ∘ i))
              (g := fun x => x ∘ i) (fun η hη => Finset.mem_image_of_mem _ hη)]
            refine Finset.sum_congr rfl fun ζ _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun η hη => ?_
            rw [← (Finset.mem_filter.1 hη).2, key]
      _ ≤ ε := hc _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NeglAt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.neglAt_pf :
    UpperTheory.Gal.Gen.GlobOp → UpperTheory.Gal.Gen.Small → UpperTheory.Gal.Gen.NeglAt := by
  intro hG hS E _ _ _ a K w₀ w hs hap hyp Φ hΦ δ hδ
  obtain ⟨C, hC⟩ := hG E a K w hs hyp
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨p, hp, hp1, hI⟩ := hS a Φ hΦ (δ / (|C| + 1)) (div_pos hδ hC1)
  obtain ⟨h, hloc, hsep, hnorm, hop⟩ := hC p hp
  refine ⟨h, ?_, hsep, ?_, ?_⟩
  · intro g hg
    have hm := (GlobalTheory.Cong.LevelExt.mem_locU_iff g).1 (hloc g hg)
    refine ⟨hm.1, fun u hu => hm.2 u ?_⟩
    have e : u.under (𝓞 (maximalRealSubfield E)) = w₀.under (𝓞 (maximalRealSubfield E)) :=
      Classical.byContradiction hu
    intro e'
    exact hap (e'.symm.trans e)
  · have hI0 : 0 ≤ ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    calc ∑ g ∈ h.support, ‖h g‖ ^ 2
        ≤ C * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 := hnorm
      _ ≤ |C| * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hI0
      _ ≤ |C| * (δ / (|C| + 1)) := mul_le_mul_of_nonneg_left hI (abs_nonneg C)
      _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ hC1]
          nlinarith [abs_nonneg C]
  · intro U hU hB φ hφ hfix
    have hB' : ¬ GenAt w Φ U := hB
    unfold GenAt at hB'
    push_neg at hB'
    obtain ⟨z, hz, h0⟩ := hB'
    rw [hop U hU z hz φ hφ hfix, hp1 z h0, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CoverPf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.cover_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.LocComm → UpperTheory.Gal.Gen.Cover := by
  intro hL hC E _ _ _ a w₀ hw K hK J hJ
  obtain ⟨hlev, hmem, -, -, hsurj, -⟩ := hL E a w₀ hw K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have ho : IsOpen (((lev K w₀ (J 0)).subgroupOf (finU (E := E) (n := a)) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨N, hN, h1, hNC⟩ := hlev.isOpen
    refine Filter.mem_of_superset ((hN.preimage continuous_subtype_val).mem_nhds h1) fun y hy => ?_
    exact Subgroup.mem_subgroupOf.2 (hNC ⟨hy, y.2⟩)
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a _ ho
  refine ⟨S, fun n => ?_⟩
  choose R hR using fun q : J 0 => (hsurj q.1)
  refine ⟨fun q => R q.out, fun q => ⟨(hR _).1, (hR _).2 ▸ q.out.2⟩, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  obtain ⟨k₀, hk₀, j, hj, hjJ, hkeq⟩ := (hmem _).1 (Subgroup.mem_subgroupOf.1 hk)
  have hcomm : j * k₀ = k₀ * j := hC E a w₀ j k₀ hj (hK.one k₀ hk₀)
  let q : J 0 ⧸ (J n).subgroupOf (J 0) := QuotientGroup.mk ⟨cLoc w₀ j, hjJ⟩
  have hq : (q.out)⁻¹ * ⟨cLoc w₀ j, hjJ⟩ ∈ (J n).subgroupOf (J 0) :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
  have hq' : (cLoc w₀ (R q.out))⁻¹ * cLoc w₀ j ∈ J n := by
    have := Subgroup.mem_subgroupOf.1 hq
    rw [(hR q.out).2]
    simpa using this
  have hr : R q.out ∈ locU a w₀ := (hR _).1
  refine ⟨γ, hγ, (⟨s, hs⟩, q), x, hx, (R q.out)⁻¹ * j * k₀, ?_, ?_⟩
  · refine mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hr) hj, ?_⟩)) (Subgroup.mem_sup_left hk₀)
    change cLoc w₀ ((R q.out)⁻¹ * j) ∈ J n
    rwa [map_mul, map_inv]
  · have hxr : R q.out * x = x * R q.out := fin_mul_inf (hlev.fin (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hr, by
      change cLoc w₀ (R q.out) ∈ J 0
      rw [(hR q.out).2]
      exact q.out.2⟩))) hx
    show γ * s * x * (k : UA E a) = γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀)
    rw [hkeq, ← hcomm]
    have e : γ * (s * R q.out) * x * ((R q.out)⁻¹ * j * k₀) = γ * s * (R q.out * x) * ((R q.out)⁻¹ * j * k₀) := by
      group
    rw [e, hxr]
    group
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RatFin
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ratFin_pf :
    UpperTheory.Gal.Gen.RatFin := by
  intro E _ _ _ a
  refine ⟨?_, ?_⟩
  · intro Z hZ
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    set_option synthInstance.maxHeartbeats 200000 in
    have hcl : IsClosed (((ratGL E a).range : Subgroup (GA E a)) : Set (GA E a)) := Subgroup.isClosed_of_discrete
    let K : Set (GA E a) := Subtype.val '' Z
    have hK : IsCompact K := hZ.image continuous_subtype_val
    have hKG : IsCompact (K ∩ ((ratGL E a).range : Set (GA E a))) := hK.inter_right hcl
    let t : Set (ratGL E a).range := {x | (x : GA E a) ∈ K}
    have himg : Subtype.val '' t = K ∩ ((ratGL E a).range : Set (GA E a)) := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
      · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
    have ht : IsCompact t := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
    have hfin : (K ∩ ((ratGL E a).range : Set (GA E a))).Finite := by
      rw [← himg]; exact (ht.finite_of_discrete).image _
    refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨x, ⟨hxZ, hxr⟩, rfl⟩
    exact ⟨⟨x, hxZ, rfl⟩, (Subgroup.mem_subgroupOf).1 hxr⟩
  · intro w γ hγ h1
    obtain ⟨δ, hδ⟩ := (Subgroup.mem_subgroupOf).1 hγ
    have hδ1 : δ = 1 := by
      ext i j
      have h2 := congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.1 i j) h1
      have h3 : (cLoc w γ : GL (Fin a) (w.adicCompletion E)).1 i j = algebraMap E (w.adicCompletion E) (δ.1 i j) := by
        simp [cLoc, ← hδ, pLoc, pFin, ratGL]
        rfl
      have h4 : algebraMap E (w.adicCompletion E) (δ.1 i j) =
          algebraMap E (w.adicCompletion E) ((1 : GL (Fin a) E).1 i j) := by
        rw [← h3]
        refine h2.trans ?_
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      exact (algebraMap E (w.adicCompletion E)).injective h4
    apply Subtype.ext
    rw [← hδ, hδ1, map_one]; rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DenseGen
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  have h2 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact inv_lt_one_of_one_lt₀ h2

theorem UpperTheory.Gal.Gen.denseGen_pf :
    UpperTheory.Gal.Gen.Step → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.DenseGen := by
  intro hStep hPF E _ _ _ l _ ι a ha w₀ hl hs K hK W S Φ hS f hf ε hε
  have hl1 := norm_l_lt_one l
  have hr0 : 0 ≤ Real.sqrt ‖((l : ℕ) : Qbar l)‖ := Real.sqrt_nonneg _
  have hr1 : Real.sqrt ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    simpa using hl1
  have key : ∀ m : ℕ, ∀ f ∈ fixedBy W K,
      ∃ G ∈ part W K (fun U => ∀ w ∈ S, GenAt w (Φ w) U), ∃ e : UA E a → ℂ,
        (∀ g, ‖ι.symm (e g)‖ ≤ Real.sqrt ‖((l : ℕ) : Qbar l)‖ ^ m) ∧
        ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g := by
    intro m
    induction m with
    | zero =>
      intro f _
      refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun g => ?_, fun v g => ?_⟩
      · simp
      · simp
    | succ m ih =>
      intro f hf
      obtain ⟨G, hG, e, he, hfe⟩ := ih f hf
      have hGf : G ∈ fixedBy W K := (hPF E a W K _).2.1 hG
      obtain ⟨G', hG', e', he', hfe'⟩ :=
        hStep E l ι a ha w₀ hl hs K hK W S Φ hS (f - G) (Submodule.sub_mem _ hf hGf)
      refine ⟨G + G', Submodule.add_mem _ hG hG', fun g => e' g * e g, fun g => ?_, fun v g => ?_⟩
      · rw [map_mul, norm_mul, pow_succ, mul_comm]
        exact mul_le_mul (he g) (Real.le_sqrt_of_sq_le (he' g)) (norm_nonneg _) (pow_nonneg hr0 _)
      · have h1 := hfe' v g
        have h2 := hfe v g
        have h3 : (f - G).1 v g = f.1 v g - G.1 v g := by simp
        have h4 : (G + G').1 v g = G.1 v g + G'.1 v g := by simp
        rw [h3] at h1
        rw [h4, mul_assoc, ← h2, ← h1]
        ring
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hr1
  obtain ⟨G, hG, e, he, hfe⟩ := key m f hf
  exact ⟨G, hG, e, fun g => (he g).trans hm.le, hfe⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StepCore
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.stepCore_pf :
    UpperTheory.Gal.Gen.AlgC → UpperTheory.Gal.Gen.Codim → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.StepCore := by
  intro hAlg hCod hPF E _ _ _ l _ ι a W C C' hCfin H _ _ hH lam hsurj hC'C hker ℓ hinf hright haut P hfd hcard f hf
  letI : Fintype H := Fintype.ofFinite H
  have hex : ∀ φ : H → ℂ, ∃ F : algForms W, ∀ v g, F.1 v g = φ (ℓ g) * f.1 v g := fun φ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => φ (ℓ g)) (haut φ) (fun g x hx => by simp only [hinf g x hx])
  choose Ψ₀ hΨ₀ using hex
  let Ψ : (H → ℂ) →ₗ[ℂ] algForms W :=
    { toFun := Ψ₀
      map_add' := fun φ ψ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hΨ₀]
        ring
      map_smul' := fun c φ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, hΨ₀, RingHom.id_apply, smul_eq_mul]
        ring }
  have hΨ : ∀ φ v g, (Ψ φ).1 v g = φ (ℓ g) * f.1 v g := hΨ₀
  have hfix : ∀ φ, Ψ φ ∈ fixedBy W C' := fun φ k hk v g => by
    have hkC : k ∈ C := hC'C hk
    have h1 : lam ⟨k, hkC⟩ = 1 := (hker ⟨k, hkC⟩).1 hk
    have h2 : ℓ (g * k) = ℓ g := by
      have := hright g ⟨k, hkC⟩
      rw [h1, mul_one] at this
      exact this
    rw [hΨ, hΨ, h2, hf k hkC v g]
  obtain ⟨h1, -, -, h4, -⟩ := hPF E a W C' P
  have hdim := hCod ℂ (H → ℂ) (algForms W) Ψ (part W C' P) (part W C' fun U => ¬ P U) (fun φ => h1 (hfix φ))
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  rw [Nat.card_eq_fintype_card] at hcard
  have hA : Fintype.card H ≤ 2 * Module.finrank ℂ ((part W C' P).comap Ψ) := by omega
  have hstable : ∀ c ∈ (part W C' P).comap Ψ, ∀ u, (fun h => c (h * u)) ∈ (part W C' P).comap Ψ := by
    intro φ hφ u
    obtain ⟨c, rfl⟩ := hsurj u
    have hnorm : ∀ c' ∈ C', (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C' := by
      intro c' hc'
      have hc'C : c' ∈ C := hC'C hc'
      have hm : (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C := C.mul_mem (C.mul_mem (C.inv_mem c.2) hc'C) c.2
      refine (hker ⟨_, hm⟩).2 ?_
      have e1 : (⟨_, hm⟩ : C) = c⁻¹ * ⟨c', hc'C⟩ * c := Subtype.ext rfl
      rw [e1, map_mul, map_mul, (hker ⟨c', hc'C⟩).1 hc', mul_one, map_inv, inv_mul_cancel]
    have hrep : Ψ (fun h => φ (h * lam c)) = algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ) :=
      Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        have e2 : (algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ)).1 v g = (Ψ φ).1 v (g * c.1) := rfl
        rw [e2, hΨ, hΨ, hright g c, hf c.1 c.2 v g]
    change Ψ _ ∈ part W C' P
    rw [hrep]
    exact h4 ⟨c.1, hCfin c.2⟩ hnorm _ hφ
  obtain ⟨φ, hφ, hnorm⟩ := hAlg l ι H hH _ hstable hA
  exact ⟨Ψ φ, hφ, fun g => 1 - φ (ℓ g), fun g => hnorm (ℓ g), fun v g => by rw [hΨ]; ring⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.AlgCPf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.algC_pf :
    UpperTheory.Gal.Gen.Alg → UpperTheory.Gal.Gen.AlgC := by
  intro hA l _ ι H _ _ hp P hP hcard
  let P' : Submodule (Qbar l) (H → Qbar l) :=
    { carrier := {f | (fun h => ι (f h)) ∈ P}
      zero_mem' := by
        show (fun h => ι ((0 : H → Qbar l) h)) ∈ P
        convert P.zero_mem using 1
        funext h
        simp
      add_mem' := by
        intro a b ha hb
        show (fun h => ι ((a + b) h)) ∈ P
        convert P.add_mem ha hb using 1
        funext h
        simp
      smul_mem' := by
        intro r a ha
        show (fun h => ι ((r • a) h)) ∈ P
        convert P.smul_mem (ι r) ha using 1
        funext h
        simp }
  let j : P ≃+ P' :=
    { toFun := fun c => ⟨fun h => ι.symm (c.1 h), by
        show (fun h => ι (ι.symm (c.1 h))) ∈ P
        simpa using c.2⟩
      invFun := fun f => ⟨fun h => ι (f.1 h), f.2⟩
      left_inv := by
        intro c
        ext h
        simp
      right_inv := by
        intro f
        ext h
        simp
      map_add' := by
        intro a b
        ext h
        simp }
  have hrank : Module.rank ℂ P = Module.rank (Qbar l) P' := by
    refine rank_eq_of_equiv_equiv (fun z => ι.symm z) j ι.symm.bijective ?_
    intro r m
    ext h
    change ι.symm (r * m.1 h) = ι.symm r * ι.symm (m.1 h)
    exact map_mul ι.symm r (m.1 h)
  have hfin : Module.finrank ℂ P = Module.finrank (Qbar l) P' := by
    unfold Module.finrank
    rw [hrank]
  have hinv : ∀ c ∈ P', ∀ g : H, (fun h => c (h * g)) ∈ P' := by
    intro c hc g
    exact hP _ hc g
  obtain ⟨c, hc, hbound⟩ := hA (Qbar l) l H hp P' hinv (hfin ▸ hcard)
  refine ⟨fun h => ι (c h), hc, ?_⟩
  intro h
  simpa using hbound h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StepPf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.step_pf :
    UpperTheory.Gal.Gen.SmoothAt → UpperTheory.Gal.Gen.Tower → UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.CountGen → UpperTheory.Gal.Gen.StepCore → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Step := by
  intro hSm hTw hLev hEll hCG hSC hPF E _ _ _ l _ ι a ha w₀ hl hs K hK W S Φ hS f hf
  obtain ⟨N, hN, hfN⟩ := hSm E a w₀ hs W f
  obtain ⟨J, hJ, hJN, htf, hpow⟩ := hTw E w₀ a l (Fact.out) hl ha N hN
  obtain ⟨n, hfd, hcard⟩ := hCG E a w₀ hs K hK J hJ W S Φ hS
  obtain ⟨lv0, mem0, inJ0, -, sec0, tr0⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  obtain ⟨-, memn, inJn, -, -, -⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  haveI hnorm : ((J n).subgroupOf (J 0)).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hJ.normal n g.1 g.2 x.1 hx⟩
  haveI : CompactSpace (J 0) := isCompact_iff_compactSpace.1 (hJ.compact 0)
  haveI hfin : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) :=
    Subgroup.quotient_finite_of_isOpen _ ((hJ.isOpen n).preimage continuous_subtype_val)
  have hp : IsPGroup l (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hpow n x.1 x.2
  let φ : lev K w₀ (J 0) →* J 0 :=
    ((cLoc w₀).comp (lev K w₀ (J 0)).subtype).codRestrict (J 0) (fun c => inJ0 c.1 c.2)
  let lam : lev K w₀ (J 0) →* (J 0 ⧸ (J n).subgroupOf (J 0)) := (QuotientGroup.mk' _).comp φ
  have hlam : ∀ c : lev K w₀ (J 0), lam c = 1 ↔ cLoc w₀ c.1 ∈ J n := fun c => by
    change ((φ c : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hsurj : Function.Surjective lam := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, hxy⟩ := sec0 y.1
    have hxC : x ∈ lev K w₀ (J 0) :=
      (mem0 x).2 ⟨1, one_mem _, x, hx, hxy ▸ y.2, (one_mul x).symm⟩
    refine ⟨⟨x, hxC⟩, ?_⟩
    change ((φ ⟨x, hxC⟩ : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = _
    congr 1
    exact Subtype.ext hxy
  have hle : lev K w₀ (J n) ≤ lev K w₀ (J 0) := fun c hc => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (memn c).1 hc
    exact (mem0 _).2 ⟨k, hk, x, hx, hJ.anti (Nat.zero_le n) hxJ, rfl⟩
  have hiff : ∀ c : lev K w₀ (J 0), c.1 ∈ lev K w₀ (J n) ↔ lam c = 1 := fun c => by
    rw [hlam]
    exact ⟨inJn c.1, tr0 (J n) c.1 c.2⟩
  obtain ⟨ℓ, hℓ₁, hℓ₂, hℓ₃⟩ := hEll E a (lev K w₀ (J 0)) lv0 _ lam
    ⟨cLoc w₀ ⁻¹' (J n : Set (GL (Fin a) (w₀.adicCompletion E))), (hJ.isOpen n).preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀),
      by simp [one_mem], fun c hc => (hlam c).2 hc⟩
    (fun c hc => by
      have h1 : cLoc w₀ c.1 = 1 :=
        htf _ (inJ0 c.1 c.2) (MonoidHom.isOfFinOrder ((cLoc w₀).comp (lev K w₀ (J 0)).subtype) hc)
      exact (hlam c).2 (h1 ▸ one_mem _))
  have hfC : f ∈ fixedBy W (lev K w₀ (J 0)) := fun c hc v g => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (mem0 c).1 hc
    rw [← mul_assoc, hfN x hx (hJN hxJ) v (g * k)]
    exact hf k hk v g
  obtain ⟨G, hG, e, he, hfe⟩ := hSC E l ι a W (lev K w₀ (J 0)) (lev K w₀ (J n)) lv0.fin _ hp lam hsurj hle hiff
    ℓ hℓ₁ hℓ₂ hℓ₃ (fun U => ∀ w ∈ S, GenAt w (Φ w) U) hfd hcard f hfC
  exact ⟨G, (hPF E a W (lev K w₀ (J n)) _).2.2.1 K le_sup_left hG, e, he, hfe⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.OpOfFinsetSum
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem opOf_finset_sum {Γ V ι : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V)
    (f : Γ →₀ ℂ) (I : Finset ι) (u : ι → V) : opOf ρ f (∑ i ∈ I, u i) = ∑ i ∈ I, opOf ρ f (u i) := by
  unfold opOf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  exact Finset.sum_comm

private theorem finite_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : Subgroup G}
    (hA : IsCompact (A : Set G)) (hB : IsOpen (B : Set G)) : Finite (A ⧸ B.subgroupOf A) := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have ho : IsOpen ((B.subgroupOf A : Subgroup A) : Set A) := hB.preimage continuous_subtype_val
  exact Subgroup.quotient_finite_of_isOpen _ ho

private theorem bound_arith {M s ε c t : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s) (hε : 0 < ε) (hc : 0 ≤ c) (ht : t ≤ ε / (M * s + 1)) :
    M * (s * c) * t ≤ ε * c := by
  have hd : 0 < M * s + 1 := by positivity
  have h1 : M * s * t ≤ ε := by
    have hMs : 0 ≤ M * s := by positivity
    calc M * s * t ≤ M * s * (ε / (M * s + 1)) := mul_le_mul_of_nonneg_left ht hMs
      _ = ε * (M * s / (M * s + 1)) := by ring
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 (by linarith)) hε.le
      _ = ε := mul_one ε
  calc M * (s * c) * t = (M * s * t) * c := by ring
    _ ≤ ε * c := mul_le_mul_of_nonneg_right h1 hc

theorem UpperTheory.Gal.Gen.count_pf :
    UpperTheory.Gal.Gen.CountCore → UpperTheory.Gal.Gen.Cover → UpperTheory.Gal.Gen.Sep → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Count := by
  intro hCore hCover hSep hPart E _ _ _ a w₀ hs K hK J hJ W B hB ε hε
  obtain ⟨M, hM0, hM⟩ := hCore E a W
  obtain ⟨S, hS⟩ := hCover E a w₀ hs K hK J hJ
  have hδ : 0 < ε / (M * (S.card : ℝ) + 1) := by positivity
  obtain ⟨h, h1, h2, h3, h4⟩ := hB _ hδ
  obtain ⟨n₀, hn₀⟩ := hSep E a w₀ hs K hK J hJ S h.support h1 h2
  refine ⟨n₀, fun n hn => ?_⟩
  haveI : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) := finite_quot (hJ.compact 0) (hJ.isOpen n)
  letI : Fintype (J 0 ⧸ (J n).subgroupOf (J 0)) := Fintype.ofFinite _
  obtain ⟨r, hr, hcov⟩ := hS n
  have hsep : Separates (lev K w₀ (J n)) (fun y : S × (J 0 ⧸ (J n).subgroupOf (J 0)) => y.1.1 * r y.2) h.support :=
    fun y g hg g' hg' γ hγ x hx c hc e =>
      hn₀ n hn (y.1, ⟨r y.2, hr y.2⟩) g hg g' hg' γ hγ x hx c hc e
  have hfix : ∀ f ∈ part W (lev K w₀ (J n)) B, ∀ v, opOf (RU E a) h (f.1 v) = f.1 v := by
    intro f hf v
    obtain ⟨I, F, hF, rfl⟩ := (hPart E a W (lev K w₀ (J n)) B).2.2.2.2 f hf
    have e : (∑ π ∈ I, F π : algForms W).1 v = ∑ π ∈ I, (F π).1 v := by
      simp [Submodule.coe_sum, LinearMap.sum_apply]
    rw [e, opOf_finset_sum]
    refine Finset.sum_congr rfl fun π hπ => ?_
    obtain ⟨hP, hfin, hfx, -⟩ := hF π hπ
    refine h4 π.V π.isAut hP _ (AutSub.mem_finPart.1 hfin v) fun x hx => funext fun g => ?_
    rw [RU_apply]
    exact hfx x ((le_sup_left : K ≤ lev K w₀ (J n)) hx) v g
  obtain ⟨hfd, hle⟩ := hM (lev K w₀ (J n)) _ _ hcov h hsep (part W (lev K w₀ (J n)) B)
    (hPart E a W (lev K w₀ (J n)) B).2.1 hfix
  refine ⟨hfd, hle.trans ?_⟩
  have hcard : (Fintype.card (S × (J 0 ⧸ (J n).subgroupOf (J 0))) : ℝ) =
      (S.card : ℝ) * (Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_coe, Nat.card_eq_fintype_card]
    push_cast
    rfl
  rw [hcard]
  exact bound_arith hM0 (Nat.cast_nonneg _) hε (Nat.cast_nonneg _) h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EllGrp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.ellGrp_pf :
    UpperTheory.Gal.Gen.EllGrp := by
  classical
  intro G H _ _ Γ C lam hyp
  have key : ∀ (r γ₁ γ₂ : G), γ₁ ∈ Γ → γ₂ ∈ Γ → ∀ c₁ c₂ : C,
      γ₁ * r * c₁ = γ₂ * r * c₂ → lam c₁ = lam c₂ := by
    intro r γ₁ γ₂ h1 h2 c₁ c₂ h
    have h' : γ₂⁻¹ * γ₁ * r = r * ((c₂ * c₁⁻¹ : C) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      calc γ₂⁻¹ * γ₁ * r = γ₂⁻¹ * (γ₁ * r * c₁) * (c₁ : G)⁻¹ := by group
        _ = γ₂⁻¹ * (γ₂ * r * c₂) * (c₁ : G)⁻¹ := by rw [h]
        _ = r * ((c₂ : G) * (c₁ : G)⁻¹) := by group
    have h3 := hyp r _ (Γ.mul_mem (Γ.inv_mem h2) h1) _ h'
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3.symm
  obtain ⟨R, hR⟩ : ∃ R : G → Set G, ∀ g x, x ∈ R g ↔ ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c :=
    ⟨fun g => {x | ∃ γ ∈ Γ, ∃ c : C, x = γ * g * c}, fun _ _ => Iff.rfl⟩
  have hself : ∀ g, g ∈ R g := fun g => (hR g g).2 ⟨1, Γ.one_mem, 1, by simp⟩
  have hsub : ∀ g g', g' ∈ R g → R g' ⊆ R g := by
    intro g g' hg x hx
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    obtain ⟨γ', hγ', c', e'⟩ := (hR g' x).1 hx
    exact (hR g x).2 ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by rw [e', e, Subgroup.coe_mul]; group⟩
  have hsymm : ∀ g g', g' ∈ R g → g ∈ R g' := by
    intro g g' hg
    obtain ⟨γ, hγ, c, e⟩ := (hR g g').1 hg
    exact (hR g' g).2 ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by rw [e, Subgroup.coe_inv]; group⟩
  obtain ⟨rep, hrep⟩ : ∃ rep : G → G, ∀ g, rep g = Classical.epsilon (· ∈ R g) :=
    ⟨_, fun _ => rfl⟩
  have hrepR : ∀ g g', g' ∈ R g → rep g' = rep g := by
    intro g g' hg
    have hRR : R g' = R g := Set.Subset.antisymm (hsub g g' hg) (hsub g' g (hsymm g g' hg))
    rw [hrep, hrep, hRR]
  have hdec : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    have hm : rep g ∈ R g := by
      rw [hrep]
      exact Classical.epsilon_spec ⟨g, hself g⟩
    obtain ⟨γ, hγ, c, e⟩ := (hR g _).1 hm
    exact ⟨c⁻¹, γ⁻¹, Γ.inv_mem hγ, by rw [e, Subgroup.coe_inv]; group⟩
  let ℓ : G → H := fun g => lam (Classical.choose (hdec g))
  have hℓ : ∀ g γ, γ ∈ Γ → ∀ c : C, g = γ * rep g * c → ℓ g = lam c := by
    intro g γ hγ c e
    obtain ⟨γ0, h0, e0⟩ := Classical.choose_spec (hdec g)
    exact key (rep g) γ0 γ h0 hγ _ _ (e0.symm.trans e)
  refine ⟨ℓ, ?_, ?_⟩
  · intro γ hγ g
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (γ * g) = rep g := hrepR g _ ((hR g _).2 ⟨γ, hγ, 1, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0]
    apply hℓ (γ * g) (γ * γ0) (Γ.mul_mem hγ h0) c0
    rw [hr]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
  · intro g c
    obtain ⟨c0, γ0, h0, e0⟩ := hdec g
    have hr : rep (g * c) = rep g := hrepR g _ ((hR g _).2 ⟨1, Γ.one_mem, c, by simp⟩)
    rw [hℓ g γ0 h0 c0 e0, ← map_mul]
    apply hℓ (g * c) γ0 h0 (c0 * c)
    rw [hr, Subgroup.coe_mul]
    conv_lhs => rw [e0]
    simp only [mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CountGen
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem finset_sup_finrank_le {ι M : Type*} [AddCommGroup M] [Module ℂ M] (S : Finset ι)
    (A : ι → Submodule ℂ M) (r : ℝ)
    (h : ∀ i ∈ S, FiniteDimensional ℂ (A i) ∧ (Module.finrank ℂ (A i) : ℝ) ≤ r) :
    FiniteDimensional ℂ (S.sup A : Submodule ℂ M) ∧
      (Module.finrank ℂ (S.sup A : Submodule ℂ M) : ℝ) ≤ S.card * r := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact ⟨inferInstance, by simp⟩
  | insert i S hi ih =>
    obtain ⟨hfd, hle⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨hfi, hli⟩ := h i (Finset.mem_insert_self i S)
    rw [Finset.sup_insert, Finset.card_insert_of_notMem hi]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    have h1 : (Module.finrank ℂ (A i ⊔ S.sup A : Submodule ℂ M) : ℝ) ≤
        (Module.finrank ℂ (A i) : ℝ) + Module.finrank ℂ (S.sup A : Submodule ℂ M) := by
      exact_mod_cast Submodule.finrank_add_le_finrank_add_finrank (A i) (S.sup A)
    push_cast
    linarith

private theorem part_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a)
    (C : Subgroup (UA E a)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (Φ : HeightOneSpectrum (𝓞 E) → MvPolynomial (Fin a) ℂ) :
    part W C (fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) ≤
      S.sup fun w => part W C fun U => ¬ GenAt w (Φ w) U := by
  refine iSup₂_le fun π hπ => ?_
  push_neg at hπ
  obtain ⟨w, hw, hg⟩ := hπ
  refine le_trans ?_ (Finset.le_sup (f := fun w => part W C fun U => ¬ GenAt w (Φ w) U) hw)
  exact le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : ¬ GenAt w (Φ w) π.V) => π.finPart W ⊓ fixedBy W C) π hg le_rfl

theorem UpperTheory.Gal.Gen.countGen_pf :
    UpperTheory.Gal.Gen.Count → UpperTheory.Gal.Gen.NeglAt → UpperTheory.Gal.Gen.CountGen := by
  classical
  intro hC hN E _ _ _ a w₀ hw₀ K hK J hJ W S Φ hD
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (2 * ((S.card : ℝ) + 1)) := ⟨_, rfl⟩
  have hc : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hεpos : 0 < ε := by rw [hε]; positivity
  have key : ∀ w, ∃ n₀ : ℕ, w ∈ S → ∀ n, n₀ ≤ n →
      FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n₀, h⟩ := hC E a w₀ hw₀ K hK J hJ W _
        (hN E a K w₀ w (hD.split w hw) (hD.apart w hw) (hD.hyp w hw) (Φ w) (hD.ne w hw)) ε hεpos
      exact ⟨n₀, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose n₀ hn₀ using key
  refine ⟨S.sup n₀, ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, n = S.sup n₀ := ⟨_, rfl⟩
  rw [← hn]
  have hall : ∀ w ∈ S, FiniteDimensional ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) ∧
      (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) : ℝ) ≤
        ε * Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := fun w hw =>
    hn₀ w hw n (hn ▸ Finset.le_sup (f := n₀) hw)
  obtain ⟨hfd, hle⟩ := finset_sup_finrank_le S
    (fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U) _ hall
  have hsub := part_le_sup W (lev K w₀ (J n)) S Φ
  refine ⟨Submodule.finiteDimensional_of_le hsub, ?_⟩
  have hmono := Submodule.finrank_mono hsub
  have hmono' : (Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Module.finrank ℂ (S.sup fun w => part W (lev K w₀ (J n)) fun U => ¬ GenAt w (Φ w) U :
        Submodule ℂ (algForms W)) := by
    exact_mod_cast hmono
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := ⟨_, rfl⟩
  rw [← hNdef] at hle
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hfin : 2 * ((S.card : ℝ) * (ε * N)) ≤ N := by
    have h2 : 2 * ((S.card : ℝ) * (ε * N)) = (S.card : ℝ) / ((S.card : ℝ) + 1) * N := by
      rw [hε]; field_simp
    rw [h2]
    have h3 : (S.card : ℝ) / ((S.card : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hc]; linarith
    nlinarith
  have : (2 * Module.finrank ℂ (part W (lev K w₀ (J n)) fun U => ¬ ∀ w ∈ S, GenAt w (Φ w) U) : ℝ) ≤
      Nat.card (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    rw [← hNdef]; linarith
  exact_mod_cast this
end
