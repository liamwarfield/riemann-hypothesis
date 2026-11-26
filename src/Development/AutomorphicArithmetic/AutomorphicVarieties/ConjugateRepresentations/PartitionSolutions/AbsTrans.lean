module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartHOfSs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRhamInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigBwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFactsAlt
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep UpperTheory.V.Lit.Dr

private theorem sand_split (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ) (p : HV E a) :
    sand (GeneralLinearGroup.map (pInf E) (GlobalTheory.UnitaryBC.splitCentre E a t)) p = (Real.exp t * Real.exp t) • p := by
  rw [GlobalTheory.UnitaryBC.splitCentre, pInf_infGL]
  refine Subtype.ext ?_
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp t • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  change Matrix.of (sand _ p).1 = (Real.exp t * Real.exp t) • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]

theorem UpperTheory.V.Cj.A.splitFacts :
    SplitFacts := by
  intro E _ _ _ a
  refine ⟨fun t => ⟨pFin_infGL _, _, mul_pos (Real.exp_pos t) (Real.exp_pos t), sand_split E a t⟩,
    fun r hr => ⟨Real.log r / 2, fun p => ?_⟩⟩
  rw [sand_split, ← Real.exp_add, add_halves, Real.exp_log hr]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.AbsTransOf
noncomputable section

open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped ContDiff

namespace UpperTheory.V.Cj.A

theorem absTrans_of (h1 : HdFacts) (h2 : ZigFwd) (h3 : ZigBwd) (h4 : BwdLast) (h5 : ZigFormal) (h6 : PullOp) (h7 : PullAct)
    (h8 : ZigMap) (h9 : CoverEx) (h10 : SatClosed) (h11 : SatFacts) : AbsTrans := by
  intro Γ V S _ _ _ _ d d' G ξ' τ hτ hc hn hcone hp ⟨l, hl⟩ q w hw hdw ⟨T, K, hT, hK, hKY, hz⟩
  obtain ⟨K1, hK1, hKK, hK1Y⟩ := exists_compact_between hK G.isOpen hKY
  obtain ⟨s1, -, s3, -⟩ := h11 Γ V S d G T K
  obtain ⟨o1, o2, o3, -⟩ := h11 Γ V S d G T (interior K1)
  obtain ⟨-, -, -, f4⟩ := h11 Γ V S d G T K1
  obtain ⟨C, φ, hC, hφ, hCA, hCO⟩ := h9 Γ V S d G hp (fun s => G.Y \ sat G T K s) (sat G T (interior K1))
    (fun s => ⟨h10 Γ V S d G hp hcone l hl T K hT hK hKY s, Set.diff_subset, o2 isOpen_interior s, fun p hp' => by
      by_cases h : p ∈ sat G T K s
      · exact Or.inr (s3 _ hKK s h)
      · exact Or.inl ⟨hp', h⟩⟩)
    (fun γ s p => by simp only [Set.mem_diff, G.ρ_mem_iff, s1 γ s p]) o1
  obtain ⟨c, z1, z2, z3, z4⟩ := h2 Γ V S (Idx Γ V) d G hc hn Idx.g (fun _ _ => rfl) C hC q 0 q (zero_add q) (fun _ => w)
    (fun γ _ _ => (hw γ).symm) (fun _ _ => hdw) (fun x hx => by simp [hd, hx, Finset.sum_range_succ])
    (fun x hx s p _ h => by
      obtain ⟨i, rfl⟩ := List.length_eq_one_iff.1 hx
      have := hCA i s (h i (by simp))
      exact hz s p this.1 this.2)
  let G' := chg G ξ'
  let f : (S → Fin d → ℂ) →+ (S → Fin d' → ℂ) := τ.compLeft S
  have hC' : IsCvx G' C := ⟨hC.1, hC.2, hC.3, hC.4⟩
  have hφ' : IsPart G' φ := ⟨hφ.1, hφ.2, hφ.3, hφ.4⟩
  have hF : ∀ i s, ∀ p ∈ G.Y \ sat G T K1 s, φ i s p ≠ 0 → p ∈ C i s := fun i s p hp' h =>
    hCO i s p (fun h' => hp'.2 (o3 _ interior_subset s h')) h
  obtain ⟨u, u1, u2, u3, u4, u5⟩ := h3 Γ V S (Idx Γ V) d' G' hc hn φ hφ' C (fun s => G.Y \ sat G T K1 s) hC'
    (h10 Γ V S d G hp hcone l hl T K1 hT hK1 hK1Y) hF q (fun x => f (c x))
    (fun γ x hx => by
      beta_reduce
      rw [z2 γ x hx]
      exact funext fun s => hτ γ _)
    (fun x hx => by rw [h1.2.2.2.1 _ _ _ f c x, z3 x hx, map_zero])
    (fun x hx s p h => by
      change τ (c x s) = 0
      rw [z4 x hx s p h, map_zero]) q 0 (zero_add q)
  obtain ⟨w', w1, w2, w3⟩ := h4 Γ V S (Idx Γ V) d' G' φ hφ' C _ hF q u u2 u4 u5
  have hl' : G'.IsInvGauge l := hl
  obtain ⟨P, p1, p2, p3⟩ := h6 Γ V S d' G' hcone l hl'
  have p4 := fun k => h7 Γ V S d' G' hcone l hl' k (P k) (p1 k)
  have hι : ∀ γ δ : Γ, (⟨γ * δ, 0⟩ : Idx Γ V) = γ • (⟨δ, 0⟩ : Idx Γ V) := fun _ _ => rfl
  have y1 := (h5 Γ V S (Idx Γ V) d G).2 (fun γ => ⟨γ, 0⟩) hι q 0 _ _ z1
  have y2 := (h5 Γ V S (Idx Γ V) d' G').2 (fun γ => ⟨γ, 0⟩) hι q 0 _ _ ((h5 Γ V S (Idx Γ V) d' G').1 q 0 u (fun _ => w') _ w2 u1)
  refine ⟨_, P q w', y1, h8 Γ V S d' G' P p2 p3 p4 q 0 _ _ y2, fun γ => by rw [p4, w1], ?_, fun s p hp' v i hv => ?_,
    T, K1, hT, hK1, hK1Y, fun s p hp' h => ?_⟩
  · rw [p2, ← w2 [⟨1, 0⟩] rfl, u3 _ rfl, map_zero]
  · rw [p1 q w' s p hp']
    exact (pullA V _ G.Y G.isOpen hcone (l s) (hl.1 s) q _).1 p hp' v i hv
  · have h0 := (hl.1 s).2.1 p hp'
    rw [p1 q w' s p hp', pull, w3 s _ ⟨hcone _ h0 p hp', fun h' => h ((f4 s p _ h0).1 h')⟩]
    rfl

theorem partA_of (h1 : AbsTrans) (h2 : SuppFwd) (h3 : SuppBwd) (h4 : LevCorr) : PartA := by
  intro E _ _ _ a ha U hUo hU σ Ξ Ξ' h hσ q α hα hd0 hs
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  obtain ⟨w, w1, w2, w3⟩ := (h4 E a ho U Ξ q).1 α hα hd0
  let τ : (Fin Ξ.d → ℂ) →+ (Fin Ξ'.d → ℂ) := AddMonoidHom.mk' (fun v i => σ (v (Fin.cast h.symm i))) fun v v' => by
    ext i
    simp
  have hτ : ∀ γ v, τ ((geo ho U Ξ).ξ γ *ᵥ v) = (geo ho U Ξ').ξ γ *ᵥ τ v := fun γ v => by
    ext i
    change σ (∑ j, ratC Ξ γ.1 (Fin.cast h.symm i) j * v j) = ∑ j, ratC Ξ' γ.1 i j * σ (v (Fin.cast h.symm j))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← (finCongr h).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hσ]
    rfl
  obtain ⟨c, w', z1, z2, z3, z4, z5, z6⟩ := h1 _ _ _ _ _ (geo ho U Ξ) (geo ho U Ξ').ξ τ hτ (coneConvex E a).1
    ⟨_, hOne_mem_cone⟩ (coneConvex E a).2 (geoProper E a ho U Ξ hU) (Dr.gauge E a ha ho U Ξ hU) q w w2 w3
    (h2 E a ho U hUo Ξ q α _ w1 hs)
  obtain ⟨β, b1, b2, b3⟩ := (h4 E a ho U Ξ' q).2 w' z3 z4 z5
  refine ⟨U, le_rfl, hUo, hU, β, b3, h3 E a ho U hU Ξ' q β _ b1 z6, hα, b2, c, sigC σ h c, ⟨ho, w, w1, z1⟩,
    ⟨ho, w', b1, z2⟩, ?_⟩
  rw [sub_self]
  cases q with
  | zero => exact fun _ _ => rfl
  | succ q => exact ⟨0, fun _ _ _ => by simp, fun x _ => by simp [hd]⟩

end UpperTheory.V.Cj.A
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.LevCorr
open UpperTheory.V.Cj.A
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem dCo_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q) (w : (geo ho U Ξ).Om q)
    (hw : Corr U Ξ α w.1) (hd : (geo ho U Ξ).dOm q w = 0) : dCo (smLie Ξ) α = 0 := by
  have h := corrD E a ho U Ξ q _ _ hw
  rw [hd] at h
  exact (corrUniq E a ho U Ξ (q + 1)).1 _ 0 _ h (corr_zero U Ξ)

theorem UpperTheory.V.Cj.A.levCorr :
    LevCorr := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα hd => ?_, fun w hi hd hb => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    refine ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, ?_⟩
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [hd] at h
    exact (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)
  · obtain ⟨η, hη⟩ := corrBwd E a ho U Ξ q w
    have e : dCo (smLie Ξ) η = 0 := dCo_zero' ho U Ξ q η w hη hd
    have b := (corrBasic E a U Ξ _ _ _ hη).2 hb
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hη
    exact ⟨η, hη, ⟨c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hη).2 hi X) (c2 X)
      (centralOf E a _ (smLie Ξ) q η b (fun Y i _ => by rw [e]; rfl) X)⟩, e⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.BwdLast
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.bwdLast :
    BwdLast := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q u hu hhd hvan
  obtain ⟨P, hP1, hPeq, hPvan⟩ := partOp Γ V S I d G φ hφ q
  have hconst : ∀ i j : I, u [i] = u [j] := by
    intro i j
    have h := hhd [i, j] rfl
    simp [UpperTheory.V.Lit.Geo.hd, Finset.sum_range_succ] at h
    have h' : u [j] - u [i] = 0 := by
      rw [sub_eq_add_neg]
      simpa using h
    exact (sub_eq_zero.mp h').symm
  refine ⟨P (fun i => u [i]), ?_, ?_, ?_⟩
  · intro γ
    have hinv : (fun i => (G.act q) γ (u [γ⁻¹ • i])) = fun i => u [i] := by
      funext i
      have h := hu γ [γ⁻¹ • i] rfl
      simp only [List.map_cons, List.map_nil, smul_inv_smul] at h
      exact h.symm
    rw [← hPeq γ (fun i => u [i]), hinv]
  · intro x hx
    match x, hx with
    | [i], _ =>
      have hfun : (fun j => u [j]) = fun _ => u [i] := by
        funext j
        exact hconst j i
      rw [hfun, hP1]
  · intro s p hp
    apply hPvan
    intro i hne
    refine hvan [i] rfl s p hp ?_
    intro i' hi'
    rw [List.mem_singleton] at hi'
    rw [hi']
    exact hC i s p hp hne
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SuppBwd
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem cont_inf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_fin (E : Type) [Field E] [NumberField E] (a : ℕ) :
    Continuous (finGL E a) := by
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem mem_out {G : Type} [Group G] (U : Subgroup G) (y : G) :
    y ∈ (fun u => Quotient.out (y : G ⧸ U) * u) '' (U : Set G) :=
  ⟨(Quotient.out (y : G ⧸ U))⁻¹ * y, QuotientGroup.eq.1 (QuotientGroup.out_eq' _), mul_inv_cancel_left _ _⟩

theorem UpperTheory.V.Cj.A.suppBwd :
    SuppBwd := by
  intro E _ _ _ a ho U hU Ξ q α w h ⟨T, K, hT, hK, hKY, hw⟩
  obtain ⟨-, hq2, hq3, -⟩ := qhtFacts E a
  have hC := (sandCpt E a).2 K hKY hK
  have hD : IsCompact (⋃ s ∈ T, (fun u => Quotient.out s * u) '' (U : Set (GL (Fin a) (Af E)))) :=
    hT.isCompact_biUnion fun s _ => hU.image (continuous_const.mul continuous_id)
  obtain ⟨B, hB⟩ := hq3 _ ((hC.prod hD).image
    (((cont_inf E a).comp continuous_fst).mul ((cont_fin E a).comp continuous_snd)))
  refine ⟨B * qht (1 : GA E a), fun X g hg => ?_⟩
  have h0 : w (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U)
      (sand (GeneralLinearGroup.map (pInf E) g) (hOne E a)) = 0 := by
    refine hw _ _ ⟨_, rfl⟩ ?_
    rintro ⟨γ, r, hr, hσ, hρ⟩
    obtain ⟨t, ht⟩ := (splitFacts E a).2 r hr
    have h1 := ((splitFacts E a).1 t).1
    refine absurd (hB 1 (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g) ?_) ?_
    · refine ⟨(GeneralLinearGroup.map (pInf E) (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g),
        GeneralLinearGroup.map (pFin E) (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g)), ⟨?_, ?_⟩,
        infGL_mul_finGL _⟩
      · rw [geo_ρ, ← map_smul, ← ht] at hρ
        simp only [Set.mem_setOf_eq, map_mul, ContinuousLinearMap.mul_apply]
        exact hρ
      · simp only [map_mul, h1, mul_one]
        refine Set.mem_biUnion hσ ?_
        have e : (geo ho U Ξ).σ γ (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U) =
            ((GeneralLinearGroup.map (pFin E) (ratGL E a γ.1) * GeneralLinearGroup.map (pFin E) g :
              GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
        rw [e]
        exact mem_out U _
    · rw [one_mul, hq2]
      exact not_le.2 hg
  have h2 := h (GeneralLinearGroup.map (pInf E) g) (GeneralLinearGroup.map (pFin E) g) X
  rw [h0, infGL_mul_finGL] at h2
  have h3 := congrArg (fun y => Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹ *ᵥ y) h2
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Matrix.mulVec_zero] at h3
  exact h3.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SuppFwd
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.suppFwd :
    SuppFwd := by
  intro E _ _ _ a ho U hU Ξ q α w h hα
  obtain ⟨R, hR⟩ := hα
  obtain ⟨C, hC, hC'⟩ := (qhtFacts E a).2.2.2 R
  have h1 : Continuous (pInf E) := continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  have h2 : Continuous (pFin E) := continuous_snd
  have hi : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h1)
  have hf : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h2)
  haveI : DiscreteTopology (GL (Fin a) (Af E) ⧸ U) := QuotientGroup.discreteTopology hU
  refine ⟨(fun g : GA E a => ((GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) '' C,
    (fun g : GA E a => sand (GeneralLinearGroup.map (pInf E) g) (hOne E a)) '' C,
    (hC.image (QuotientGroup.continuous_mk.comp hf)).finite_of_discrete,
    hC.image ((sandCpt E a).1.comp hi), ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro s _ ⟨g, rfl⟩ hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hlt : R < qht (infGL E a g * finGL E a x) := by
      by_contra hle
      obtain ⟨γ, t, hm⟩ := hC' _ (not_lt.1 hle)
      obtain ⟨e1, r, hr, e2⟩ := (splitFacts E a).1 t
      refine hp ⟨⟨γ, Subgroup.mem_top γ⟩, r, hr, ⟨_, hm, ?_⟩, ⟨_, hm, ?_⟩⟩
      · simp only [map_mul, e1, pFin_infGL, pFin_finGL, one_mul, mul_one]
        rfl
      · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one, ContinuousLinearMap.mul_apply, e2, map_smul, geo_ρ]
    refine ContinuousAlternatingMap.ext fun v => ?_
    have hv' : v = fun i => (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i)))) := by
      funext i
      rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, ← ContinuousLinearMap.mul_apply, ← map_mul,
        mul_inv_cancel, map_one]
      simp
    rw [hv', h, hR _ _ hlt, Matrix.mulVec_zero]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.CoverEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartBase
noncomputable section

open scoped ContDiff Manifold Topology

namespace UpperTheory.V.Cj.A

theorem partBase : PartBase := by
  intro V _ _ _ Y hY D hD hDp
  let Y' : TopologicalSpace.Opens V := ⟨Y, hY⟩
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : LocallyCompactSpace Y' := Y'.isOpen.locallyCompactSpace
  haveI : SecondCountableTopology V := inferInstance
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) (M := Y') isClosed_univ
    (fun j => ((↑) : Y' → V) ⁻¹' D j) (fun j => (hD j).preimage continuous_subtype_val)
    (fun x _ => Set.mem_iUnion.2 ⟨(x : V), hDp x x.2⟩)
  classical
  refine ⟨fun j p => if h : p ∈ Y then f j ⟨p, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    let g : V → ℝ := fun p => if h : p ∈ Y then f j ⟨p, h⟩ else 0
    have h1 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ (fun y : Y' => g (y : V)) ⟨x, hx⟩ := by
      have e : (fun y : Y' => g (y : V)) = f j := by
        funext y
        exact dif_pos y.2
      rw [e]
      exact (f j).contMDiff.contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ g x :=
      (contMDiffAt_subtype_iff (U := Y') (f := g) (x := ⟨x, hx⟩)).1 h1
    exact (contMDiffAt_iff_contDiffAt.1 h2).contDiffWithinAt
  · intro p hp
    obtain ⟨t, ht, htf⟩ := f.locallyFinite ⟨p, hp⟩
    obtain ⟨N, hN, hNt⟩ := (mem_nhds_subtype _ _ _).1 ht
    refine ⟨N, hN, htf.subset ?_⟩
    rintro j ⟨x, hxN, hne⟩
    by_cases hxY : x ∈ Y
    · have h : f j ⟨x, hxY⟩ ≠ 0 := by simpa [hxY] using hne
      exact ⟨⟨x, hxY⟩, h, hNt hxN⟩
    · exact (hne (dif_neg hxY)).elim
  · intro p hp
    refine Eq.trans ?_ (f.sum_eq_one (x := ⟨p, hp⟩) (Set.mem_univ _))
    exact finsum_congr fun j => dif_pos hp
  · intro j p hne
    by_cases hpY : p ∈ Y
    · have h : f j ⟨p, hpY⟩ ≠ 0 := by simpa [hpY] using hne
      exact hf j (subset_tsupport _ h)
    · exact (hne (dif_neg hpY)).elim

end UpperTheory.V.Cj.A
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartProd
open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open scoped ContDiff

private def UpperTheory.V.Cj.A.idxEquiv (Γ J : Type) : Γ × J ≃ Idx Γ J where
  toFun x := ⟨x.1, x.2⟩
  invFun i := (i.g, i.j)
  left_inv _ := rfl
  right_inv _ := rfl

theorem UpperTheory.V.Cj.A.partProd :
    PartProd := by
  intro Γ V S J _ _ _ d G u hu ψ hψs hψf hψ1
  obtain ⟨hus, huf, hu1⟩ := hu
  have hlf : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, {i : Idx Γ J | ∃ x ∈ N,
      u ((G.σ i.g⁻¹) s) ((G.ρ i.g⁻¹) x) * ψ ((G.σ i.g⁻¹) s) i.j ((G.ρ i.g⁻¹) x) ≠ 0}.Finite := by
    intro s p hp
    obtain ⟨N₁, hN₁, hF⟩ := huf s p hp
    have key : ∀ γ : Γ, ∃ M ∈ nhds p,
        {j | ∃ x ∈ M, ψ ((G.σ γ⁻¹) s) j ((G.ρ γ⁻¹) x) ≠ 0}.Finite := by
      intro γ
      obtain ⟨M, hM, hMf⟩ := hψf ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) p) (G.maps _ p hp)
      refine ⟨(G.ρ γ⁻¹) ⁻¹' M, (G.ρ γ⁻¹).continuous.continuousAt.preimage_mem_nhds hM, ?_⟩
      refine hMf.subset ?_
      rintro j ⟨x, hx, hne⟩
      exact ⟨_, hx, hne⟩
    choose M hM hMf using key
    refine ⟨N₁ ∩ ⋂ γ ∈ hF.toFinset, M γ, ?_, ?_⟩
    · exact Filter.inter_mem hN₁ ((Filter.biInter_finset_mem _).2 fun γ _ => hM γ)
    · refine ((hF.toFinset.finite_toSet.biUnion fun γ _ =>
        (Set.finite_singleton γ).prod (hMf γ)).image (idxEquiv Γ J)).subset ?_
      rintro ⟨g, j⟩ ⟨x, ⟨hx1, hx2⟩, hne⟩
      have hu0 : u ((G.σ g⁻¹) s) ((G.ρ g⁻¹) x) ≠ 0 := left_ne_zero_of_mul hne
      have hψ0 : ψ ((G.σ g⁻¹) s) j ((G.ρ g⁻¹) x) ≠ 0 := right_ne_zero_of_mul hne
      have hgF : g ∈ hF.toFinset := hF.mem_toFinset.2 ⟨x, hx1, hu0⟩
      refine ⟨(g, j), Set.mem_biUnion (x := g) hgF ⟨Set.mem_singleton _, x, ?_, hψ0⟩, rfl⟩
      exact Set.mem_iInter₂.1 hx2 g hgF
  refine ⟨?_, hlf, ?_, ?_⟩
  · intro i s
    have hmap : Set.MapsTo (G.ρ i.g⁻¹) G.Y G.Y := fun p hp => G.maps _ p hp
    exact ((hus _).comp (G.ρ i.g⁻¹).contDiff.contDiffOn hmap).mul
      ((hψs _ _).comp (G.ρ i.g⁻¹).contDiff.contDiffOn hmap)
  · intro s p hp
    have hfin : (Function.support fun x : Γ × J =>
        u ((G.σ x.1⁻¹) s) ((G.ρ x.1⁻¹) p) * ψ ((G.σ x.1⁻¹) s) x.2 ((G.ρ x.1⁻¹) p)).Finite := by
      obtain ⟨N, hN, hNf⟩ := hlf s p hp
      refine (hNf.preimage (idxEquiv Γ J).injective.injOn).subset ?_
      intro x hx
      exact ⟨p, mem_of_mem_nhds hN, hx⟩
    rw [← finsum_comp_equiv (idxEquiv Γ J)]
    show ∑ᶠ x : Γ × J, u ((G.σ x.1⁻¹) s) ((G.ρ x.1⁻¹) p) *
      ψ ((G.σ x.1⁻¹) s) x.2 ((G.ρ x.1⁻¹) p) = 1
    rw [finsum_curry _ (by exact hfin)]
    have hin : ∀ a : Γ, ∑ᶠ b : J, u ((G.σ a⁻¹) s) ((G.ρ a⁻¹) p) * ψ ((G.σ a⁻¹) s) b ((G.ρ a⁻¹) p) =
        u ((G.σ a⁻¹) s) ((G.ρ a⁻¹) p) := by
      intro a
      rw [← mul_finsum, hψ1 _ _ (G.maps _ _ hp), mul_one]
    rw [finsum_congr hin]
    exact hu1 s p hp
  · intro γ i s p
    have h1 : (G.σ γ⁻¹) ((G.σ γ) s) = s := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
    have h2 : (G.ρ γ⁻¹) ((G.ρ γ) p) = p := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
    show u ((G.σ (γ * i.g)⁻¹) ((G.σ γ) s)) ((G.ρ (γ * i.g)⁻¹) ((G.ρ γ) p)) *
      ψ ((G.σ (γ * i.g)⁻¹) ((G.σ γ) s)) i.j ((G.ρ (γ * i.g)⁻¹) ((G.ρ γ) p)) = _
    rw [mul_inv_rev, map_mul, map_mul, Equiv.Perm.mul_apply, ContinuousLinearMap.mul_apply, h1, h2]
end

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.coverEx :
    CoverEx := by
  classical
  intro Γ V S _ _ _ _ d G hP A O hAO hA hO
  obtain ⟨W, hW⟩ := UpperTheory.V.Lit.Dr.window Γ V S d G hP
  obtain ⟨u, hu⟩ := UpperTheory.V.Lit.Dr.cutoff Γ V S d G W hW
  have hB : ∀ s j, ∃ B : Set V, IsOpen B ∧ Convex ℝ B ∧ B ⊆ A s ∧ (j ∈ A s → j ∈ B) := by
    intro s j
    by_cases hj : j ∈ A s
    · obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 (hAO s).1 j hj
      exact ⟨Metric.ball j r, Metric.isOpen_ball, convex_ball j r, hb, fun _ => Metric.mem_ball_self hr⟩
    · exact ⟨∅, isOpen_empty, convex_empty, Set.empty_subset _, fun h => absurd h hj⟩
  choose B hBo hBc hBA hBm using hB
  have hψ := fun s => partBase V G.Y G.isOpen (fun j => if j ∈ O s then O s else B s j)
    (fun j => by
      by_cases hj : j ∈ O s
      · simpa [hj] using (hAO s).2.2.1
      · simpa [hj] using hBo s j)
    (fun p hp => by
      by_cases hj : p ∈ O s
      · simp [hj]
      · simpa [hj] using hBm s p (((hAO s).2.2.2 hp).resolve_right hj))
  choose ψ h1 h2 h3 h4 using hψ
  have hsub : ∀ (i : Idx Γ V) s, G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j ⊆ A s := by
    intro i s p hp
    exact (hA i.g⁻¹ s p).1 (hBA _ _ hp)
  refine ⟨fun i s => G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j, _, ⟨?_, ?_, ?_, ?_⟩,
    partProd Γ V S V d G u hu ψ h1 h2 h3, hsub, ?_⟩
  · intro i s
    exact (hBo _ _).preimage (G.ρ _).continuous
  · intro i s
    exact (hBc _ _).linear_preimage (G.ρ i.g⁻¹).toLinearMap
  · intro i s
    exact (hsub i s).trans (hAO s).2.1
  · intro γ i s p
    have e1 : G.ρ (γ * i.g)⁻¹ (G.ρ γ p) = G.ρ i.g⁻¹ p := by
      rw [mul_inv_rev, map_mul, ContinuousLinearMap.mul_apply, G.ρ_inv_apply]
    have e2 : G.σ (γ * i.g)⁻¹ (G.σ γ s) = G.σ i.g⁻¹ s := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.mul_apply]; simp
    simp only [Set.mem_preimage, Idx.smul_g, Idx.smul_j, e1, e2]
  · intro i s p hp hne
    have h5 := h4 _ _ _ (right_ne_zero_of_mul hne)
    have h6 : G.ρ i.g⁻¹ p ∉ O (G.σ i.g⁻¹ s) := fun h => hp ((hO i.g⁻¹ s p).1 h)
    by_cases hj : i.j ∈ O (G.σ i.g⁻¹ s)
    · rw [if_pos hj] at h5
      exact absurd h5 h6
    · rw [if_neg hj] at h5
      exact h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigMap
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.zigMap :
    ZigMap := by
  intro Γ V S _ _ _ d G P hd' hi ha q
  induction q with
  | zero =>
    intro k u c h x hx
    show P 0 (u x) = G.incl (c x)
    rw [h x hx, hi]
  | succ q ih =>
    rintro k u c ⟨b, hb, hdb, hz⟩
    refine ⟨fun x => P q (b x), fun γ x hx => ?_, fun x hx => ?_, ?_⟩
    · show P q (b (x.map (γ * ·))) = G.act q γ (P q (b x))
      rw [hb γ x hx, ha]
    · show G.dOm q (P q (b x)) = P (q + 1) (u x)
      rw [hd', hdb x hx]
    · have e : hd (fun x => P q (b x)) = fun x => P q (hd b x) :=
        funext fun x => hdFacts.2.2.2.1 Γ _ _ (P q).toAddMonoidHom b x
      rw [e]
      exact ih (k + 1) (hd b) c hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SatClosed
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.OrbClosed
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.orbClosed :
    OrbClosed := by
  intro Γ V S _ _ _ _ d G hG K hKY hK s s'
  unfold UpperTheory.V.Lit.Dr.Geo.Proper at hG
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hpY, hpA⟩
  obtain ⟨L, hLn, hLY, hL⟩ := local_compact_nhds (G.isOpen.mem_nhds hpY)
  have hFfin : {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K}.Finite :=
    hG (L ∪ K) (Set.union_subset hLY hKY) (hL.union hK) s s'
  set F := {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K} with hF
  have hBc : IsClosed (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K) :=
    hFfin.isClosed_biUnion fun γ _ => hK.isClosed.preimage (G.ρ γ).continuous
  have hpB : p ∉ ⋃ γ ∈ F, (G.ρ γ) ⁻¹' K := by
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists]
    intro γ hγF hγ
    exact hpA ⟨γ, hγF.1, hγ⟩
  have hnb : (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K)ᶜ ∈ nhds p := hBc.isOpen_compl.mem_nhds hpB
  filter_upwards [hLn, hnb] with q hqL hqB
  refine ⟨hLY hqL, ?_⟩
  rintro ⟨γ, hσ, hγ⟩
  apply hqB
  simp only [Set.mem_iUnion, Set.mem_preimage]
  exact ⟨γ, ⟨hσ, q, Or.inl hqL, Or.inr hγ⟩, hγ⟩
end

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satClosed :
    SatClosed := by
  intro Γ V S _ _ _ _ d G hP hC l hl T K hT hK hKY s
  have hcont : ∀ s', ContinuousOn (fun p : V => l s' p • p) G.Y := fun s' =>
    (hl.1 s').1.continuousOn.smul continuousOn_id
  have hmem : ∀ s', ∀ p ∈ G.Y, l s' p • p ∈ G.Y := fun s' p hp =>
    hC _ ((hl.1 s').2.1 p hp) p hp
  have horb : ∀ s', IsOpen (G.Y \ {p | ∃ γ : Γ, G.σ γ s = s' ∧ G.ρ γ p ∈ (fun p : V => l s' p • p) '' K}) := fun s' =>
    orbClosed Γ V S d G hP _ (by rintro _ ⟨k, hk, rfl⟩; exact hmem s' k (hKY hk))
      (hK.image_of_continuousOn ((hcont s').mono hKY)) s s'
  have hopen := (hcont s).isOpen_inter_preimage G.isOpen (hT.isOpen_biInter fun s' _ => horb s')
  convert hopen using 1
  ext p
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  refine and_congr_right fun hp => ⟨fun h s' hs' => ⟨hmem s p hp, ?_⟩, fun h => ?_⟩
  · rintro ⟨γ, rfl, k, hk, hk'⟩
    have h1 := (hl.1 (G.σ γ s)).2.1 k (hKY hk)
    have h2 := (hl.1 s).2.1 p hp
    refine h ⟨γ, (l (G.σ γ s) k)⁻¹ * l s p, mul_pos (inv_pos.2 h1) h2, hs', ?_⟩
    have h3 : l (G.σ γ s) k • k = l s p • G.ρ γ p := by rw [← map_smul]; exact hk'
    rw [mul_smul, ← h3, inv_smul_smul₀ h1.ne']
    exact hk
  · rintro ⟨γ, t, ht, hs', hk⟩
    refine (h _ hs').2 ⟨γ, rfl, _, hk, ?_⟩
    show l (G.σ γ s) (t • G.ρ γ p) • t • G.ρ γ p = _
    rw [(hl.1 _).2.2 t ht _ (G.maps γ p hp), hl.2 γ s p hp, map_smul, smul_smul]
    congr 1
    field_simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PullOp
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr
open scoped ContDiff

theorem UpperTheory.V.Cj.A.pullOp :
    PullOp := by
  intro Γ V S _ _ _ _ d G hC l hl
  have hY : IsOpen G.Y := G.isOpen
  have hpos : ∀ s, ∀ p ∈ G.Y, l s p • p ∈ G.Y := fun s p hp => hC _ ((hl.1 s).2.1 p hp) p hp
  have hw : ∀ q (w : G.Om q) (s : S),
      ContDiffOn ℝ ∞ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ p ∉ G.Y, (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := fun q w => w.2
  have mem : ∀ q (w : G.Om q), (fun s => G.Y.indicator
      (pull (l s) ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))) ∈ G.Om q := by
    intro q w s
    refine ⟨?_, fun p hp => Set.indicator_apply_eq_zero.2 fun h => absurd h hp⟩
    exact (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).1.congr
      fun p hp => Set.indicator_of_mem hp _
  have padd : ∀ q (s : S) (a b : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (a + b) p = pull (l s) a p + pull (l s) b p := by
    intro q s a b p
    ext v
    simp [pull]
  have psmul : ∀ q (s : S) (c : ℂ) (a : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (c • a) p = c • pull (l s) a p := by
    intro q s c a p
    ext v
    simp [pull]
  have ext_ind : ∀ q (om : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) p, p ∈ G.Y →
      extDeriv (G.Y.indicator om) p = extDeriv om p := by
    intro q om p hp
    simp only [extDeriv]
    rw [Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hY.mem_nhds hp) fun x hx => Set.indicator_of_mem hx om)]
  let P : ∀ q, G.Om q →ₗ[ℂ] G.Om q := fun q =>
    { toFun := fun w => ⟨_, mem q w⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_add, Pi.add_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact padd q s _ _ p
        · simp [Set.indicator, hp]
      map_smul' := by
        intro c a
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact psmul q s c _ p
        · simp [Set.indicator, hp] }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro q w s p hp
    exact Set.indicator_of_mem hp _
  · intro q w
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · rw [Geo.dOm_apply G _ s hp]
      change extDeriv (G.Y.indicator _) p = G.Y.indicator _ p
      rw [ext_ind _ _ _ hp, Set.indicator_of_mem hp,
        (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).2 p hp]
      simp only [pull]
      rw [Geo.dOm_apply G w s (hpos s p hp)]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
  · intro f
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · change G.Y.indicator _ p = _
      rw [Set.indicator_of_mem hp]
      ext v
      simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rw [Geo.incl_apply G f s (hpos s p hp), Geo.incl_apply G f s hp]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PullAct
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr Matrix

theorem UpperTheory.V.Cj.A.pullAct :
    PullAct := by
  intro Γ V S _ _ _ d G _hcone l hl q P hP γ w
  have hinv : ∀ x : V, G.ρ γ (G.ρ γ⁻¹ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinv' : ∀ x : V, G.ρ γ⁻¹ (G.ρ γ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinvS : ∀ s : S, G.σ γ (G.σ γ⁻¹ s) = s := by
    intro s
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  apply Subtype.ext
  funext s p
  by_cases hp : p ∈ G.Y
  · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
    have hleq : l (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = l s p := by
      have := hl.2 γ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) hp'
      rw [hinvS, hinv] at this
      exact this.symm
    have hdiff : DifferentiableAt ℝ (l s) p :=
      ((hl.1 s).1.contDiffAt (G.isOpen.mem_nhds hp)).differentiableAt (by simp)
    have hf : HasFDerivAt (fun x => l s x • x) (fderiv ℝ (fun x => l s x • x) p) (G.ρ γ (G.ρ γ⁻¹ p)) := by
      rw [hinv]
      exact (hdiff.smul differentiableAt_id).hasFDerivAt
    have hcomp := (G.ρ γ⁻¹).hasFDerivAt.comp (G.ρ γ⁻¹ p) (hf.comp (G.ρ γ⁻¹ p) (G.ρ γ).hasFDerivAt)
    have heq : (fun x => l (G.σ γ⁻¹ s) x • x) =ᶠ[nhds (G.ρ γ⁻¹ p)]
        (⇑(G.ρ γ⁻¹) ∘ ((fun x => l s x • x) ∘ ⇑(G.ρ γ))) := by
      filter_upwards [G.isOpen.mem_nhds hp'] with x hx
      have := hl.2 γ (G.σ γ⁻¹ s) x hx
      rw [hinvS] at this
      simp only [Function.comp_apply, map_smul, hinv', this]
    have hder : ∀ u : V, fderiv ℝ (fun x => l (G.σ γ⁻¹ s) x • x) (G.ρ γ⁻¹ p) (G.ρ γ⁻¹ u)
        = G.ρ γ⁻¹ (fderiv ℝ (fun x => l s x • x) p u) := by
      intro u
      rw [(hcomp.congr_of_eventuallyEq heq).fderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hinv]
    ext v
    rw [G.act_apply, hP w _ _ hp', hP _ s p hp]
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply, G.act_apply]
    rw [hleq, map_smul]
    simp only [Function.comp_def, hder]
  · have hnot : G.ρ γ⁻¹ p ∉ G.Y := by
      intro h
      exact hp (hinv p ▸ G.maps γ _ h)
    have h1 := ((P w).2 (G.σ γ⁻¹ s)).2 _ hnot
    have h2 := ((P (G.act q γ w)).2 s).2 p hp
    rw [h2]
    ext v
    rw [G.act_apply, h1]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SatFacts
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satFacts :
    SatFacts := by
  intro Γ V S _ _ _ d G T K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ s p
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq]
    constructor
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ, t, ht, ?_, ?_⟩
      · rw [map_mul, Equiv.Perm.mul_apply]
        exact hT
      · rw [map_mul, ContinuousLinearMap.mul_apply]
        exact hK
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ⁻¹, t, ht, ?_, ?_⟩
      · rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hT
      · rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hK
  · intro hK s
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨γ, t, ht, hT, hp⟩
    have hc : Continuous fun q : V => t • (G.ρ γ) q :=
      continuous_const.smul (G.ρ γ).continuous
    filter_upwards [(hK.preimage hc).mem_nhds hp] with q hq
    exact ⟨γ, t, ht, hT, hq⟩
  · rintro K' hKK' s p ⟨γ, t, ht, hT, hp⟩
    exact ⟨γ, t, ht, hT, hKK' hp⟩
  · intro s p t ht
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq, map_smul, smul_smul]
    constructor
    · rintro ⟨γ, u, hu, hT, hK⟩
      exact ⟨γ, u * t, mul_pos hu ht, hT, hK⟩
    · rintro ⟨γ, u, hu, hT, hK⟩
      refine ⟨γ, u / t, div_pos hu ht, hT, ?_⟩
      rwa [div_mul_cancel₀ u ht.ne']
end

namespace UpperTheory.V.Cj

theorem A.absTrans : A.AbsTrans :=
  A.absTrans_of A.hdFacts A.zigFwd A.zigBwd A.bwdLast A.zigFormal A.pullOp A.pullAct A.zigMap A.coverEx A.satClosed A.satFacts

theorem partA : PartA := A.partA_of A.absTrans A.suppFwd A.suppBwd A.levCorr

end UpperTheory.V.Cj
