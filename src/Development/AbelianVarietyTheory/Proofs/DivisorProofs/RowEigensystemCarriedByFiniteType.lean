module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpanGoodBlock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorFamilyAdjointLiftSingleEigensystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorFamilyAdjointLiftSingleEigensystem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.UpSystem

theorem flatMap_cast (l : List ℕ) : List.flatMap (fun a : ℕ => [(a : ℤ)]) l = List.map (fun a : ℕ => (a : ℤ)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem labIn_eq (n : ℕ) (s : List ℕ) : Formalism.IndefR.Links.labIn n s =
    List.map (fun a : ℕ => (a : ℤ)) s ++ List.replicate (n - 2 * s.length) 0 ++ List.map (fun a : ℕ => -(a : ℤ)) s.reverse := by
  unfold Formalism.IndefR.Links.labIn
  simp only [List.bind_eq_flatMap, List.pure_def, flatMap_cast, List.map_map]
  rfl

theorem labIn_pairwise {n : ℕ} {s : List ℕ} (h : Formalism.L2.Col.InertTypeOk n s) :
    (Formalism.IndefR.Links.labIn n s).Pairwise (fun a b : ℤ => b ≤ a) := by
  obtain ⟨h1, -, -⟩ := h
  rw [labIn_eq]
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact List.pairwise_map.2 (h1.imp fun h => by exact_mod_cast h)
  · exact List.pairwise_replicate.2 (Or.inr le_rfl)
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    rw [List.eq_of_mem_replicate hb]
    exact Int.natCast_nonneg x
  · rw [List.pairwise_map, List.pairwise_reverse]
    exact h1.imp fun h => by omega
  · intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
      omega
    · rw [List.eq_of_mem_replicate ha]
      omega

end GlobalTheory.UpSystem

namespace GlobalTheory.UpSystem


set_option maxHeartbeats 1000000 in
theorem up_sys : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hOk hW hEx hS hTS hInert
  have h1 := GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW
  have hC := h1.1 hEx
  have hSF := h1.2.1
  have hIn := h1.2.2.1
  have hEE := h1.2.2.2.2.1
  choose hX hXo _ using (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  have hf := GlobalTheory.AdjBlock.model_form (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ)
    (J := (levEnv _ R.βX (R.datXt A3.A.μ0)).J) (χ := (levEnv _ R.βX (R.datXt A3.A.μ0)).χ) (R.B.R A3.A.μ0).pres
    (R.HX A3.A.μ0) (hC.models.HX A3.A.μ0) (hC.models.jX A3.A.μ0)
  choose Tc hTc using fun i => GlobalTheory.AdjBlock.exists_cx hf.1 hf.2.1 ((A3.rowI A3.A.μ0).opAll i)
  refine ⟨Tc, fun i f => (hTc i f).symm, fun c => ?_⟩
  have hext : ∀ i (U : Module.End ℂ (R.HX A3.A.μ0).H),
      (∀ f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = U (R.jX A3.A.μ0 f)) → Tc i = U :=
    fun i U hU => GlobalTheory.AdjBlock.ext_of_span hf.2.1 fun f => (hTc i f).trans (hU f)
  have hzero : ∀ i, (A3.rowI A3.A.μ0).opAll i = 0 → Tc i = 0 := by
    intro i h0
    refine hext i 0 (fun f => ?_)
    have e1 : (A3.rowI A3.A.μ0).opAll i f = 0 := by rw [h0]; rfl
    exact (congrArg (R.jX A3.A.μ0) e1).trans ((map_zero _).trans (LinearMap.zero_apply _).symm)
  have hsys : ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cX c0, GlobalTheory.Hk3.MatchE R.toRealDat A3.A.μ0 P cX c0 → ∀ i,
      Tc i = hX P cX → ∃ a : ℂ, ∀ w ∈ R.EEc c,
        Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P hP cX c0 hm i hi
    have h10 := (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 P hP cX c0 hm hX hXo).2 c
    refine ⟨_, fun w hw => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) hi).trans
      (h10 w ((hEE c).symm ▸ hw))⟩
  have hev0 : ∀ i, Tc i = 0 → ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i h0 =>
    ⟨0, fun w _ => (congrArg (fun U : Module.End ℂ (R.HX A3.A.μ0).H => U (LinearMap.adjoint (R.Th A3.A.μ0) w)) h0).trans
      ((LinearMap.zero_apply _).trans (zero_smul ℂ _).symm)⟩
  have key : ∀ i, ∃ a : ℂ, ∀ w ∈ R.EEc c,
      Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = a • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    rintro (⟨P, k⟩ | ⟨Q, y⟩)
    · by_cases hk : k ≤ D.sp.X'.rank
      · have hgood := ((GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P.1 P.2).1
        have h99 := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 (P : A3.A.ok A3.A.μ0)
        have hso := (GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo
          (P : A3.A.ok A3.A.μ0) k hk
        exact hsys _ hgood _ _ (h99.choose_spec.1 k hk) _ (hext _ _ hso)
      · exact hev0 _ (hzero _ ((hC.fam.degR A3.A.μ0 P).2 k (not_le.1 hk)))
    · refine Or.elim (hInert.1 A3.A.μ0 ((Q : A3.okI A3.A.μ0), y)) (fun h0 => ?_) (fun hy => ?_)
      · exact hev0 (Sum.inr (Q, y)) (hzero (Sum.inr (Q, y)) h0)
      · have hgc := hIn A3.A.μ0 Q.1 Q.2
        have tie := (hW.inert.hR A3.A.μ0).some
        have hy'' : Formalism.L2.Col.InertTypeOk D.sp.X'.rank hy.choose := R.B.rankR ▸ hy.choose_spec.1
        have h78 := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hC.lev hC.fam hC.models A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
          (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI A3.A.μ0)
          (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
          (fun i hi => ⟨(hIn A3.A.μ0 i.1.1 i.1.2).1, (hIn A3.A.μ0 i.1.1 i.1.2).2, labIn_pairwise hi⟩) tie (Q, hy.choose) hy''
        have hm := (hTS _ hgc.1 hgc.2).1.1 (Finsupp.single (Formalism.IndefR.Links.labIn D.sp.X'.rank hy.choose) 1)
        refine hsys _ hgc.1 _ _ hm.choose_spec (Sum.inr (Q, y)) (hext _ _ fun f => ?_)
        exact (congrArg (R.jX A3.A.μ0) (LinearMap.congr_fun hy.choose_spec.2 f)).trans (h78.2.2.2 hX hXo f)
  exact ⟨fun i => (key i).choose, fun w hw i => (key i).choose_spec w hw⟩

end GlobalTheory.UpSystem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorFamilyAdjointLiftSingleEigensystemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∃ Tc : (A3.rowI A3.A.μ0).OpIx → Module.End ℂ (R.HX A3.A.μ0).H, (∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = Tc i (R.jX A3.A.μ0 f)) ∧ ∀ c, ∃ x : (A3.rowI A3.A.μ0).OpIx → ℂ, ∀ w ∈ R.EEc c, ∀ i, Tc i (LinearMap.adjoint (R.Th A3.A.μ0) w) = x i • LinearMap.adjoint (R.Th A3.A.μ0) w := by
  first | exact @GlobalTheory.UpSystem.up_sys | exact GlobalTheory.UpSystem.up_sys | (intros; apply GlobalTheory.UpSystem.up_sys <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIxOfMemEigAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem exists_ix_of_mem_eigAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m), A3.fam3.Ok3 s → ∀ (x : (A3.rowI A3.A.μ0).OpIx → K) (f : (A3.A.fam.R A3.A.μ0).S.Forms), f ≠ 0 → f ∈ (A3.A.fam.R A3.A.μ0).ZHg A3.A.X → f ∈ Formalism.L2.Col.eigAt (A3.rowI A3.A.μ0).opAll x → ∃ p : A3.fam3.base3.Ix, (A3.rowI A3.A.μ0).HasRes3 p.1 x := by
  classical
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 h x f hf0 hfZ hfx
  have hB : (A3.A.fam.R A3.A.μ0).Ok s := h.ok2.what₂ A3.A.μ0
  have hD : (A3.rowI A3.A.μ0).Ok3 := h.what₂ A3.A.μ0
  have hs := (A3.rowI A3.A.μ0).splitOver_opAll hB hD

  have hfZH : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
    le_eigSum_elim (A3.A.fam.R A3.A.μ0).op (A3.rowI A3.A.μ0).opI hD.comm hs _ (by exact hfZ.1)
  have hHB : Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => x (Sum.inl i)) := by
    by_contra hn
    have hf2 : f ∈ Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i)) :=
      Formalism.L2.Col.eigAt_le_eigSum (C := fun y => ¬ Formalism.L2.Col.HasBlocks (A3.A.fam.R A3.A.μ0).n (A3.A.fam.R A3.A.μ0).q (A3.A.fam.R A3.A.μ0).t (A3.A.fam.R A3.A.μ0).bl (fun i => y (Sum.inl i))) hn hfx
    exact hf0 (Submodule.disjoint_def.1 (Formalism.L2.Col.disjoint_eigSum hD.comm fun y h1 h2 => h2 h1) f hfZH hf2)
  choose c hc using hHB
  let Sg : Pl0 → K[X] := fun P0 => if hP : ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 then c hP.choose else 1
  have hSg : ∀ P, Sg ((A3.A.fam.R A3.A.μ0).pl P) = c P := by
    intro P
    have hP : ∃ P', (A3.A.fam.R A3.A.μ0).pl P' = (A3.A.fam.R A3.A.μ0).pl P := ⟨P, rfl⟩
    simp only [Sg, dif_pos hP]
    rw [hB.pl_inj hP.choose_spec]
  let e : I0 × Ty → K := fun k0 => if hP : ∃ P, (A3.rowI A3.A.μ0).plI P = k0.1 then x (Sum.inr (hP.choose, k0.2)) else 0
  have he : ∀ (P : (A3.rowI A3.A.μ0).PlI) (y : Ty), e ((A3.rowI A3.A.μ0).plI P, y) = x (Sum.inr (P, y)) := by
    intro P y
    have hP : ∃ P', (A3.rowI A3.A.μ0).plI P' = (A3.rowI A3.A.μ0).plI P := ⟨P, rfl⟩
    simp only [e, dif_pos hP]
    rw [hD.plI_inj hP.choose_spec]
  have hres : (A3.rowI A3.A.μ0).HasRes3 (Sg, e) x := by
    refine ⟨fun P => ?_, fun k => (he k.1 k.2).symm⟩
    show _ = Sg ((A3.A.fam.R A3.A.μ0).pl P) * (A3.A.fam.R A3.A.μ0).blockProd P
    rw [hSg P, mul_comm]
    exact hc P

  set a0 := goodAt A3.A.fam.X (⊥ : Subgroup G) 1 with ha0
  have hidem : a0 * a0 = a0 :=
    (good_at_spec K A3.A.fam.v0 h.ok2.conj G A3.A.fam.X h.ok2.irr (⊥ : Subgroup G) 1).idem
  have hfix : (A3.A.fam.R A3.A.μ0).S.gaOp (A3.A.fam.R A3.A.μ0).r a0 f = f := by
    obtain ⟨g, hg⟩ := LinearMap.mem_range.1 hfZ.2
    have hid' : a0 * goodAt A3.A.X (⊥ : Subgroup G) 1 = goodAt A3.A.X (⊥ : Subgroup G) 1 := hidem
    rw [← hg, ← BlockDat.gaOp_mul, hid']
  obtain ⟨u0, hu0⟩ := (A3.A.fam.R A3.A.μ0).exists_vE_of_fix (Lvl.full A3.A.fam.X) hfix
  have hmem : (Sg, e) ∈ (A3.rowI A3.A.μ0).ixFin3 A3.A.fam.X := by
    rw [(A3.rowI A3.A.μ0).mem_ixFin3 hD.comm]
    refine ⟨fun P0 hP0 => ?_, fun P0 hP0 y => ?_, ?_⟩
    · have hP : ¬ ∃ P, (A3.A.fam.R A3.A.μ0).pl P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show Sg P0 = 1
      simp only [Sg, dif_neg hP]
    · have hP : ¬ ∃ P, (A3.rowI A3.A.μ0).plI P = P0 := fun ⟨P, hP⟩ => hP0 ⟨P, hP⟩
      show e (P0, y) = 0
      simp only [e, dif_neg hP]
    · intro hbot
      have hu0mem : u0 ∈ (A3.A.fam.R A3.A.μ0).inV0 (Lvl.full A3.A.fam.X) ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum (Sg, e)) := by
        rw [BlockDat.mem_goodPart_iff, hu0]
        exact Formalism.L2.Col.eigAt_le_eigSum (C := (A3.rowI A3.A.μ0).HasRes3 (Sg, e)) hres hfx
      rw [hbot, Submodule.mem_bot] at hu0mem
      apply hf0
      rw [← hu0, hu0mem, Matrix.mulVec_zero, map_zero]
  exact ⟨⟨(Sg, e), hmem⟩, hres⟩

end GlobalTheory.Div
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfRowTestOfScalar
noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

end Concrete

end GlobalTheory.OneFormTest
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEigensystemCarriedByFiniteType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Div

theorem span_range_comp_basis {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) :
    Submodule.span ℂ (Set.range fun k => j (b k)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨b k, rfl⟩)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V)
    (opC : I → Module.End ℂ W) (Z : Submodule K V) (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hcomm : ∀ i v, j (op i v) = opC i (j v))
    (hpc : Formalism.L2.Col.PairComm op) (hso : Formalism.L2.Col.SplitOver op) (x : I → ℂ) (u : W)
    (hu : ∀ i, opC i u = x i • u) (hu0 : u ≠ 0) (huZ : u ∈ Submodule.span ℂ (j '' (Z : Set V))) :
    ∃ s : I → K, x = (fun i => σ (s i)) ∧
      Formalism.L2.Col.eigAt opC x = Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) ∧
      ∃ f, f ≠ 0 ∧ f ∈ Z ∧ f ∈ Formalism.L2.Col.eigAt op s := by
  have hsp' : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ := (span_range_comp_basis σ j b).trans hsp
  have key := GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp' hcomm
  have hmem : u ∈ Formalism.L2.Col.eigAt opC x := Formalism.L2.Col.mem_eigAt_of_forall_apply hu
  have hocc : Formalism.L2.Col.Occurs opC x := fun hbot => hu0 ((Submodule.eq_bot_iff _).1 hbot u hmem)
  obtain ⟨s, _, rfl⟩ := key.2.2 hpc hso x hocc
  refine ⟨s, rfl, (key.1 s).symm, ?_⟩
  have hin : u ∈ Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) := by
    rw [← GlobalTheory.span_image_inf_of_linearIndependent σ j b hli]
    exact ⟨huZ, (key.1 s) ▸ hmem⟩
  by_contra hcon
  push_neg at hcon
  apply hu0
  have hle : Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · subst hy0; simp
    · exact absurd hy.2 (hcon y hy0 hy.1)
  exact (Submodule.mem_bot ℂ).1 (hle hin)

theorem map_le_span_image {K V W H : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] W) (Θ : H →ₗ[ℂ] W) (E : Submodule ℂ H)
    (A B : Submodule K V) (h : ∀ v ∈ E, Θ v ∈ Submodule.span ℂ (j '' (A : Set V))) (hAB : A ≤ B) :
    E.map Θ ≤ Submodule.span ℂ (j '' (B : Set V)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  exact Submodule.span_mono (Set.image_mono hAB) (h v hv)


set_option maxHeartbeats 400000 in
theorem carries_of_eEc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hCW hEx hSch hTw hHk hPG hIx c hc
  obtain ⟨Tc, hTc, hx⟩ := GlobalTheory.T.operatorFamily_adjointLift_single_eigensystem R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  by_cases h0 : ∀ w ∈ R.EEc c, LinearMap.adjoint (R.Th A3.A.μ0) w = 0
  · obtain ⟨p⟩ := hIx
    refine ⟨p, hc, ?_⟩
    rewrite [Submodule.map_le_iff_le_comap]
    intro w hw
    have h := h0 w hw
    simp only [Submodule.mem_comap, h, Submodule.zero_mem]
  push_neg at h0
  obtain ⟨w, hw, hne⟩ := h0
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  refine ⟨p, hc, map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

end GlobalTheory.Div
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEigensystemCarriedByFiniteTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowEigensystem_carried_by_finite_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  first | exact @GlobalTheory.Div.carries_of_eEc_ne_bot | exact GlobalTheory.Div.carries_of_eEc_ne_bot | (intros; apply GlobalTheory.Div.carries_of_eEc_ne_bot <;> assumption)
end
