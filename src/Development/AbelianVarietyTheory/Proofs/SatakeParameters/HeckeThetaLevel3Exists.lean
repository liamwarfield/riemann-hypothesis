module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSeparatingInertEigenvaluePassage
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodRationalEigenformHittingCarriedPart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryRowOperatorIsLabelOperatorWithPartner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfType
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Fwd

theorem sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V)
    (op : I → Module.End K V) (opC : I → Module.End ℂ W)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (hint : ∀ i x, j (op i x) = opC i (j x)) (hc : Formalism.L2.Col.PairComm opC) (Q : (I → K) → Prop) {u : W}
    (hu : u ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V))) (hu0 : u ≠ 0) {y : I → ℂ}
    (hy : ∀ i, opC i u = y i • u) : ∃ s, Q s ∧ y = fun i => σ (s i) := by
  have h1 := (GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp hint).2.1 Q
  rw [h1] at hu
  by_contra hne
  have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ∃ s, Q s ∧ x = fun i => σ (s i)) (C' := fun x => x = y)
    (fun x hx h => hne (h ▸ hx))
  have hu' : u ∈ Formalism.L2.Col.eigSum opC (fun x => x = y) :=
    Formalism.L2.Col.eigAt_le_eigSum (op := opC) (C := fun x => x = y) rfl (Formalism.L2.Col.mem_eigAt_of_forall_apply hy)
  exact hu0 ((Submodule.disjoint_def.1 hd) u hu hu')

end GlobalTheory.Hk3.Fwd


open GlobalTheory.Hk3.Fwd in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Hk3.passage_of_carried : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos hB hTr j pl cV cW hLD p c hCar hW
  obtain ⟨sy, x, hxg, hxe, hxW, hx0, hlab⟩ :=
    GlobalTheory.T.exists_good_rational_eigenform_hitting_carried_part hHowe R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos j pl cV cW hLD p c hCar hW
  obtain ⟨hCore, hSF, -, -, hEE, hWW, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCar.1
  have hu0 := GlobalTheory.T.upward_theta_lift_injective_on_carried_part R F hB hPos p c hCar w hw hw0
  obtain ⟨hOpsX, hOpsV⟩ := GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models
  obtain ⟨hX, hXo, hXn⟩ := hOpsX A3.A.μ0
  obtain ⟨hV, hVo, -⟩ := hOpsV j A3.A.μ0
  obtain ⟨plX, cX, c0, hRD⟩ := GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hHowe R F hInt hC hEx hSch hJ A3.A.μ0
  have hsplit := GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 core.lev core.fam core.models
  have hM := core.models
  have hBx := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R A3.A.μ0).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX A3.A.μ0
  have hk := kForm_semi (R.jX A3.A.μ0) (R.HX A3.A.μ0).e (R.B.R A3.A.μ0).pres.extL (fun x => hM.jX A3.A.μ0 x) hinj
    (hrange.trans hBx.2.symm) (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hBx.1
  have hjop : ∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = hX (plX i) (cX i) (R.jX A3.A.μ0 f) := hRD.op hX hXo
  have hcomm : Formalism.L2.Col.PairComm (fun i => hX (plX i) (cX i)) := fun a b => hXn.1 _ _ (hRD.good a) (hRD.good b) _ _
  have hwE : w ∈ EEc R.toRealDat R.SF c := hEE c ▸ hw
  have hy : ∀ i, hX (plX i) (cX i) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
      evC (Yc D 0) (plX i) (fun d => c (plX i) (dualLab d)) (c0 i) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i =>
    (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 core hSch R.SF hSF A3.A.μ0 (plX i) (hRD.good i) (cX i) (c0 i) (hRD.mat i) hX hXo).2 c w hwE
  have hu : LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (R.jX A3.A.μ0 ''
      (Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll ((A3.rowI A3.A.μ0).HasRes3 p.1) : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hCar.2 (Submodule.mem_map_of_mem hw)
  obtain ⟨sR, hsR, hyR⟩ := sys_of_mem_span D.what₂.embLL (R.jX A3.A.μ0) (Module.Basis.ofVectorSpace _ _)
    (A3.rowI A3.A.μ0).opAll (fun i => hX (plX i) (cX i)) hk.1 hk.2 hjop hcomm _ hu hu0 hy
  have hXs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ D.sp.X'.rank →
      hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
        D.what₂.embLL (sR (Sum.inl (P, k))) • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P k hkr
    have heq : hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) = hX (plX (Sum.inl (P, k))) (cX (Sum.inl (P, k))) := by
      refine LinearMap.ext_on hk.2 ?_
      rintro _ ⟨b, rfl⟩
      exact ((hsplit.1 A3.A.μ0 hX hXo P k hkr _).symm).trans (hjop (Sum.inl (P, k)) _)
    exact (LinearMap.congr_fun heq _).trans ((hy (Sum.inl (P, k))).trans
      (congrArg (fun z : ℂ => z • LinearMap.adjoint (R.Th A3.A.μ0) w) (congrFun hyR (Sum.inl (P, k)))))
  have hVs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ (Vc D j).rank →
      hV (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (sy (Sum.inl (P, k))) • R.jV j A3.A.μ0 x := by
    intro P k hkr
    have h1 : A3.A.heckeL j A3.A.μ0 (P, k) x = sy (Sum.inl (P, k)) • x := hxe (Sum.inl (P, k))
    exact (hsplit.2 j A3.A.μ0 hV hVo P k hkr x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) h1).trans ((R.jV j A3.A.μ0).map_smulₛₗ _ x))
  have hL := GlobalTheory.T.liftSplitHeckePolys_eq_transfer_residualPolys R.toRealDat F.lv2 hInt core hSch hOk.ok2.irr R.SF hSF j c p.1.1 (fun i => sR (Sum.inl i))
    (fun i => sy (Sum.inl i)) hsR.1 hX hV hXo hVo w hwE hu0 hXs (R.jV j A3.A.μ0 x) (hWW j c ▸ hxW) hx0 hVs
  exact ⟨sy, ⟨hL, hTr j p c hCar sy ⟨x, hxg, hxe, hxW, hx0⟩⟩, hlab⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriedPart_eigensystem_passage_of_type : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) := by
  first | exact @GlobalTheory.Hk3.passage_of_carried | exact GlobalTheory.Hk3.passage_of_carried | (intros; apply GlobalTheory.Hk3.passage_of_carried <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassage
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseLevelVectorInGoodAlgebraicFormsSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseLevelVectorInGoodAlgebraicFormsSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3

theorem exists_part_level_vector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hSch s hOk hGG hU j c hne
  obtain ⟨hCoreF, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hW
  have hCore := hCoreF hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨h, -, -, -, hsup, hstab, -, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hX R.SF hSF j
  obtain ⟨hid, -, -, -⟩ := eH_laws R.toRealDat F.lv2 hCore hX j
  have hfix : ∀ u ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j u = u := by
    intro u hu
    have hr : u ∈ LinearMap.range (eH R.toRealDat j) := hsup ▸ (le_iSup (fun c => Wcc R.toRealDat R.SF j c) c) hu
    obtain ⟨x, rfl⟩ := hr
    rw [← Module.End.mul_apply, hid]
  rw [hWc] at hne ⊢
  obtain ⟨u, huU, hu0, hup⟩ := GlobalTheory.T.exists_level_vector_goodType_stable_subspace (sg0 D A3.A) A3.A.X F.P0 F.ψ0⁻¹ (R.gW j (sg0 D A3.A))
    (Wcc R.toRealDat R.SF j c) hX hGG (fun g => hstab c g) hne (fun u hu => by
      have := hfix u hu
      simpa [eH, RealDat.eC] using this)
  refine ⟨u, huU, hu0, ?_⟩
  have hlev := (GlobalTheory.T.goodForms_baseLevel_iff_goodProjection R.toRealDat F.lv2 hCore hX j u).2 ⟨hfix u huU, hup⟩
  have hL := GlobalTheory.LevelForms.levelW_of_irr R.toRealDat F.lv2 hX hU hCore.models.HW
  rw [hL false j (sg0 D A3.A)]
  exact hlev

end GlobalTheory.Hk3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBaseLevelVectorInGoodAlgebraicFormsSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseLevel_vector_in_goodAlgebraicForms_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) := by
  first | exact @GlobalTheory.Hk3.exists_part_level_vector | exact GlobalTheory.Hk3.exists_part_level_vector | (intros; apply GlobalTheory.Hk3.exists_part_level_vector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Back

theorem exists_level_vec_in_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → (R.toCx3 F).PartsW false → ∀ j c, R.Wc' j c ≠ ⊥ → ∃ w ∈ R.Wc' j c, w ≠ 0 ∧ w ∈ ⨆ p, R.Wp3 j p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  obtain ⟨w, hw, hw0, hws⟩ := GlobalTheory.T.exists_baseLevel_vector_in_goodAlgebraicForms_span R F hCW hEx hSch s hOk hGG hLU j c h0
  exact ⟨w, hw, hw0, GlobalTheory.T.mem_iSup_type_parts_of_good_base_forms R F hParts j w hws⟩

theorem blockProd_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (P : B.Pl) : B.blockProd P ≠ 0 := by
  unfold BlockDat.blockProd
  rw [ne_eq, List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  intro ν _ h
  unfold Formalism.L2.Col.blockPoly at h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨c, _, hc⟩ := h
  have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) hc
  simp at this

theorem eig_in_sum {H : Type} [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H] {Q J K : Type} (ok : Q → Prop)
    (h : Q → J → Module.End ℂ H) (ev : K → Q → J → ℂ) (V : K → Submodule ℂ H) (S : K → Prop) (k0 : K)
    (hc : ∀ P P', ok P → ok P' → ∀ c c', Commute (h P c) (h P' c'))
    (hev : ∀ k P, ok P → ∀ cc, ∀ x ∈ V k, h P cc x = ev k P cc • x)
    (w : H) (hw : w ∈ V k0) (hw0 : w ≠ 0) (hwS : w ∈ ⨆ (k : K) (_ : S k), V k) :
    ∃ k, S k ∧ ∀ P, ok P → ∀ cc, ev k P cc = ev k0 P cc := by
  classical
  let op : {P // ok P} × J → Module.End ℂ H := fun i => h i.1.1 i.2
  have hpc : Formalism.L2.Col.PairComm op := fun i i' => hc _ _ i.1.2 i'.1.2 _ _
  let χ : K → {P // ok P} × J → ℂ := fun k i => ev k i.1.1 i.2
  have hV : ∀ k, V k ≤ Formalism.L2.Col.eigAt op (χ k) := fun k x hx =>
    Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hev k i.1.1 i.1.2 i.2 x hx
  by_contra hne
  push_neg at hne
  have h1 : (⨆ (k : K) (_ : S k), V k) ≤ Formalism.L2.Col.eigSum op (fun x => x ≠ χ k0) := by
    refine iSup₂_le fun k hk => (hV k).trans (Formalism.L2.Col.eigAt_le_eigSum ?_)
    intro he
    obtain ⟨P, hP, cc, hcc⟩ := hne k hk
    exact hcc (congrFun he (⟨P, hP⟩, cc))
  have h2 : V k0 ≤ Formalism.L2.Col.eigSum op (fun x => x = χ k0) :=
    (hV k0).trans (Formalism.L2.Col.eigAt_le_eigSum rfl)
  have hd := Formalism.L2.Col.disjoint_eigSum (op := op) hpc (C := fun x => x = χ k0) (C' := fun x => x ≠ χ k0)
    (fun x h h' => h' h)
  exact hw0 ((Submodule.disjoint_def.1 hd) w (h2 hw) (h1 hwS))

theorem types_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (hSep : A3.fam3.TypesSep3) (j : Fin D.R.m)
    (p p' : A3.fam3.base3.Ix) (y : (A3.liftI j A3.A.μ0).OpIx → ℂ)
    (hp : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) y)
    (hp' : cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p'.1)) y) : p = p' := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨x', hx', hxx⟩ := hp'
  have hxe : x = x' := funext fun i => D.what₂.embLL.injective (congrFun hxx i)
  subst hxe
  by_contra hne
  have hne' : p.1 ≠ p'.1 := fun h => hne (Subtype.ext h)
  rcases hSep p.1 p.2 p'.1 p'.2 hne' j with ⟨P, hP⟩ | ⟨k, hk⟩
  · apply hP
    have h1 := hx.1 P
    have h2 := hx'.1 P
    rw [h1] at h2
    exact mul_right_cancel₀ (blockProd_ne_zero _ P) h2
  · exact hk ((hx.2 k).symm.trans (hx'.2 k))

theorem wc_le_wp_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr hParts hSep j pl cV cW hLD p c hsys
  obtain ⟨hcoreF, hSF, -, -, -, hWeq, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hCW
  have hcore := hcoreF hEx
  obtain ⟨h, -, hNorm, -, hsum, -, hev, hchar⟩ :=
    GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hcore hSch hOk.ok2.irr R.SF hSF j
  have hidem := (eH_laws R.toRealDat F.lv2 hcore hOk.ok2.irr j).1
  by_cases h0 : R.Wc' j c = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨w, hwc, hw0, hwp⟩ := exists_level_vec_in_parts R F hCW hEx hSch s hOk hGG hLU hParts j c h0
  have hwp' : w ∈ ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
    have hle : (⨆ p, R.Wp3 j p) ≤
        ⨆ (c' : Pl D.host.E → List ℤ → ℂ) (_ : ∃ p', R.Carries p' c'), Wcc R.toRealDat R.SF j c' := by
      refine iSup_le fun p' => iSup₂_le fun c' hc' => ?_
      rw [hWeq]
      exact le_iSup₂_of_le (f := fun c' (_ : ∃ p', R.Carries p' c') => Wcc R.toRealDat R.SF j c') c' ⟨p', hc'⟩ le_rfl
    exact hle hwp
  rw [hWeq] at hwc
  obtain ⟨c', ⟨p', hcar⟩, hag⟩ := eig_in_sum (Good R.toRealDat A3.A.μ0) h
    (fun c P cc => evC (Wc D j) P (c P) cc) (Wcc R.toRealDat R.SF j) (fun c' => ∃ p', R.Carries p' c') c hNorm.1
    (fun k P hP cc x hx => hev k P hP cc x hx) w hwc hw0 hwp'
  have hsub : Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro x hx
    refine hchar c' x ?_ ?_
    · have hr : x ∈ LinearMap.range (eH R.toRealDat j) := hsum ▸ (le_iSup (Wcc R.toRealDat R.SF j) c hx)
      obtain ⟨y, rfl⟩ := hr
      rw [← Module.End.mul_apply, hidem]
    · intro P d hP hd
      rw [hev c P hP _ x hx, ← hag P hP]
      simp [evC, hd]
  have hne : R.Wc' j c' ≠ ⊥ := by
    rw [hWeq]
    intro hb
    exact hw0 ((Submodule.eq_bot_iff _).1 hb w (hsub hwc))
  have hfwd := GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hCW hEx hSch hJunk s hOk hGG hLU hPGU hPGE hPLW hA hPos hB hTr j pl cV cW hLD p' c' hcar hne
  have hlab : labW j pl cW c' = labW j pl cW c := funext fun i => hag (pl i) (hLD.good i) (cW i)
  rw [hlab] at hfwd
  have hpp : p' = p := types_eq hSep j p' p _ hfwd hsys
  subst hpp
  rw [hWeq]
  refine hsub.trans ?_
  rw [← hWeq]
  exact le_iSup₂_of_le (f := fun c (_ : R.Carries p' c) => R.Wc' j c) c' hcar le_rfl

end GlobalTheory.Hk3.Back
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassageStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenPart_le_typePart_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  first | exact @GlobalTheory.Hk3.Back.wc_le_wp_of_passage | exact GlobalTheory.Hk3.Back.wc_le_wp_of_passage | (intros; apply GlobalTheory.Hk3.Back.wc_le_wp_of_passage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryLiftOperatorIsLabelOperatorWithPartner
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryLiftOperatorIsLabelOperatorWithPartner
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDictionary

set_option maxHeartbeats 4000000

variable {D : D7} {G : Type} [Group G] [Fintype G] {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Zero

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem hk_zero (V : HSp D) (P : Pl D.host.E) : hk V P 0 = 0 := Finsupp.sum_zero_index

theorem postOn_zero (V : HSp D) {S} (M : DSModel V S) (T : MMap M) : postOn M 0 T = 0 := by
  ext v
  simp [postOn]

theorem hkF_zero (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (F : Bridge.Gf V → W) : hkF V P 0 F = 0 := by
  funext g
  exact Finsupp.sum_zero_index

theorem ops_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (y : (R.HV j t).H) : h P 0 y = 0 := by
  refine (hM.HV j t).1 ?_
  rw [hh P hP 0 y, map_zero]
  exact hkF_zero _ _ _

theorem match_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) : MatchW R j t P 0 0 := by
  intro y y' hy
  have h0 : y' = 0 := by
    refine (hM.HV j t).1 ?_
    rw [hy, map_zero]
    exact hkF_zero _ _ _
  have e1 : (R.thG j t) y' = 0 := by rw [h0]; exact (R.thG j t).map_zero
  have e2 : (R.HW j (sg0 D A)).e ((R.thG j t) y') = 0 := by rw [e1]; exact (R.HW j (sg0 D A)).e.map_zero
  refine e2.trans ?_
  rw [hk_zero]
  exact (postOn_zero _ _ _).symm

theorem op_zero (hM : R.IsModels) (j : Fin D.R.m) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (o : Module.End D.what₂.LL (A.MtCSD j t).Forms) (ho : o = 0)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H) (hh : IsOpsV R j t h) (x : (A.MtCSD j t).Forms) :
    R.jV j t (o x) = h P 0 (R.jV j t x) := by
  rw [ops_zero R hM j t P hP h hh, ho, LinearMap.zero_apply]
  exact (R.jV j t).map_zero

end Zero

section Cases

variable {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks)

theorem split_good (F : Face D A) (core : Core R F) (t : T) (P : A.ok t) : Good R t (R.pl P) :=
  ((GlobalTheory.GoodPrimes.good_primes R F core.lev).2.2.2 core.fam t P P.2).1

theorem split_low (F : Face D A) (core : Core R F) (hS : SchurAll R) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.thetaLift_transfer_heckePoly_splitPrime R F core hS j t P
  exact ⟨R.pl P, Finsupp.single (splitLab (Vc D j).rank k) 1, splitC (Wc D j).rank (z k), split_good R F core t P,
    fun h hh x => (GlobalTheory.SplitHeckeLabel.split_ops R F core.lev core.fam core.models).2 j t h hh P k hk x, hz k hk⟩

theorem split_high (F : Face D A) (core : Core R F) (j : Fin D.R.m) (t : T) (P : A.ok t) (k : ℕ)
    (hk : ¬ k ≤ (Vc D j).rank) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R t pl ∧
      (∀ h, IsOpsV R j t h → ∀ x, R.jV j t (A.heckeL j t (P, k) x) = h pl cV (R.jV j t x)) ∧ MatchW R j t pl cV cW := by
  have h0 : A.heckeL j t (P, k) = 0 := (core.fam.degL j t P).2 k (not_le.1 hk)
  have hg := split_good R F core t P
  refine ⟨R.pl P, 0, 0, hg, fun h hh x => ?_, match_zero R core.models j t _⟩
  exact op_zero R core.models j t (R.pl P) hg (A.heckeL j t (P, k)) h0 h hh x

end Cases

section Inert

variable {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} (R : RealDat3 D A3 Ks) (F : Face3 D A3)

theorem inert_valid (hH : HoweUnram) (hI : GlobalTheory.Chain.LiftInteg D) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hS : SchurAll R.toRealDat) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (hs : Formalism.L2.Col.InertTypeOk (Vc D j).rank s) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, hconj⟩ := hGoodI t Q Q.2
  have two := GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hI core hS t (R.plI Q) hg hconj (GlobalTheory.T.hyperspecialFixesAllChainVacua_at_inert_prime R F hC t _ hg hconj)
  obtain ⟨cW, hW⟩ := (two.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1)
  refine ⟨R.plI Q, Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s) 1, cW, hg, fun h hh x => ?_, hW⟩
  have hty : ∀ i : A3.okI t × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2 →
      Good R.toRealDat t (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    intro i hi
    obtain ⟨g1, g2⟩ := hGoodI t i.1 i.1.2
    exact ⟨g1, g2, ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank _).2 ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩
  exact (GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 core.lev core.fam core.models j t (A3.okI t × List ℕ) (fun i => R.plI i.1)
    (fun i => GlobalTheory.Hk3.labIn (Vc D j).rank i.2) (A3.heckeLI j t) (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2) hty
    (hC.inert.hL j t).some (Q, s) hs).2.2.2 h hh x

theorem inert_vanish (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m) (t : T) (Q : A3.okI t) (s : List ℕ)
    (h0 : A3.heckeLI j t (Q, s) = 0) :
    ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t (A3.heckeLI j t (Q, s) x) = h pl cV (R.jV j t x)) ∧
        MatchW R.toRealDat j t pl cV cW := by
  obtain ⟨hCore, -, hGoodI, -, -, -, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨hg, -⟩ := hGoodI t Q Q.2
  refine ⟨R.plI Q, 0, 0, hg, fun h hh x => ?_, match_zero R.toRealDat core.models j t _⟩
  exact op_zero R.toRealDat core.models j t (R.plI Q) hg (A3.heckeLI j t (Q, s)) h0 h hh x

end Inert

theorem every_op_label : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ j t, ∃ pl cV cW, LiftDict R j t pl cV cW := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hI hC hEx hS hJ j t
  have core := (GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC).1 hEx
  have key : ∀ i : (A3.liftI j t).OpIx, ∃ (pl : Pl D.host.E) (cV cW : List ℤ →₀ ℂ), Good R.toRealDat t pl ∧
      (∀ h, IsOpsV R.toRealDat j t h → ∀ x, R.jV j t ((A3.liftI j t).opAll i x) = h pl cV (R.jV j t x)) ∧
      MatchW R.toRealDat j t pl cV cW := by
    rintro (⟨P, k⟩ | ⟨Q, s⟩)
    · by_cases hk : k ≤ (Vc D j).rank
      · exact split_low R.toRealDat F.lv2 core hS j t P k hk
      · exact split_high R.toRealDat F.lv2 core j t P k hk
    · rcases hJ.L j t Q s with h0 | ⟨s', hs', he⟩
      · exact inert_vanish R F hC hEx j t Q s h0
      · have hrank : A3.A.r + A3.A.t = (Vc D j).rank := (R.B.rankL j).symm
        rw [hrank] at hs'
        obtain ⟨pl, cV, cW, g, o, m⟩ := inert_valid R F hH hI hC hEx hS j t Q s' hs'
        refine ⟨pl, cV, cW, g, fun h hh x => ?_, m⟩
        have e : (A3.liftI j t).opAll (Sum.inr (Q, s)) = A3.heckeLI j t (Q, s') := he
        rw [e]
        exact o h hh x
  choose pl cV cW h1 h2 h3 using key
  exact ⟨pl, cV, cW, ⟨h1, fun h hh i x => h2 i h hh x, h3⟩⟩

end GlobalTheory.LiftDictionary

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryLiftOperatorIsLabelOperatorWithPartnerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_liftOperator_is_labelOperator_with_partner : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ j t, ∃ pl cV cW, LiftDict R j t pl cV cW := by
  first | exact @GlobalTheory.LiftDictionary.every_op_label | exact GlobalTheory.LiftDictionary.every_op_label | (intros; apply GlobalTheory.LiftDictionary.every_op_label <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZeroPassage

theorem dualPoly_coeff_zero {K : Type} [Field K] (s : K) (p : K[X]) (hp : p ≠ 0) : (dualPoly s p).coeff 0 = 1 := by
  unfold dualPoly
  rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_comp]
  simp [← coeff_zero_eq_eval_zero, hp]

theorem heckePoly_zero {L Pl : Type} [Field L] (n : ℕ) (q : Pl → ℕ) (P : Pl) :
    Formalism.L2.Col.heckePoly n q (fun _ => (0 : L)) P = 0 := by
  simp [Formalism.L2.Col.heckePoly, Formalism.L2.Col.heckePolyOf]

theorem mem_resSet_of_mem_ixFin3 {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 I0 Ty : Type} {B : BlockDat K G Pl0} (D : InertDat3 B I0 Ty) {X : Finset (G → K)}
    {p : Typ3 K Pl0 I0 Ty} (hp : p ∈ D.ixFin3 X) : p.1 ∈ B.resSet X := by
  unfold InertDat3.ixFin3 at hp
  split_ifs at hp with hfin
  · rw [Set.Finite.mem_toFinset] at hp
    refine ⟨hp.1, fun hb => hp.2.2 ?_⟩
    have hle : D.inertTypeEigenspaceSum p ≤ B.partF p.1 := by
      refine iSup₂_le fun x hx => ?_
      refine le_trans ?_ (Formalism.L2.Col.eigAt_le_eigSum (op := B.op) (C := B.HasRes p.1) (x := fun i => x (Sum.inl i)) hx.1)
      exact le_iInf fun i => iInf_le (fun k => (D.opAll k).maxGenEigenspace (x k)) (Sum.inl i)
    rw [eq_bot_iff] at hb ⊢
    exact le_trans (Submodule.comap_mono (Submodule.map_mono hle)) hb
  · simp at hp

theorem zero_not_passage : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ j (p : A3.fam3.base3.Ix), ¬ cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h j p
  rintro ⟨x, hx, hx0⟩
  obtain ⟨P, hP⟩ := (GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F h).2.2.2.2.2.2
  have hxz : (fun i => x (Sum.inl i)) = fun _ => (0 : D.what₂.LL) := by
    funext i
    have h1 := congrFun hx0 (Sum.inl i)
    exact (map_eq_zero_iff _ D.what₂.embLL.injective).1 h1.symm
  let P' : (A3.A.fam.L j A3.A.μ0).Pl := ⟨P, hP⟩
  have hres := hx.1 P'
  rw [hxz] at hres
  replace hres := (heckePoly_zero (L := D.what₂.LL) (Pl := (A3.A.fam.L j A3.A.μ0).Pl) _ _ _).symm.trans hres
  have hmem : p.1.1 ∈ (A3.A.fam.R A3.A.μ0).resSet A3.A.X := mem_resSet_of_mem_ixFin3 (A3.rowI A3.A.μ0) p.2
  have hc : (p.1.1 P).coeff 0 = 1 :=
    (A3.A.fam.R A3.A.μ0).lf_coeff_zero_of_mem_resSet (fun Q => (h.base.fam.degR A3.A.μ0 Q).1) hmem P
  have hne : p.1.1 P ≠ 0 := fun h0 => by rw [h0, coeff_zero] at hc; exact zero_ne_one hc
  have hb : ((A3.A.fam.L j A3.A.μ0).blockProd P').coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]; exact (A3.A.fam.L j A3.A.μ0).lf_blockProd_eval_zero P'
  have ht : ((A3.fam3.tr3 j p.1).1 ((A3.A.fam.L j A3.A.μ0).pl P')).coeff 0 = 1 := dualPoly_coeff_zero _ _ hne
  have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) hres
  simp only [coeff_zero, mul_coeff_zero, hb, ht, mul_one] at h2
  exact zero_ne_one h2

end GlobalTheory.ZeroPassage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteTypeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_eigensystem_not_passage_of_finiteType : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ j (p : A3.fam3.base3.Ix), ¬ cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
  first | exact @GlobalTheory.ZeroPassage.zero_not_passage | exact GlobalTheory.ZeroPassage.zero_not_passage | (intros; apply GlobalTheory.ZeroPassage.zero_not_passage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigSumMulProjEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIInfOfApply
namespace GlobalTheory.IndependentInfimum

open Module

theorem le_of_indep {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : X → Submodule K V) (hW : iSupIndep W) (hUW : ∀ x, U x ≤ W x)
    (hU : ⨆ x, U x = ⊤) (x : X) : W x ≤ U x := by
  classical
  intro w hw
  have htop : w ∈ ⨆ y, U y := by rw [hU]; exact Submodule.mem_top
  have hsplit : (⨆ y, U y) = U x ⊔ ⨆ (y) (_ : y ≠ x), U y := by
    apply le_antisymm
    · refine iSup_le fun y => ?_
      by_cases hy : y = x
      · subst hy
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le y hy le_rfl)
    · exact sup_le (le_iSup U x) (iSup₂_le fun y _ => le_iSup U y)
  rw [hsplit] at htop
  obtain ⟨u, hu, w', hw', hsum⟩ := Submodule.mem_sup.1 htop
  have hw'W : w' ∈ ⨆ (y) (_ : y ≠ x), W y :=
    (iSup₂_mono fun y _ => hUW y) hw'
  have hdiff : w - u ∈ W x := W x |>.sub_mem hw (hUW x hu)
  have heq : w - u = w' := by rw [← hsum]; abel
  have hdis := (hW x).le_bot (Submodule.mem_inf.2 ⟨hdiff, heq ▸ hw'W⟩)
  rw [Submodule.mem_bot, sub_eq_zero] at hdis
  rw [hdis]
  exact hu

theorem mem_iInf_of_apply {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : I → Module.End K V) (x : I → K) (v : V) (hv : ∀ i, A i v = x i • v) :
    v ∈ ⨅ i, (A i).maxGenEigenspace (x i) := Submodule.mem_iInf _ |>.2 fun i =>
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (hv i))

theorem main {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hE : ⨆ (c : C), Ec c = LinearMap.range e)
    (hl : ∀ (c : C), ∀ w ∈ Ec c, ∀ (i : I), (h i : E → E) w = lab c i • w) :
    (Formalism.L2.Col.PairComm fun (i : I) ↦ h i * e) ∧ ∀ (Q : (I → ℂ) → Prop), ¬Q (0 : I → ℂ) →
      Formalism.L2.Col.eigSum (fun (i : I) ↦ h i * e) Q = ⨆ (c : C), ⨆ (_ : Q (lab c)), Ec c := by
  classical
  have hee : ∀ v, e (e v) = e v := fun v => by
    have := congrArg (fun f : Module.End ℂ E => f v) he
    simpa using this
  have hfix : ∀ c, ∀ w ∈ Ec c, e w = w := by
    intro c w hw
    have : w ∈ LinearMap.range e := hE ▸ Submodule.mem_iSup_of_mem c hw
    obtain ⟨u, rfl⟩ := this
    exact hee u
  have hA : ∀ c, ∀ w ∈ Ec c, ∀ i, (h i * e) w = lab c i • w := by
    intro c w hw i
    rw [Module.End.mul_apply, hfix c w hw, hl c w hw]
  have hcomm : ∀ i j, Commute (h i * e) (h j * e) := by
    intro i j
    have key : ∀ w ∈ ⨆ c, Ec c, (h i * e) ((h j * e) w) = (h j * e) ((h i * e) w) := by
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem c w hw =>
        rw [hA c w hw j, hA c w hw i, map_smul, map_smul, hA c w hw j, hA c w hw i, smul_comm]
      | zero => simp
      | add a b _ _ ha hb => simp only [map_add (f := _), ha, hb]
    ext v
    have hv : e v ∈ ⨆ c, Ec c := by rw [hE]; exact ⟨v, rfl⟩
    have := key _ hv
    simpa [Module.End.mul_apply, hee] using this
  refine ⟨hcomm, fun Q hQ => ?_⟩
  have hind : iSupIndep fun x : I → ℂ => ⨅ i, (h i * e).maxGenEigenspace (x i) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun i => h i * e)
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  let U : (I → ℂ) → Submodule ℂ E := fun x =>
    (⨆ (c : C) (_ : lab c = x), Ec c) ⊔ ⨆ (_ : x = 0), LinearMap.ker e
  have hUW : ∀ x, U x ≤ ⨅ i, (h i * e).maxGenEigenspace (x i) := by
    intro x
    refine sup_le (iSup₂_le fun c hc w hw => ?_) (iSup_le fun hx w hw => ?_)
    · exact mem_iInf_of_apply (fun i => h i * e) x w fun i => hc ▸ hA c w hw i
    · refine mem_iInf_of_apply (fun i => h i * e) x w fun i => ?_
      rw [LinearMap.mem_ker] at hw
      simp [hx, Module.End.mul_apply, hw]
  have hU : ⨆ x, U x = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : LinearMap.range e ≤ ⨆ x, U x := by
      rw [← hE]
      exact iSup_le fun c => le_iSup_of_le (lab c)
        (le_sup_of_le_left (le_iSup₂_of_le (f := fun c' (_ : lab c' = lab c) => Ec c') c rfl le_rfl))
    have h2 : LinearMap.ker e ≤ ⨆ x, U x :=
      le_iSup_of_le 0 (le_sup_of_le_right
        (le_iSup_of_le (f := fun _ : (0 : I → ℂ) = 0 => LinearMap.ker e) rfl le_rfl))
    have h3 : v - e v ∈ LinearMap.ker e := by simp [LinearMap.mem_ker, hee]
    have := Submodule.add_mem _ (h1 ⟨v, rfl⟩) (h2 h3)
    simpa using this
  unfold Formalism.L2.Col.eigSum Formalism.L2.Col.eigAt
  apply le_antisymm
  · refine iSup₂_le fun x hx => (le_of_indep U _ hind hUW hU x).trans ?_
    refine sup_le (iSup₂_le fun c hc => ?_) (iSup_le fun h0 => absurd (h0 ▸ hx) hQ)
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c (hc ▸ hx) le_rfl
  · refine iSup₂_le fun c hc => ?_
    refine le_iSup₂_of_le
      (f := fun (x : I → ℂ) (_ : Q x) => ⨅ i, (h i * e).maxGenEigenspace (x i)) (lab c) hc ?_
    intro w hw
    exact mem_iInf_of_apply (fun i => h i * e) (lab c) w (hA c w hw)

end GlobalTheory.IndependentInfimum
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3


open _root_.Formalism.L2.Col in
theorem eigSum_mul_proj_eq {E I C : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hr : (⨆ c, Ec c) = LinearMap.range e)
    (hh : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    PairComm (fun i => h i * e) ∧ ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
      eigSum (fun i => h i * e) Q = ⨆ (c : C) (_ : Q (lab c)), Ec c := by
  first
  | exact @_root_.GlobalTheory.IndependentInfimum.main
  | exact _root_.GlobalTheory.IndependentInfimum.main
  | (apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndependentInfimum.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndependentInfimum.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndependentInfimum.main ..)

end GlobalTheory.Hk3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3Exists
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem tw_cut_eig (s : Bool) {E I C : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hs : (⨆ c, Ec c) = LinearMap.range e) (hl : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) ∧
      ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
        Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) Q =
          Tw.sub s (⨆ (c : C) (_ : Q (fun i => cj s (lab c i))), Ec c) := by
  obtain ⟨hc, hq⟩ := GlobalTheory.Hk3.eigSum_mul_proj_eq h e Ec lab he hs hl
  obtain ⟨a, b, -⟩ := GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup s (fun i => h i * e)
  refine ⟨a hc, fun Q hQ => ?_⟩
  have h0 : (fun i => cj s ((0 : I → ℂ) i)) = 0 := by funext i; simp
  rw [b Q, hq _ (by rw [h0]; exact hQ)]

theorem cxSys_cj_iff {K I : Type} [Field K] {σ τ : K →+* ℂ} {s : Bool} (h : ∀ a, σ a = cj s (τ a)) (H : (I → K) → Prop) (y : I → ℂ) :
    cxSys σ H (fun i => cj s (y i)) ↔ cxSys τ H y := by
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨x, hx, funext fun i => ?_⟩
    have := congrFun e i
    simp only [h] at this
    simpa [cj_cj] using congrArg (cj s) this
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, funext fun i => (h _).symm⟩

set_option maxHeartbeats 2000000 in
theorem heckeTheta_level3_exists_alt : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW := by
  intro hHowe hHC hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hC hEx hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hParts hTS hPin
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hCoreE, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreE hEx
  have hSch : SchurAll R.toRealDat :=
    ⟨fun _ _ _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      fun _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2⟩
  have hTr := (hPin (GlobalTheory.T.exists_separating_inert_eigenvalue_passage hHowe R F hLI hC hEx hSch hJ hirr hB hPos)).1
  have hOps := fun i => GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hirr R.SF hSF i
  choose h hIsW hNorm hGc hSup hInv hEig hChar using hOps
  have hDict := GlobalTheory.T.every_liftOperator_is_labelOperator_with_partner hHowe R F hLI hC hEx hSch hJ
  choose pl cV cW hD using hDict
  have hLaws := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hirr
  have hcut := fun j => tw_cut_eig (twAt D.what₂.embLL A3.A.v0) (fun i => h j (pl j A3.A.μ0 i) (cW j A3.A.μ0 i)) (eH R.toRealDat j)
    (Wcc R.toRealDat R.SF j) (fun c => labW j (pl j A3.A.μ0) (cW j A3.A.μ0) c) (hLaws j).1 (hSup j)
    (fun c w hw i => hEig j c _ ((hD j A3.A.μ0).good i) _ w hw)
  refine ⟨fun j t i => Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j), ?_, ?_, ?_⟩
  · intro j t i u
    obtain ⟨hV, hVo, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).2 j t
    have hK := RealDat3.kFormL_of (R := R) (F := F) hCore.models
    have hop : (R.toCx3 F).opLC j t (Sum.inl i) = Tw.map (E := (R.HV j t).H) (F := (R.HV j t).H) (twAt D.what₂.embLL A3.A.v0) (hV (pl j t i) (cV j t i)) := by
      refine LinearMap.ext_on_range (hK j t).2 fun k => ?_
      rw [← CxData.jL_opL _ hK]
      show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j t ((A3.liftI j t).opAll i _)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (hV _ _ (R.jV j t _))
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hD j t).op hV hVo i _)
    have hs := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hCore hSch hirr R.SF hSF j t (pl j t i) ((hD j t).good i) _ _ ((hD j t).mat i) hV hVo).1 (h j) (hIsW j)
    rw [hop]
    show R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) =
      Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j)
        (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u)))
    rw [map_smul]
    congr 1
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) (eH R.toRealDat j (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))))
    rw [(hLaws j).2.2.2 t, hs]
  · intro j
    exact (hcut j).1
  · intro j p
    have hv := fun a => R.toRealDat.emb0 a
    have hQ0 : ¬ cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
      intro h0
      have h1 : (0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) = fun i => cj (twAt D.what₂.embLL A3.A.v0) ((0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) i) := by
        funext i; simp
      rw [h1] at h0
      exact GlobalTheory.T.zero_eigensystem_not_passage_of_finiteType R F hC j p ((cxSys_cj_iff hv _ _).1 h0)
    have key := (hcut j).2 _ hQ0
    show Tw.sub _ (R.Wp3 j p) = _
    refine Eq.trans ?_ key.symm
    congr 1
    apply le_antisymm
    · refine iSup₂_le fun c hc => ?_
      by_cases hne : R.Wc' j c = ⊥
      · rw [hne]; exact bot_le
      · exact le_iSup₂_of_le c ((cxSys_cj_iff hv _ _).2
          (GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr j _ _ _ (hD j A3.A.μ0) p c hc hne)) (hWc j c).le
    · refine iSup₂_le fun c hc => ?_
      rw [← hWc j c]
      exact GlobalTheory.T.eigenPart_le_typePart_of_passage hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr hParts hTS j _ _ _ (hD j A3.A.μ0) p c
        ((cxSys_cj_iff hv _ _).1 hc)

end GlobalTheory.Hk3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeThetaLevel3ExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTheta_level3_exists : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW := by
  first | exact @GlobalTheory.Hk3.heckeTheta_level3_exists_alt | exact GlobalTheory.Hk3.heckeTheta_level3_exists_alt | (intros; apply GlobalTheory.Hk3.heckeTheta_level3_exists_alt <;> assumption)
end
