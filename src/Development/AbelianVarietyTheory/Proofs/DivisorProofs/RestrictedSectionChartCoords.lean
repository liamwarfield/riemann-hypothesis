module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSKerRes

section Dictionary

variable {Y : Scheme.{0}} {M N : LB Y} {O W : Y.Opens}

theorem coord_resM (h : W ≤ O) (s : Γ(LB.toMod M, O)) (i : M.ι) :
    LB.coord (Twist.resM (LB.toMod M) h s) i = resG Y (inf_le_inf_right _ h) (LB.coord s i) :=
  LB.coord_map h s i

theorem le_tens (O : Y.Opens) (q : (tens M N).ι) : O ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 ⊓ M.U q.1 :=
  fun _ hy => ⟨⟨hy.1, hy.2.2⟩, hy.2.1⟩

def ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) : Γ(LB.toMod (tens M N), O) :=
  LB.mkSec (fun q => resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1)) fun p q => by
    have h₁ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U p.2 := fun _ hy => ⟨hy.1.1, hy.1.2.2⟩
    have h₂ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ O ⊓ N.U q.2 := fun _ hy => ⟨hy.1.1, hy.2.2⟩
    have h₃ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U p.1 := fun _ hy => hy.1.2.1
    have h₄ : O ⊓ (tens M N).U p ⊓ (tens M N).U q ≤ M.U q.1 := fun _ hy => hy.2.1
    have e₁ := congrArg (fun r => resG Y (le_inf le_rfl h₄) (LB.coord r q.1))
      (Twist.coord_rel s p.2 q.2 h₁ h₂ (le_inf (h₁.trans inf_le_right) (h₂.trans inf_le_right)))
    have e₂ := LB.coord_rel (Twist.coord s p.2) p.1 q.1 (le_inf h₁ h₃) (le_inf h₁ h₄) (le_inf h₃ h₄)
    simp only [coord_resM, LB.coord_smul, map_mul, LB.resG_resG] at e₁
    simp only [LB.resG_resG]
    refine e₂.trans ?_
    rw [e₁, ← mul_assoc]
    refine congrArg (· * _) ?_
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))).symm

theorem coord_ofTwistFun (s : Γ(twist (LB.toMod M) N, O)) (q : (tens M N).ι) :
    LB.coord (ofTwistFun s) q = resG Y (le_tens O q) (LB.coord (Twist.coord s q.2) q.1) := rfl

def ofTwist : Γ(twist (LB.toMod M) N, O) →+ Γ(LB.toMod (tens M N), O) where
  toFun := ofTwistFun
  map_zero' := LB.sec_ext fun q => by
    rw [coord_ofTwistFun, Twist.coord_zero, LB.coord_zero, map_zero, LB.coord_zero]
  map_add' s t := LB.sec_ext fun q => by
    rw [LB.coord_add, coord_ofTwistFun, coord_ofTwistFun, coord_ofTwistFun, Twist.coord_add, LB.coord_add, map_add (f := _)]

theorem tens_le (O : Y.Opens) (i : M.ι) (j : N.ι) : O ⊓ N.U j ⊓ M.U i ≤ O ⊓ (tens M N).U (i, j) :=
  fun _ hy => ⟨hy.1.1, hy.2, hy.1.2⟩

theorem tens_rel (f : Γ(LB.toMod (tens M N), O)) (i i' : M.ι) (j j' : N.ι) (h : W ≤ O ⊓ (tens M N).U (i, j))
    (h' : W ≤ O ⊓ (tens M N).U (i', j')) (hM : W ≤ M.U i ⊓ M.U i') (hN : W ≤ N.U j ⊓ N.U j') :
    resG Y h (LB.coord f (i, j)) = resG Y hM (M.g i i' : Γ(Y, M.U i ⊓ M.U i')) *
      resG Y hN (N.g j j' : Γ(Y, N.U j ⊓ N.U j')) * resG Y h' (LB.coord f (i', j')) := by
  refine (LB.coord_rel f (i, j) (i', j') h h' (le_inf (h.trans inf_le_right) (h'.trans inf_le_right))).trans ?_
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (LB.resG_resG _ _ _) (LB.resG_resG _ _ _))

theorem surjective_ofTwist (hM : M.IsLB) (hN : N.IsLB) :
    Function.Surjective (ofTwist : Γ(twist (LB.toMod M) N, O) → Γ(LB.toMod (tens M N), O)) := fun f => by
  let a : ∀ j : N.ι, Γ(LB.toMod M, O ⊓ N.U j) := fun j =>
    LB.mkSec (fun i => resG Y (tens_le O i j) (LB.coord f (i, j))) fun i i' => by
      simp only [LB.resG_resG]
      refine (tens_rel f i i' j j _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.1.2⟩)
        (by exact fun _ hy => ⟨hy.1.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.1.2⟩)).trans ?_
      exact congrArg (· * _) ((congrArg (_ * ·) (LB.resG_g_self hN _ _)).trans (mul_one _))
  have ha : ∀ j i, LB.coord (a j) i = resG Y (tens_le O i j) (LB.coord f (i, j)) := fun _ _ => rfl
  refine ⟨Twist.mkSec a fun j j' => LB.sec_ext fun i => ?_, LB.sec_ext fun q => ?_⟩
  · simp only [coord_resM, LB.coord_smul, ha, LB.resG_resG]
    refine (tens_rel f i i j j' _ (by exact fun _ hy => ⟨hy.1.1.1, hy.2, hy.1.2⟩)
      (by exact fun _ hy => ⟨hy.2, hy.2⟩) (by exact fun _ hy => ⟨hy.1.1.2, hy.1.2⟩)).trans ?_
    exact congrArg (· * _) ((congrArg (· * _) (LB.resG_g_self hM _ _)).trans (one_mul _))
  · refine (coord_ofTwistFun _ q).trans ?_
    exact (LB.resG_resG (tens_le O q.1 q.2) (le_tens O q) (LB.coord f q)).trans (LB.resG_self _ _)

variable {k : Type} [CommRing k] (p : Y ⟶ Sp k) {L : LB Y} {n l : ℤ}

def toH0 : Γ(twistZ (LB.toMod M) L n, O) →+ Vanishing.H0 p (tw M L n) O := ofTwist

theorem restricted_section_chart_coords (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι)
    (h : W ≤ O ⊓ (tw M L n).U (twIdx n i j)) (h' : W ≤ O ⊓ L.U j ⊓ M.U i) :
    resG Y h ((toH0 p s).loc (twIdx n i j)) = resG Y h' (LB.coord (Twist.zcoord s j) i) := by
  rw [Twist.zcoord, coord_resM, LB.resG_resG]
  exact LB.resG_resG _ _ _

theorem germ_of_global_section (s : Γ(twistZ (LB.toMod M) L n, O)) (i : M.ι) (j : L.ι) (y : Y) (hy : y ∈ O)
    (hi : y ∈ M.U i) (hj : y ∈ L.U j) :
    H0.germ (twIdx n i j) y hy (mem_tw_U.2 ⟨hi, hj⟩) (toH0 p s) =
      ger y (memInf (memInf hy hj) hi) (LB.coord (Twist.zcoord s j) i) := by
  have h : O ⊓ L.U j ⊓ M.U i ≤ O ⊓ (tw M L n).U (twIdx n i j) := fun _ hz => ⟨hz.1.1, mem_tw_U.2 ⟨hz.2, hz.1.2⟩⟩
  have e := congrArg (ger y (memInf (memInf hy hj) hi)) (restricted_section_chart_coords p s i j h le_rfl)
  rwa [ger_resG, ger_resG] at e

theorem global_section_mul (hM : M.IsLB) (hL : L.IsLB) (w : L.Sec) (h : n + 1 = l) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec w) h).app O s) = mulSec hM hL w h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, germ_of_global_section p _ i j y hy hi hj, germ_of_global_section p _ i j y hy hi hj,
      Twist.zcoord_mulSecOfEq_app, LB.coord_smul, map_mul, ger_resG, ger_resG, Twist.zfun_zofSec]

theorem exists_local (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) (h : n + 1 = l)
    (s : Γ(twistZ (LB.toMod M) L l, ⊤)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) (y : Y) :
    ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin d → Γ(twistZ (LB.toMod M) L n, W)),
      (twistZ (LB.toMod M) L l).presheaf.map (homOfLE le_top).op s =
        ∑ i, (Twist.mulSecOfEq (LB.toMod M) (Twist.zofSec (t i)) h).app W (m i) := by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf hi hj)
  have hVi : V.1 ≤ M.U i := e.trans inf_le_left
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ ⊤ ⊓ (tw M L l).U (twIdx l i j) := fun _ hz => ⟨trivial, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf le_top hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hV, fun a => (Twist.zchartEquiv hL n j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL l j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
    smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [coord_resM]
  erw [Twist.zcoord_resM]
  rw [coord_resM, LB.resG_resG, LB.resG_resG]

end Dictionary

section Main

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Main

theorem exists_global {k : Type} [Field k] {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (hY : IsProjOver (GlobalTheory.strHom k (X := Y)))
    (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB) {d : ℕ} (t : Fin d → L.Sec) {n l : ℤ} (h : n + 1 = l)
    (hreg : RegSeq hL (LB.toMod M) (List.ofFn t)) (hvan : VanishFrom L (LB.toMod M) 0) (hd : (d : ℤ) ≤ n + 1)
    (f : Vanishing.H0 p (tw M L l) ⊤) (hf : VanishesTo (cutIdeal hL t) 1 f) :
    ∃ μ : Fin d → Vanishing.H0 p (tw M L n) ⊤, f = ∑ i, mulSec hM hL (t i) h (μ i) := by
  subst h
  obtain ⟨σ, rfl⟩ : ∃ σ : Γ(twistZ (LB.toMod M) L (n + 1), ⊤), toH0 p σ = f :=
    surjective_ofTwist hM (Twist.isLB_lbZPow hL _) f
  have := (VB.isVB_toMod hM).isFiniteQC
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_global_combination_of_local_regular_ideal k Y hY L hL d t (LB.toMod M) 0 n hreg hvan ((zero_add _).trans_le hd) σ
    (exists_local p hM hL t rfl σ hf)
  refine ⟨fun i => toH0 p (m i), (congrArg (toH0 p) hm).trans ?_⟩
  exact (map_sum (toH0 p) _ _).trans (Finset.sum_congr rfl fun i _ => global_section_mul p hM hL _ rfl (m i))

theorem kerRes : Quoted → KerRes := by
  intro Q K _ _ G hnef hbig s hs l hl f hf
  obtain ⟨⟨f, rfl⟩, hv⟩ := mem_Fil.1 hf
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨g, hg, hreg⟩ := GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros K G s hs _ hB
  have hv' := vanishesTo_of_isUnit G s g hg ((vanishesTo_restr_iff hs.inU le_top).1 hv)
  have hproj : IsProjOver (GlobalTheory.strHom K (X := G.Y)) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  obtain ⟨μ, e⟩ := exists_global hproj G.str hB G.isLB _ (Nat.cast_succ l).symm hreg (GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist Q K G hnef hbig)
    (by exact_mod_cast hl) f hv'
  refine ⟨fun j => H0.restr le_top (∑ i, g i j • μ i), fun j => ⟨_, rfl⟩, ?_⟩
  have e' (i) : H0.restr (le_top : G.U ≤ ⊤) (mulSec hB G.isLB (G.comb (∑ j, g i j • s j)) (Nat.cast_succ l).symm (μ i)) =
      G.mulW l (∑ j, g i j • s j) (H0.restr le_top (μ i)) := by
    rw [G.mulW_apply, mulSec, mulSec, ProdChart.restr_mul, H0.restr_ofSec]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e', map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_comm

end GlobalTheory.HSKerRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegr
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.Lat

theorem mem_of_bil {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (g : A →+ B →+ C)
    {SA : Set A} {SB : Set B} {T : AddSubgroup C} (h : ∀ a ∈ SA, ∀ b ∈ SB, g a b ∈ T) {a : A} {b : B}
    (ha : a ∈ AddSubgroup.closure SA) (hb : b ∈ AddSubgroup.closure SB) : g a b ∈ T := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | zero => simpa using T.zero_mem
    | add b b' _ _ h1 h2 => simpa using T.add_mem h1 h2
    | neg b _ h1 => simpa using T.neg_mem h1
  | zero => simpa using T.zero_mem
  | add a a' _ _ h1 h2 => simpa using T.add_mem h1 h2
  | neg a _ h1 => simpa using T.neg_mem h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intAt (v : Pl (F := F)) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
    evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

theorem at_mul {v : Pl (F := F)} {a : AF F} (b : AF F) (ha : At (evFin F v) a) : At (evFin F v) (a * b) := by
  intro u hu
  have h := ha u hu
  rw [smul_eq_mul] at h ⊢
  rw [← mul_assoc, h, zero_mul]

theorem int_mul {v : Pl (F := F)} {a b : AF F} (ha : evFin F v a ∈ v.adicCompletionIntegers F)
    (hb : evFin F v b ∈ v.adicCompletionIntegers F) : evFin F v (a * b) ∈ v.adicCompletionIntegers F := by
  rw [map_mul]
  exact mul_mem ha hb

def smulHom (n : ℕ) : AE F E →+ (Fin n → AE F E) →+ (Fin n → AE F E) :=
  AddMonoidHom.mk' (fun c => DistribSMul.toAddMonoidHom _ c)
    (fun c c' => AddMonoidHom.ext fun x => by funext i; simp [add_mul])

theorem smul_mem_latAt {v : Pl (F := F)} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {x : Fin n → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) : c • x ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) ?_ hc hx
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ ⟨a, ha, hai, y, hy, rfl⟩
  refine AddSubgroup.subset_closure ⟨b * a, at_mul a hb, int_mul hbi hai, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem smul_incl_mem_latAt {v : Pl (F := F)} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {y : Fin n → E}
    (hy : y ∈ X.L) : (c • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) (SB := {fun i => inclR (F := F) (AF F) (y i)}) ?_ hc (AddSubgroup.subset_closure rfl)
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ rfl
  refine AddSubgroup.subset_closure ⟨b, hb, hbi, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem vecMulVec_mem {v : Pl (F := F)} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) {x : Fin n → AE F E} {y : Fin d → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) (hy : y ∈ GlobalTheory.InertSph.latAt W v) : Matrix.vecMulVec x y ∈ latAtV X W v := by
  let g : (Fin n → AE F E) →+ (Fin d → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Matrix.vecMulVec x y)
        (fun y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add]))
      (fun x x' => AddMonoidHom.ext fun y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
  refine mem_of_bil g ?_ hx hy
  rintro _ ⟨a, ha, hai, x0, hx0, rfl⟩ _ ⟨b, hb, hbi, y0, hy0, rfl⟩
  refine AddSubgroup.subset_closure ⟨a * b, at_mul b ha, int_mul hai hbi, x0, hx0, y0, hy0, ?_⟩
  ext i j
  simp only [g, AddMonoidHom.mk'_apply, Matrix.vecMulVec_apply, incM, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [Algebra.smul_def, map_mul]
  ring

end GlobalTheory.InertLocFrame.Lat

namespace GlobalTheory.InertLocFrame


open GlobalTheory.InertLocFrame.Lat in
theorem mem_latAtV_iff_xm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  intro F E _ _ _ _ _ v n d X W L _ _ ι hinj hsupp hmul hint PV PW hPV hPW z
  have hsing : ∀ {m : ℕ} (j i : Fin m), (Pi.single j (1 : L) : Fin m → L) i ∈ Formalism.UG.intL L := by
    intro m j i
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
      have h1 : ι 1 ∈ Lat.intAt (E := E) v := (hint 1).1 (one_mem _)
      have h1s : At (evFin F v) (ι 1) := (hsupp _).2 ⟨1, rfl⟩
      let X' : Fin n → AE F E := a • fun i => inclR (F := F) (AF F) (x i)
      let Y' : Fin d → AE F E := ι 1 • fun k => inclR (F := F) (AF F) (y k)
      have hX'm : X' ∈ GlobalTheory.InertSph.latAt X v := AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
      have hY'm : Y' ∈ GlobalTheory.InertSph.latAt W v := Lat.smul_incl_mem_latAt W h1 hy
      have hX's : ∀ i, ∃ t, ι t = X' i := fun i => (hsupp _).1 fun u hu => by
        show u • (a • inclR (F := F) (AF F) (x i)) = 0
        rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      have hY's : ∀ k, ∃ t, ι t = Y' k := fun k => (hsupp _).1 fun u hu => by
        show u • (ι 1 * inclR (F := F) (AF F) (y k)) = 0
        rw [← smul_mul_assoc, h1s u hu, zero_mul]
      let xt : Fin n → L := fun i => pre ι (X' i)
      let yt : Fin d → L := fun k => pre ι (Y' k)
      have hxt : ∀ i, ι (xt i) = X' i := fun i => pre_spec ι (hX's i)
      have hyt : ∀ k, ι (yt k) = Y' k := fun k => pre_spec ι (hY's k)
      let c : Fin n → L := ((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ xt
      let c' : Fin d → L := ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) *ᵥ yt
      have hPc : (PV : Matrix (Fin n) (Fin n) L) *ᵥ c = xt := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hPc' : (PW : Matrix (Fin d) (Fin d) L) *ᵥ c' = yt := by
        simp only [c']
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hc : ∀ i, c i ∈ Formalism.UG.intL L := (hPV c).2 (by
        rw [hPc]
        convert hX'm using 1
        funext i
        exact hxt i)
      have hc' : ∀ k, c' k ∈ Formalism.UG.intL L := (hPW c').2 (by
        rw [hPc']
        convert hY'm using 1
        funext k
        exact hyt k)
      refine ⟨Matrix.vecMulVec c' c, fun i j => mul_mem (hc' i) (hc j), ?_⟩
      ext i k
      rw [xm_apply, Matrix.map_apply]
      have e1 : ((PV : Matrix (Fin n) (Fin n) L) * (Matrix.vecMulVec c' c)ᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i k = xt i * yt k := by
        rw [← hPc, ← hPc']
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
          Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      have e2 : ι 1 * X' i = X' i := by rw [← hxt i, ← hmul, one_mul]
      rw [e1, hmul, hxt, hyt]
      show X' i * (ι 1 * inclR (F := F) (AF F) (y k)) = (a • incM F (Matrix.vecMulVec x y)) i k
      rw [← mul_assoc, mul_comm (X' i), e2]
      simp only [X', incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul,
        smul_mul_assoc]
    | zero => exact ⟨0, fun _ _ => zero_mem _, map_zero _⟩
    | add z z' _ _ h h' =>
      obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨u', hu', rfl⟩ := h'
      exact ⟨u + u', fun i j => add_mem (hu i j) (hu' i j), map_add _ _ _⟩
    | neg z _ h =>
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨-u, fun i j => neg_mem (hu i j), map_neg _ _⟩
  · rintro ⟨u, hu, rfl⟩
    have e : xm ι PV PW u = ∑ j, ∑ l, Matrix.vecMulVec (ι (u l j) • fun i => ι ((PV : Matrix _ _ L) i j))
        (fun k => ι ((PW : Matrix _ _ L) k l)) := by
      ext i k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [xm_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_sum, hmul]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine sum_mem fun j _ => sum_mem fun l _ => Lat.vecMulVec_mem X W (Lat.smul_mem_latAt X ((hint _).1 (hu l j)) ?_) ?_
    · have h := (hPV (Pi.single j 1)).1 (hsing j)
      simpa [Matrix.mulVec_single_one] using h
    · have h := (hPW (Pi.single l 1)).1 (hsing l)
      simpa [Matrix.mulVec_single_one] using h

end GlobalTheory.InertLocFrame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegrStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_tensorLatticeAtPlace_iff_frame_coordinates_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  first | exact @GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | exact GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | (intros; apply GlobalTheory.InertLocFrame.mem_latAtV_iff_xm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorConstantTermSum
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.HeckeCT

open Formalism.UG Formalism.UG.P GlobalTheory.LFun

section Tri

variable {R T : Type} [CommRing R] [CommRing T] {r s N : ℕ} (h : r + s = N)

def Tri (g : GL (Fin N) R) (m : GL (Fin r) R × GL (Fin s) R) : Prop :=
  ∃ X, g.val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val X 0 m.2.val

theorem blk_sub (m : GL (Fin r) R × GL (Fin s) R) :
    (blk h m).val.submatrix (blkE h) (blkE h) = Matrix.fromBlocks m.1.val 0 0 m.2.val := by
  change (Matrix.reindex (blkE h) (blkE h) (Matrix.fromBlocks m.1.val 0 0 m.2.val)).submatrix _ _ = _
  simp

theorem tri_blk (m : GL (Fin r) R × GL (Fin s) R) : Tri h (blk h m) m := ⟨0, blk_sub h m⟩

variable {h}

theorem Tri.mul {g g' : GL (Fin N) R} {m m' : GL (Fin r) R × GL (Fin s) R} (a : Tri h g m) (b : Tri h g' m') :
    Tri h (g * g') (m * m') := by
  obtain ⟨X, a⟩ := a
  obtain ⟨Y, b⟩ := b
  refine ⟨m.1.val * Y + X * m'.2.val, ?_⟩
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ (blkE h), a, b, Matrix.fromBlocks_multiply]
  simp

end Tri

theorem blk_mem {L : Type} [Field L] {O : Subring L} {r s N : ℕ} (h : r + s = N) {m : GL (Fin r) L × GL (Fin s) L}
    (h1 : m.1 ∈ GLint (Fin r) O) (h2 : m.2 ∈ GLint (Fin s) O) : blk h m ∈ GLint (Fin N) O := by
  have key : ∀ m : GL (Fin r) L × GL (Fin s) L, m.1 ∈ GLint (Fin r) O → m.2 ∈ GLint (Fin s) O →
      ∀ a b, (blk h m).val a b ∈ O := fun m h1 h2 a b => by
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    have := congrFun (congrFun (blk_sub h m) a) b
    rw [Matrix.submatrix_apply] at this
    rw [this]
    rcases a with a | a <;> rcases b with b | b
    exacts [satake_glint_entry O h1 a b, O.zero_mem, O.zero_mem, satake_glint_entry O h2 a b]
  refine satake_mem_glint O _ (key m h1 h2) ?_
  rw [← map_inv]
  exact key _ (inv_mem h1) (inv_mem h2)

theorem sum_fun {α A B C Q : Type} [Fintype α] [Fintype A] [Fintype B] [Fintype C] [Fintype Q] [DecidableEq α]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] (e : A ⊕ B ⊕ C ≃ α) (G : (A → Q) → (B → Q) → ℂ) :
    ∑ c : α → Q, G (fun a => c (e (.inl a))) (fun b => c (e (.inr (.inl b)))) =
      (Fintype.card Q : ℂ) ^ Fintype.card C * ∑ a, ∑ b, G a b := by
  let f : (A → Q) × (B → Q) × (C → Q) ≃ (α → Q) :=
    (((Equiv.sumArrowEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))).symm).trans (e.arrowCongr (Equiv.refl Q))
  rw [← f.sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [f]

section Pairs

variable {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
  (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)

def pairMap : satakePairs S₁ ⊕ satakePairs S₂ ⊕ (S₁ × (S₂ᶜ : Finset (Fin s))) → satakePairs S
  | .inl p => ⟨(blkE h (.inl p.1.1), blkE h (.inl p.1.2)), (h1 _).2 p.2.1, fun e => p.2.2.1 ((h1 _).1 e), p.2.2.2⟩
  | .inr (.inl p) => ⟨(blkE h (.inr p.1.1), blkE h (.inr p.1.2)), (h2 _).2 p.2.1, fun e => p.2.2.1 ((h2 _).1 e),
      Nat.add_lt_add_left p.2.2.2 r⟩
  | .inr (.inr p) => ⟨(blkE h (.inl p.1.1), blkE h (.inr p.2.1)), (h1 _).2 p.1.2,
      fun e => Finset.mem_compl.1 p.2.2 ((h2 _).1 e), Nat.lt_add_right _ p.1.1.2⟩

theorem pairMap_bijective : Function.Bijective (pairMap h h1 h2) := by
  constructor
  · rintro (p | p | p) (p' | p' | p') e <;> simp [pairMap] at e ⊢
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Subtype.ext (Prod.ext e.1 e.2)
    · exact Prod.ext e.1 e.2
  · rintro ⟨⟨a, b⟩, x, y, z⟩
    obtain ⟨a, rfl⟩ := (blkE h).surjective a
    obtain ⟨b, rfl⟩ := (blkE h).surjective b
    rcases a with a | a <;> rcases b with b | b
    · exact ⟨.inl ⟨(a, b), (h1 _).1 x, fun e => y ((h1 _).2 e), z⟩, rfl⟩
    · exact ⟨.inr (.inr (⟨a, (h1 _).1 x⟩, ⟨b, Finset.mem_compl.2 fun e => y ((h2 _).2 e)⟩)), rfl⟩
    · exact absurd (Nat.lt_add_right a b.2) (not_lt.2 (le_of_lt z))
    · exact ⟨.inr (.inl ⟨(a, b), (h2 _).1 x, fun e => y ((h2 _).2 e), Nat.lt_of_add_lt_add_left z⟩), rfl⟩

theorem tri_satakeGL {L : Type} [Field L] (O : Subring L) {π : L} (hπ : π ≠ 0) (c : satakePairs S → O) :
    Tri h (satakeGL O hπ S c) (satakeGL O hπ S₁ fun p => c (pairMap h h1 h2 (.inl p)),
      satakeGL O hπ S₂ fun p => c (pairMap h h1 h2 (.inr (.inl p)))) := by
  refine ⟨Matrix.of fun a b => (satakeGL O hπ S c).val (blkE h (.inl a)) (blkE h (.inr b)), ?_⟩
  ext (a | a) (b | b)
  · have : blkE h (.inl a) < blkE h (.inl b) ↔ a < b := Iff.rfl
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, satakeGL_apply, satakeN, h1, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq]
    rfl
  · rfl
  · exact satakeGL_lower O hπ S c _ _ (Nat.lt_add_right a b.2)
  · have : blkE h (.inr a) < blkE h (.inr b) ↔ a < b := Nat.add_lt_add_iff_left
    simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, satakeGL_apply, satakeN, h2, this, Matrix.one_apply,
      Equiv.apply_eq_iff_eq, Sum.inr.injEq]
    rfl

end Pairs

section Local

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {ϖ : v.adicCompletion E}
  (hu : IsUnifV E v ϖ)

abbrev Res : Type := satakeRes (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩

abbrev rep {n : ℕ} (S : Finset (Fin n)) (c : satakePairs S → Res hu) : GL (Fin n) (v.adicCompletion E) :=
  satakeGL (Ov E v) (satake_unif_ne_zero v hu) S fun p => satakeSec (Ov E v) ⟨ϖ, mem_Ov_of_isUnifV hu⟩ (c p)

variable [Fintype (Res hu)]

theorem finsum_Tj {n j : ℕ} (hj : j ≤ n) (F : GL (Fin n) (v.adicCompletion E) → ℂ)
    (hF : ∀ g, ∀ k ∈ KGL v (n := n), F (g * k) = F g) :
    ∑ᶠ c : GL (Fin n) (v.adicCompletion E) ⧸ KGL v (n := n), Tj ℂ n (Ov E v) ϖ j c.out * F c.out =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, ∑ c : satakePairs S → Res hu, F (rep hu S c) := by
  classical
  have hϖ := mem_Ov_of_isUnifV hu
  have hr := satake_range_eq v hϖ hu Final.TjCosets hj
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion E)) : GL (Fin n) (v.adicCompletion E) ⧸ KGL v (n := n)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj v hϖ hu h),
      Finset.sum_subtype (Finset.univ.powersetCard j) (p := fun S : Finset (Fin n) => S.card = j)
        (fun S => by simp [Finset.mem_powersetCard]), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => ?_
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (KGL v (n := n)) (satakeB v hϖ hu ⟨S, c⟩)
    rw [hκ, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right v (satakeB_mem v hϖ hu ⟨S, c⟩) κ.2),
      Pi.one_apply, one_mul, hF _ _ κ.2]
    rfl
  · intro x hx
    have hT : Tj ℂ n (Ov E v) ϖ j x.out ≠ 0 := left_ne_zero_of_mul hx
    rw [satake_Tj_ne_zero_iff] at hT
    obtain ⟨i, rfl⟩ := (Set.ext_iff.1 hr x).2 hT
    simp

theorem sum_rep {r s N : ℕ} (h : r + s = N) {S : Finset (Fin N)} {S₁ : Finset (Fin r)} {S₂ : Finset (Fin s)}
    (h1 : ∀ a, blkE h (.inl a) ∈ S ↔ a ∈ S₁) (h2 : ∀ a, blkE h (.inr a) ∈ S ↔ a ∈ S₂)
    (F : GL (Fin N) (v.adicCompletion E) → ℂ) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ c : satakePairs S → Res hu, F (rep hu S c) = (qV E v : ℂ) ^ (S₁.card * (s - S₂.card)) *
      ∑ c₁ : satakePairs S₁ → Res hu, ∑ c₂ : satakePairs S₂ → Res hu, F (blk h (rep hu S₁ c₁, rep hu S₂ c₂)) := by
  have := sum_fun (Equiv.ofBijective _ (pairMap_bijective h h1 h2))
    fun (c₁ : satakePairs S₁ → Res hu) (c₂ : satakePairs S₂ → Res hu) => F (blk h (rep hu S₁ c₁, rep hu S₂ c₂))
  rw [← Nat.card_eq_fintype_card, satake_card_res v _ hu, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin] at this
  rw [← this]
  exact Finset.sum_congr rfl fun c _ => hF _ _ (tri_satakeGL h h1 h2 _ _ _)


omit [Fintype (Res hu)] in
include hu in
theorem finsum_Tj_levi {r s N j : ℕ} (h : r + s = N) (hj : j ≤ N) (F : GL (Fin N) (v.adicCompletion E) → ℂ)
    (hK : ∀ g, ∀ k ∈ KGL v (n := N), F (g * k) = F g) (hF : ∀ g m, Tri h g m → F g = F (blk h m)) :
    ∑ᶠ c : GL (Fin N) (v.adicCompletion E) ⧸ KGL v (n := N), Tj ℂ N (Ov E v) ϖ j c.out * F c.out =
      ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
        (qV E v : ℂ) ^ (i.1 * (s - i.2)) * ∑ᶠ c₁ : GL (Fin r) (v.adicCompletion E) ⧸ KGL v (n := r),
          ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v (n := s),
            Tj ℂ r (Ov E v) ϖ i.1 c₁.out * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (c₁.out, c₂.out)) := by
  classical
  have := satake_res_finite v (mem_Ov_of_isUnifV hu) hu
  let _ : Fintype (Res hu) := Fintype.ofFinite _
  let J : Finset (Fin r) × Finset (Fin s) ≃ Finset (Fin N) :=
    Finset.sumEquiv.symm.toEquiv.trans (blkE h).finsetCongr
  have hJ : ∀ T, J T = (T.1.disjSum T.2).map (blkE h).toEmbedding := fun _ => rfl
  rw [finsum_Tj hu hj F hK,
    ← Finset.sum_equiv J (s := Finset.univ.filter fun T => T.1.card + T.2.card = j)
      (f := fun T => ∑ c : satakePairs (J T) → Res hu, F (rep hu (J T) c))
      (fun T => by simp [hJ, Finset.mem_powersetCard]) (fun _ _ => rfl),
    ← Finset.sum_fiberwise_of_maps_to (g := fun T : Finset (Fin r) × Finset (Fin s) => (T.1.card, T.2.card))
      (t := (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j)) (fun T hT => by
        have a1 := Finset.card_le_univ T.1
        have a2 := Finset.card_le_univ T.2
        simp only [Fintype.card_fin] at a1 a2
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hT ⊢
        omega)]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hi
  have e1 : ∀ g : GL (Fin r) (v.adicCompletion E), ∑ᶠ c₂ : GL (Fin s) (v.adicCompletion E) ⧸ KGL v (n := s),
      Tj ℂ r (Ov E v) ϖ i.1 g * Tj ℂ s (Ov E v) ϖ i.2 c₂.out * F (blk h (g, c₂.out)) =
      Tj ℂ r (Ov E v) ϖ i.1 g * ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c)) := fun g => by
    rw [← finsum_Tj hu hi.1.2 (fun x => F (blk h (g, x))) fun x k hk => ?_, mul_finsum]
    · simp only [mul_assoc]
    · rw [← hK (blk h (g, x)) _ (blk_mem h (m := (1, k)) (one_mem _) hk), ← map_mul]
      simp
  simp only [e1]
  rw [finsum_Tj hu hi.1.1 (fun g => ∑ S ∈ (Finset.univ : Finset (Fin s)).powersetCard i.2,
        ∑ c : satakePairs S → Res hu, F (blk h (g, rep hu S c))) fun x k hk =>
      Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun c _ => by
        rw [← hK (blk h (x, _)) _ (blk_mem h (m := (k, 1)) hk (one_mem _)), ← map_mul]
        simp]
  rw [Finset.sum_congr (s₂ := Finset.univ.powersetCard i.1 ×ˢ Finset.univ.powersetCard i.2) ?_ fun _ _ => rfl,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun S₁ hS₁ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S₂ hS₂ => ?_
    rw [sum_rep hu h (S₁ := S₁) (S₂ := S₂) (fun a => by simp [hJ]) (fun a => by simp [hJ]) F hF,
      (Finset.mem_powersetCard.1 hS₁).2, (Finset.mem_powersetCard.1 hS₂).2]
  · ext T
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ, Prod.ext_iff]
    omega

end Local

section Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

end Global

end GlobalTheory.ResW.HeckeCT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CapKilled

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def ktype (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Sm E a) where
  carrier := {ψ | ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W}
  zero_mem' g := by
    have e : (fun k : Kinf E a => (cptRep E a k 0).1 g) = 0 := by funext k; simp
    rw [e]; exact W.zero_mem
  add_mem' {ψ ψ'} h h' g := by
    have e : (fun k : Kinf E a => (cptRep E a k (ψ + ψ')).1 g) =
        (fun k : Kinf E a => (cptRep E a k ψ).1 g) + fun k : Kinf E a => (cptRep E a k ψ').1 g := by
      funext k; simp
    rw [e]
    exact W.add_mem (h g) (h' g)
  smul_mem' c ψ h g := by
    have e : (fun k : Kinf E a => (cptRep E a k (c • ψ)).1 g) = c • fun k : Kinf E a => (cptRep E a k ψ).1 g := by
      funext k; simp
    rw [e]
    exact W.smul_mem c (h g)


variable (E a) in
def killed (q : (E →+* ℂ) → ℂ → Polynomial ℂ) : Submodule ℂ (Sm E a) :=
  ⨅ τ, ⨅ u, LinearMap.ker (Polynomial.aeval (cap τ u) (q τ u))


variable (E a) in
def space (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ))
    (q : (E →+* ℂ) → ℂ → Polynomial ℂ) : Submodule ℂ (Sm E a) :=
  leftInv E a ⊓ fixL E a L ⊓ ktype E a W ⊓ killed E a q ⊓ tame E a

theorem mem_killed {q : (E →+* ℂ) → ℂ → Polynomial ℂ} {ψ : Sm E a} :
    ψ ∈ killed E a q ↔ ∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0 := by
  simp [killed, Submodule.mem_iInf]

theorem mem_space {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {q : (E →+* ℂ) → ℂ → Polynomial ℂ} {ψ : Sm E a} :
    ψ ∈ space E a L W q ↔ (∀ γ g, ψ.1 (ratGL E a γ * g) = ψ.1 g) ∧ (∀ k ∈ L, finRep E a k ψ = ψ) ∧
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ).1 g) ∈ W) ∧
      (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) ∧ ψ ∈ tame E a := by
  rw [space, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, mem_killed]
  exact ⟨fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩

end GlobalTheory.CapKilled

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymPrOpenBounded
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.SymImageC

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def refLev (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p + 1) (fun i => 2 * (i.val + 1))

def refGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | GlobalTheory.RootEx.Radical.Uni (refLev p) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => GlobalTheory.RootEx.Radical.Uni.mul ha hb
  inv_mem' := fun ha => GlobalTheory.RootEx.Radical.Uni.inv ha

theorem N_le_refGroup {p q : ℕ} (h₁ : p ≤ q) (h₂ : q ≤ p + 1) :
    GlobalTheory.RootEx.N k n c q ≤ refGroup k n c p := by
  intro g hg r s hrs
  refine (GlobalTheory.RootEx.Radical.mem_N_iff g).1 hg r s ?_
  rcases r with r | r <;> rcases s with s | s <;>
    simp only [refLev, Sum.elim_inl, Sum.elim_inr] at hrs <;>
    simp only [GlobalTheory.RootEx.lev, Sum.elim_inl, Sum.elim_inr] <;> omega

theorem symN_le_refGroup : symN k n c ≤ refGroup k n c ((c + 1) / 2) :=
  sup_le (N_le_refGroup le_rfl (by omega)) (N_le_refGroup (by omega) (by omega))

theorem toBlocks₁₁_of_mem_symN {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) : u.val.toBlocks₁₁ = 1 := by
  have h : GlobalTheory.RootEx.Radical.Uni (refLev ((c + 1) / 2)) u.val := symN_le_refGroup hu
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [h _ _ (by simp [refLev])]
  simp [Matrix.one_apply]

theorem toBlocks₁₁_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    (u * GlobalTheory.RootEx.embX c g).val.toBlocks₁₁ = g.val := by
  have h := toBlocks₁₁_of_mem_symN hu
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

theorem toBlocks₁₁_inv_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    ((u * GlobalTheory.RootEx.embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
  have h := toBlocks₁₁_of_mem_symN (inv_mem hu)
  rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (u⁻¹).val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

end GlobalTheory.FunObj.SymImageC


open GlobalTheory.FunObj.SymImageC in
theorem GlobalTheory.FunObj.SymImageC.symPr_open_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (C : Subgroup (GL (n ⊕ Fin c) k)) (hC : IsOpen (C : Set (GL (n ⊕ Fin c) k)))
    (hb : ∃ A : Set (GL (n ⊕ Fin c) k), IsCompact A ∧ (C : Set (GL (n ⊕ Fin c) k)) ⊆ A) :
    IsOpen (symPr C : Set (GL n k)) ∧ ∃ A : Set (GL n k), IsCompact A ∧ (symPr C : Set (GL n k)) ⊆ A := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  constructor
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have ho := hC.preimage (GlobalTheory.RootEx.QuotLinear.continuous_embX (k := k) (n := n) (c := c))
    refine Filter.mem_of_superset (ho.mem_nhds (by simp [one_mem])) fun g hg => ?_
    exact ⟨1, one_mem _, by simpa using hg⟩
  · obtain ⟨A, hA, hCA⟩ := hb
    let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
      fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
    have hbl : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    have hφ : Continuous φ :=
      (hbl.comp Units.continuous_val).prodMk
        (MulOpposite.continuous_op.comp (hbl.comp Units.continuous_coe_inv))
    refine ⟨_, (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hA.image hφ),
      ?_⟩
    rintro g ⟨u, hu, h⟩
    refine ⟨_, hCA h, ?_⟩
    simp only [φ]
    rw [toBlocks₁₁_mul_embX hu, toBlocks₁₁_inv_mul_embX hu]
    rfl
end
end
