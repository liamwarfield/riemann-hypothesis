module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDualTamePart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.Crd

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Ortho (S : Formalism.BasicNotions.HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem ortho_pos (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) : Ortho (Examples₂.posSpace hstar N) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) N 0 a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

abbrev co (S : Formalism.BasicNotions.HSpace E) {n : ℕ} (h : S.rank = n) : S.V ≃ₗ[E] (Fin n → E) :=
  S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem Ortho.isStd {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) : Formalism.L2.Herm.IsStd S := ⟨S.frame, h.1, h.2⟩

theorem Ortho.gram {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) :
    S.gram.reindex (finCongr hn) (finCongr hn) = 1 := by
  subst hn
  ext a b
  simpa [HSpace.gram, Matrix.one_apply] using h.1 a b

theorem Ortho.mem_standardLattice_iff_integral_coords {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) (x : Fin n → E) :
    x ∈ S.L0.map (((co S hn : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
      ∀ j, x j ∈ (algebraMap (𝓞 E) E).range := by
  subst hn
  rw [h.2]
  constructor
  · rintro ⟨v, hv, rfl⟩ j
    have := (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame v).1 hv j
    simpa [co] using this
  · intro hx
    refine ⟨(co S rfl).symm x, (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame _).2 fun j => ?_, (co S rfl).apply_symm_apply x⟩
    have h2 : S.frame.repr ((co S rfl).symm x) j = x j :=
      congrFun ((co S rfl).apply_symm_apply x) j
    rw [h2]
    exact hx j

theorem map_symm_map {S : Formalism.BasicNotions.HSpace E} {n : ℕ} (e : S.V ≃ₗ[E] (Fin n → E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    (L.map ((e.symm : (Fin n → E) →ₗ[E] S.V).restrictScalars (𝓞 E))).map
      ((e : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = L := by
  ext x
  simp

theorem incl_co {S S' : Formalism.BasicNotions.HSpace E} {n : ℕ} (hn : S.rank = n) (hn' : S'.rank = n - 1) (f : S'.V →ₗ[E] S.V)
    (hf : ∀ (a : Fin S'.rank) (b : Fin S.rank), (a : ℕ) = b → f (S'.frame a) = S.frame b) (x : Fin (n - 1) → E) (j : Fin n) :
    co S hn (f ((co S' hn').symm x)) j = if h : j.1 < n - 1 then x ⟨j.1, h⟩ else 0 := by
  subst hn
  have hs : (co S' hn').symm x = ∑ a : Fin (S.rank - 1), x a • S'.frame (finCongr hn'.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
    · simp [co]
    · intro a _ ha
      have : ¬ (a : ℕ) = k := fun h => ha (Fin.ext h)
      simp [co, Finsupp.single_apply, Fin.ext_iff, this]
    · simp
  have hb : ∀ a : Fin (S.rank - 1), f (S'.frame (finCongr hn'.symm a)) = S.frame ⟨a.1, by omega⟩ := fun a => hf _ _ rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum, map_sum]
  simp only [map_smul, hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hc : ∀ a : Fin (S.rank - 1), co S rfl (S.frame ⟨a.1, by omega⟩) j = if a.1 = j.1 then 1 else 0 := by
    intro a
    simp [co, Fin.ext_iff]
  simp only [hc]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j.1, h⟩]
    · simp
    · intro a _ ha
      rw [if_neg (fun h2 => ha (Fin.ext h2)), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (fun h2 : a.1 = j.1 => h (h2 ▸ a.2)), mul_zero]

end Gen

end GlobalTheory.Mem.Col2.Crd

end


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.TC.spaces_in_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (I.rec7 l Z) ∧ gramP (I.rec7 l Z) = 1 ∧ (∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (I.rec7 l Z) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (I.rec7 l Z) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  intro B X I hI hP l Z
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact Crd.ortho_pos hs _
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  refine ⟨⟨fun i _ => (oX i).isStd, oX'.isStd⟩, oX'.gram (rankP (I.rec7 l Z)), fun x j => ?_, fun i hi =>
    ⟨(oX i).gram (rankN (I.rec7 l Z) i hi), fun x => (oX i).mem_standardLattice_iff_integral_coords (rankN (I.rec7 l Z) i hi) x, fun u a => ⟨fun c => ?_, ?_⟩⟩⟩
  · exact Crd.incl_co (S := B.sp.X B.R.m) (S' := B.sp.X') (rankN (I.rec7 l Z) _ le_rfl) (rankP (I.rec7 l Z)) B.sp.iX' hP.iX x j
  · unfold TC.latAt
    rw [dite_eq_left hi]
    exact Crd.map_symm_map (S := B.sp.X i) (TC.crd B i hi) _
  · exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (I.rec7 l Z) ∧ gramP (I.rec7 l Z) = 1 ∧ (∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (I.rec7 l Z) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (I.rec7 l Z) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  first | exact @GlobalTheory.Mem.Col2.TC.spaces_in_coordinates | exact GlobalTheory.Mem.Col2.TC.spaces_in_coordinates | (intros; apply GlobalTheory.Mem.Col2.TC.spaces_in_coordinates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspBoundSiegel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem posIdele_mul (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) :
    posIdele (K := E) (ρ * σ) (mul_pos hρ hσ) = posIdele ρ hρ * posIdele σ hσ := by
  unfold posIdele
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← map_mul]
  congr 1
  exact Subtype.ext (mul_pow ρ σ _)

theorem posIdele_exp (u : ℝ) :
    posIdele (K := E) (Real.exp u) (Real.exp_pos u) = infId E (expU fun _ : InfinitePlace E => (u : ℂ)) := by
  refine Units.ext (ad_ext ?_ ?_)
  · have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    simp only [map_add (f := _), map_sub, map_one, h, sub_self, zero_add]
    funext w
    have hc := IsTotallyComplex.isComplex w
    have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).1 w) = _
    rw [← coe_infiniteProj, infiniteProj_posIdele]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (posRealElem w _) = _
    unfold posRealElem
    rw [dite_eq_right hw, RingEquiv.apply_symm_apply]
    simp [InfinitePlace.mult, hw, Real.sqrt_sq (Real.exp_pos u).le, expU, Complex.ofReal_exp]
  · change ((posIdele _ _ : IdeleGroup E) : AdeleRing (𝓞 E) E).2 = (1 : Af E) - 0 + 0
    rw [sub_zero, add_zero]
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by rw [posIdele_finite]; rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem posIdele_congr {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x = y) :
    posIdele (K := E) x hx = posIdele y hy := by subst h; rfl

theorem diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    diagUnits a (fun _ : Fin a => posIdele (K := E) x hx) = splitCentre E a (Real.log x) := by
  rw [splitCentre_eq_scalar, ← posIdele_exp, posIdele_congr hx (Real.exp_pos _) (Real.exp_log hx).symm]
  refine Units.ext ?_
  rw [coe_diagUnits]
  rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_posIdele_pos :
    Continuous fun r : {r : ℝ // 0 < r} => (posIdele (K := E) r.1 r.2 : IdeleGroup E) := by
  unfold posIdele
  exact continuous_finsetProd _ fun w _ => (continuous_moduleSection w).comp
    (Continuous.subtype_mk ((continuous_subtype_val).pow _) _)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem ideleModule_det_diagUnits_posIdele (a : ℕ) {x : ℝ} (hx : 0 < x) :
    (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
      (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx))) : ℝ) = x ^ (a * Module.finrank ℚ E) := by
  have hdet : Matrix.GeneralLinearGroup.det (diagUnits a (fun _ : Fin a => posIdele (K := E) x hx)) =
      posIdele x hx ^ a := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
  rw [hdet, map_pow, Positive.val_pow, ideleModule_posIdele, ← pow_mul, mul_comm]

theorem cuspFormsBounded_of_rapidDecay (h : GlobalTheory.Published.CuspRapidDecaySiegelGL) : GlobalTheory.Published.CuspFormsBoundedGL := by
  intro E _ _ _ a φ hφ hA
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨‖φ.1 1‖, fun g => ?_⟩
    have : g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [this]
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) a
  set d : ℕ := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have had : a * d ≠ 0 := (Nat.mul_pos ha hd0).ne'
  set m : AdelicGLn.AdelicGL E a → ℝ :=
    fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm
  have hmpos : ∀ b, 0 < m b := fun b => (IdeleGroup.ideleModule E _).2
  set s : AdelicGLn.AdelicGL E a → ℝ := fun b => m b ^ (((a * d : ℕ) : ℝ)⁻¹) with hs
  have hspos : ∀ b, 0 < s b := fun b => Real.rpow_pos_of_pos (hmpos b) _
  have hspow : ∀ b, s b ^ (a * d) = m b := fun b => Real.rpow_inv_natCast_pow (hmpos b).le had
  set f : AdelicGLn.AdelicGL E a → AdelicGLn.AdelicGL E a :=
    fun b => b * (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf
  have hmc : Continuous m :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  have hsc : Continuous fun b => (⟨s b, hspos b⟩ : {r : ℝ // 0 < r}) :=
    Continuous.subtype_mk (hmc.rpow_const fun b => Or.inl (hmpos b).ne') _
  have hfc : Continuous f := continuous_id.mul ((continuous_diagUnits a).comp
    (continuous_pi fun _ => continuous_posIdele_pos.comp hsc)).inv
  have hω'c : IsCompact (f '' ω) := hω.image hfc
  have hω'B : f '' ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (hωB hb) (inv_mem (diagUnits_mem_adelicBorel a _))
  have hω'1 : ∀ b ∈ f '' ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1 := by
    rintro _ ⟨b, -, rfl⟩
    have e : IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
        (diagUnits a (fun _ : Fin a => posIdele (K := E) (s b) (hspos b)))) =
        IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) :=
      Subtype.ext (by rw [ideleModule_det_diagUnits_posIdele, hspow])
    simp only [hf, map_mul, map_inv, e, mul_inv_cancel]
    rfl
  obtain ⟨C, hC⟩ := h E a φ hφ (f '' ω) hω'c hω'B hω'1 t ht 0
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg g
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  set ρ := (∏ i, r i) ^ ((a : ℝ)⁻¹) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hprod _
  have hρa : ρ ^ a = ∏ i, r i := Real.rpow_inv_natCast_pow hprod.le ha.ne'
  set r' : Fin a → ℝ := fun i => r i / ρ with hr'
  have hr'pos : ∀ i, 0 < r' i := fun i => div_pos (hr i) hρpos
  have hD : diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) =
      diagUnits a (fun _ : Fin a => posIdele (K := E) ρ hρpos) *
        diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by
    rw [← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← posIdele_mul]
    exact posIdele_congr _ _ (by simp only [hr']; field_simp)
  set D' := diagUnits a (fun i => posIdele (K := E) (r' i) (hr'pos i)) with hD'
  have key : ratGL E a γ * g = splitCentre E a (Real.log (s b) + Real.log ρ) * (f b * D' * k) := by
    change AdelicGLn.diagonal E a γ * g = _
    rw [e, hD, diagUnits_posIdele a hρpos, splitCentre_add]
    simp only [hf, diagUnits_posIdele a (hspos b)]
    symm
    calc splitCentre E a (Real.log (s b)) * splitCentre E a (Real.log ρ) *
          (b * (splitCentre E a (Real.log (s b)))⁻¹ * D' * k)
        = splitCentre E a (Real.log (s b)) * (splitCentre E a (Real.log ρ) *
            (b * (splitCentre E a (Real.log (s b)))⁻¹)) * D' * k := by group
      _ = splitCentre E a (Real.log (s b)) * ((b * (splitCentre E a (Real.log (s b)))⁻¹) *
            splitCentre E a (Real.log ρ)) * D' * k := by rw [splitCentre_comm (Real.log ρ)]
      _ = (splitCentre E a (Real.log (s b)) * b) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by group
      _ = (b * splitCentre E a (Real.log (s b))) * (splitCentre E a (Real.log (s b)))⁻¹ *
            splitCentre E a (Real.log ρ) * D' * k := by rw [splitCentre_comm (Real.log (s b)) b]
      _ = b * (splitCentre E a (Real.log ρ) * D') * k := by group
  calc ‖φ.1 g‖ = ‖φ.1 (ratGL E a γ * g)‖ := by rw [hφ.1.left]
    _ = ‖φ.1 (f b * D' * k)‖ := by rw [key, hA]
    _ ≤ C * ∏ i, r' i ^ (0 : Fin a → ℝ) i := hC (f b) ⟨b, hb, rfl⟩ r' hr'pos (fun i j hij => by
          simp only [hr']
          rw [← mul_div_assoc]
          exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le) (by
          simp only [hr']
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa,
            div_self hprod.ne']) k hk
    _ = C := by simp

end GlobalTheory.CuspBoundSiegel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypeParts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypeParts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LabProof


set_option maxHeartbeats 2000000 in
theorem hasLab_exists : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ p, HasLab Y σ p := by
  intro hW hDS hHC hCD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hPins hHolds hHost σ
  obtain ⟨c, hE, hWp⟩ := GlobalTheory.T.exists_sphericalEigensystem_of_finiteType_with_parts hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost σ
  have hcar := GlobalTheory.T.eigensystem_carried_by_finiteType_of_meets_level_rows hW hDS hHC hCD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds hHost
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := hE b U hU
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxU
    exact hU0 hxU.symm
  obtain ⟨p, hp⟩ := hcar c b x hx0 hx (by rw [hxU]; exact hU.1)
  have hinjW : ∀ i, Function.Injective (R.HW i (sg0 D A3.A)).e := fun i => (hPins.char.base.models.HW i _).1
  refine ⟨p, fun i => ?_, fun k hk => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := (Y.tied.lift.isot i σ y).1 hy
    rw [Y.prtWE] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hWp i U' hU'
    rw [Y.mjRead] at hU'e
    have h2 : (R.HW i (sg0 D A3.A)).e (Y.mj.eW i y) = (R.HW i (sg0 D A3.A)).e w := by
      rw [hwU]
      exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).injective hU'e.symm
    have h3 : Y.mj.eW i y ∈ R.Wc' i c := (hinjW i h2) ▸ hw
    exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.Wc' i c) c hp le_rfl h3
  · have h1 := Y.tied.base.ft k
    rw [hk, Y.prtE0] at h1
    obtain ⟨U', hU', hU'e⟩ := h1
    obtain ⟨w, hw, hwU⟩ := hE false U' hU'
    refine ⟨w, le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl hw, ?_⟩
    rw [← hU'e, hwU]
    rfl

end GlobalTheory.Mem.R3.LabProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFamilyLabelContainingFiniteTypePartsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ σ : D.what₂.FT, ∃ p, HasLab Y σ p := by
  first | exact @GlobalTheory.Mem.R3.LabProof.hasLab_exists | exact GlobalTheory.Mem.R3.LabProof.hasLab_exists | (intros; apply GlobalTheory.Mem.R3.LabProof.hasLab_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.ClsZero

section Canon
variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def canon (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) :=
  Classical.epsilon (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp),
    d' = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d) (h := ⟨d⟩)

theorem canon_spec (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : ∃ (γ : UF X.E n) (k : Λ.grp),
    canon Λ d = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d :=
  Classical.epsilon_spec (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp), d' = ((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d)
    ⟨d, 1, 1, (one_smul _ d).symm⟩

theorem canon_smul (γ : UF X.E n) (k : Λ.grp) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    canon Λ (((γ, (k.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • d) = canon Λ d := by
  unfold canon
  congr 1
  funext d'
  apply propext
  constructor
  · rintro ⟨γ', k', rfl⟩
    exact ⟨γ' * γ, k' * k, by rw [← mul_smul]; rfl⟩
  · rintro ⟨γ', k', rfl⟩
    refine ⟨γ' * γ⁻¹, k' * k⁻¹, ?_⟩
    rw [← mul_smul]
    congr 1
    ext1 <;> simp

theorem canon_idem (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : canon Λ (canon Λ d) = canon Λ d := by
  obtain ⟨γ, k, h⟩ := canon_spec Λ d
  conv_lhs => rw [h]
  exact canon_smul Λ γ k d

theorem orb_iff (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (hΘ : Θ = LevQFam.top X.E X.K n Q)
    (hy : y = Ys.triv X n) (p p' : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ; ∃ g : FrmG Λ' Θ, g • p = p') ↔ canon Λ p'.1.1.deco = canon Λ p.1.1.deco := by
  subst hΛ hΘ hy
  constructor
  · rintro ⟨g, rfl⟩
    exact canon_smul Λ' g.1 g.2.1 p.1.1.deco
  · intro h
    obtain ⟨γ₁, k₁, h₁⟩ := canon_spec Λ' p.1.1.deco
    obtain ⟨γ₂, k₂, h₂⟩ := canon_spec Λ' p'.1.1.deco
    have e : p'.1.1.deco = (((γ₂⁻¹ * γ₁ : UF X.E n), ((k₂⁻¹ * k₁ : Λ'.grp).1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • p.1.1.deco := by
      have := h₂.symm.trans (h.trans h₁)
      rw [← eq_inv_smul_iff, ← mul_smul] at this
      exact this
    generalize γ₂⁻¹ * γ₁ = γ at e
    generalize k₂⁻¹ * k₁ = k at e
    let q : DecoF X.E n ST SG Q := ((γ, k.1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p.1.1
    have hq : q.deco = p'.1.1.deco := e.symm
    have hc : ∀ P : Q, (p'.1.1.fr P)⁻¹ * q.fr P ∈ GLint X.E n P.1 := by
      intro P x
      have h1 := q.2 P x
      have h2 := p'.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x))
      have h3 : p'.1.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [h3] at h2
      have h4 : q.1.1 = p'.1.1.1.1 := hq
      rw [h4] at h1
      exact h2.symm.trans h1
    refine ⟨(γ, k, ⟨fun P => ⟨_, hc P⟩, fun _ _ => trivial⟩), ?_⟩
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext e.symm ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p'.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ X.E n Q) P)⁻¹.1))⁻¹ = p'.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · have h1 : p.1.2 = ∅ := p.2
      have h2 : p'.1.2 = ∅ := p'.2
      show (fun v => γ.1 v) '' p.1.2 = p'.1.2
      rw [h1, h2, Set.image_empty]

theorem eps_eq (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (p : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ
     Classical.epsilon (p := fun r => ∃ g : FrmG Λ' Θ, r = (g • p).1.1.deco) (h := ⟨p.1.1.deco⟩)) = canon Λ p.1.1.deco := by
  subst hΛ
  unfold canon
  congr 1
  funext r
  apply propext
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2.1, rfl⟩
  · rintro ⟨γ, k, rfl⟩
    exact ⟨(γ, k, 1), rfl⟩

end Canon

attribute [local instance] starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem levelTypePrimes_stepZero_eq_colLev (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = colLev I.Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_G b

theorem chartIndexLevelTwistPrimes_stepZero_eq_top (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = LevQFam.top _ _ _ _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_Q b

theorem ys0 (a : I.ι) : ysAt B.R I.sel (I.tup a) (I.cst a) 0 = Ys.triv _ _ :=
  if_neg (by have := B.R.two_le_m; omega)

theorem stepZero_chartIndex_subsingleton (h : I.Ok) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) : b = b' := by
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  obtain ⟨b0, hb0⟩ := (h.idx_ok a).zero_uniq
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 hm) (by simp)
  obtain ⟨_ | b', hb'⟩ := b'
  · exact absurd (hb'.2 hm) (by simp)
  obtain rfl : b = b' := (hb0 b).trans (hb0 b').symm
  rfl

theorem stepZero_chartIndex_nonempty (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b0, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b0, by have := B.R.two_le_m; simp; omega⟩⟩

theorem cl_eq_iff (h : I.Ok) (u : B.Word) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) (p p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    (I.stp u a 0).cl b p = (I.stp u a 0).cl b' p' ↔ canon (colLev I.Ch 0) p.1.1.deco = canon (colLev I.Ch 0) p'.1.1.deco := by
  obtain rfl := stepZero_chartIndex_subsingleton h a b b'
  rw [← orb_iff (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b) _ (chartIndexLevelTwistPrimes_stepZero_eq_top h a b) (ys0 a) p' p]
  constructor
  · intro e
    exact Quotient.exact (eq_of_heq (Sigma.mk.inj e).2)
  · intro e
    exact congrArg (Sigma.mk b) (Quotient.sound e)

theorem cl_rep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (c : S.Cl) : S.cl c.1 (S.rep c) = c :=
  congrArg (Sigma.mk c.1) (S.rp_spec c.1 c.2)

theorem bij0 (h : I.Ok) (u : B.Word) (a : I.ι) (b) : Function.Bijective (I.cl0 u a b) := by
  constructor
  · intro c c' e
    have e1 := (cl_eq_iff h u a b b _ _).1 e
    rw [← cl_rep _ c, ← cl_rep _ c']
    exact (cl_eq_iff h u I.mu0 _ _ _ _).2 e1
  · intro c
    obtain ⟨b0⟩ := stepZero_chartIndex_nonempty h I.mu0
    refine ⟨(I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c)), ?_⟩
    have e := (cl_eq_iff h u I.mu0 _ _ _ _).1 (cl_rep _ ((I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c))))
    refine Eq.trans ?_ (cl_rep _ c)
    exact (cl_eq_iff h u a _ _ _ _).2 e

theorem stepZero_preferred_iff_canonicalRep (h : I.Ok) (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0)
    (p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    I.pref u a 0 b p ↔ p.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := by
  have hm := B.R.two_le_m
  have e := eps_eq (ST := (B.primes X).vT u) (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b)
    (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b) p
  constructor
  · intro hp
    exact Eq.trans (hp.1 rfl) e
  · intro hp
    exact ⟨fun _ => hp.trans e.symm, fun e' => absurd e' (by omega),
      topLev_pref_ne I.Ch I.sel (I.tup a) (I.cst a) I.Ps u (by omega) _⟩

theorem empty_mem_couplingIndexAtStep_zero (a : I.ι) (N) : ∅ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) 0).ys N := by
  rw [ys0]; rfl

theorem stepZero_representative_deco_eq_canonical (h : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    ((I.stp u a 0).rep c).1.1.deco = canon (colLev I.Ch 0) ((I.stp u a 0).rep c).1.1.deco := by
  obtain ⟨b, q⟩ := c
  let p := (I.stp u a 0).rep ⟨b, q⟩
  obtain ⟨γ, k, e⟩ := canon_spec (colLev I.Ch 0) p.1.1.deco
  let p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 := ⟨(((γ, k.1, 1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N 0) (I.Q a)) • p.1.1, ∅), empty_mem_couplingIndexAtStep_zero a _⟩
  have e' : p'.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := e.symm
  have hc : (I.stp u a 0).cl b p' = ⟨b, q⟩ := by
    refine Eq.trans ?_ (cl_rep _ ⟨b, q⟩)
    refine (cl_eq_iff h u a b b _ _).2 ?_
    rw [e', canon_idem]
  have hp := @pref_prefRep _ _ _ ((I.stp0 u a 0).actD b) (I.pref u a 0 b) p'
    ((stepZero_preferred_iff_canonicalRep h u a b p').2 (by rw [e', canon_idem]))
  have hq : q = Quotient.mk _ p' := (eq_of_heq (Sigma.mk.inj hc).2).symm
  refine (stepZero_preferred_iff_canonicalRep h u a b _).1 ?_
  rw [hq]
  exact hp

theorem stepZero_corresponding_representatives_same_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b) (c : (I.stp u I.mu0 0).Cl) :
    ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  refine (stepZero_representative_deco_eq_canonical h u a _).trans (Eq.trans ?_ (stepZero_representative_deco_eq_canonical h u I.mu0 c).symm)
  exact (cl_eq_iff h u a (I.cl0 u a b c).1 b ((I.stp u a 0).rep (I.cl0 u a b c))
    (I.pt0 u I.mu0 a ((I.stp u I.mu0 0).rep c))).1 (cl_rep (I.stp u a 0) (I.cl0 u a b c))

theorem stepZero_classes_bijective_same_deco : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b,
    Function.Bijective (I.cl0 u a b) ∧
      ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco :=
  fun _ h u a b => ⟨bij0 h u a b, stepZero_corresponding_representatives_same_deco h u a b⟩

end GlobalTheory.Mem.Col2.ClsZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDecoStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cl0_bijective_and_deco_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b, Function.Bijective (I.cl0 u a b) ∧ ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  first | exact @GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco | exact GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco | (intros; apply GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolLowOnce

open GlobalTheory.HolDict.HolTo GlobalTheory.HolDict.CoefExt

section General

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Hm : Mt n} {σ : Mt n → (H →L[ℂ] H)} {v : H}

theorem smFn_coef (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) :
    SmFn (fun _ : Unit => Hm) fun u => ⟪l, σ (u ()) v⟫_ℂ := by
  intro k τs Xs hX u hu
  have hmem : ∀ t : Fin k → ℝ, (List.ofFn fun i =>
      (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : Unit → Mt n)).prod ∈ UG (fun _ : Unit => Hm) := fun t =>
    prod_mem_UG _ fun v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact single_mem_UG (fun _ : Unit => Hm) _ (hX i) _
  simp only [Pi.mul_apply, hσ.2 _ (hu ()) _ (hmem _ ()), ContinuousLinearMap.comp_apply]
  simp only [prod_single_apply, if_true]
  have h1 := hv k Xs hX
  exact (((innerSL ℂ l).comp (σ (u ()))).restrictScalars ℝ).contDiff.comp h1

theorem der_coef (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) {X : Mt n}
    (hX : X ∈ lieH Hm) {u : Unit → Mt n} (hu : u ∈ UG (fun _ : Unit => Hm)) :
    der () X (fun u => ⟪l, σ (u ()) v⟫_ℂ) u = ⟪l, σ (u ()) (dRep σ X v)⟫_ℂ := by
  unfold der
  have e : (fun t : ℝ => ⟪l, σ ((u * (Pi.mulSingle () (NormedSpace.exp (t • X)) : Unit → Mt n)) ()) v⟫_ℂ) =
      fun t : ℝ => ⟪l, σ (u ()) (σ (NormedSpace.exp (t • X)) v)⟫_ℂ := by
    funext t
    rw [Pi.mul_apply, hσ.2 _ (hu ()) _ (single_mem_UG (fun _ : Unit => Hm) () hX t ()), Pi.mulSingle_eq_same]
    rfl
  rw [e]
  exact ((((innerSL ℂ l).comp (σ (u ()))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_of_smooth hv hX)).deriv

theorem derC_coef {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀)
    (hσ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (l : H) (Z : Mt n) {u : Unit → Mt n}
    (hu : u ∈ UG (fun _ : Unit => Hm)) :
    derC (fun _ : Unit => Hm) () Z (fun u => ⟪l, σ (u ()) v⟫_ℂ) u = ⟪l, σ (u ()) (dRepC Hm σ Z v)⟫_ℂ := by
  obtain ⟨h1, h2⟩ := conj_facts (herm_of_orth h) (dets_ne h).1 Z
  have hA : (1 / 2 : ℂ) • (Z + conjH Hm Z) ∈ lieH Hm := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    abel_nf
    simp
  have hB : (1 / (2 * Complex.I) : ℂ) • (Z - conjH Hm Z) ∈ lieH Hm := by
    show _ = _
    rw [conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
    rw [this, neg_smul, ← smul_neg, ← smul_add]
    abel_nf
    simp
  unfold derC dRepC
  rw [der_coef hσ hv l hA hu, der_coef hσ hv l hB hu, map_add (f := _), map_smul, inner_add_right, inner_smul_right]

theorem inner_iso (T : H →L[ℂ] H) (hT : ∀ x, ‖T x‖ = ‖x‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem eq_zero_of_orth [CompleteSpace H] {q : ℕ} {x₀ : Mt n} {w : Fin n → ℤ} (h : OrthFr Hm q x₀)
    (hσ : IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ) (hirr : IsIrredOn (Formalism.QuantumDeterminants.UH Hm) σ) (hv : SmoothVec (lieH Hm) σ v) (hv0 : v ≠ 0)
    (hk : ∀ a c : Fin n, a ≤ c → dRepC Hm σ (x₀ * Matrix.single a c 1 * x₀⁻¹) v = if a = c then (w a : ℂ) • v else 0)
    (l : H) (hmem : ∀ s, torEl (fun _ : Unit => x₀) s () ∈ Formalism.QuantumDeterminants.UH Hm)
    (hl : ∀ s, σ (torEl (fun _ : Unit => x₀) s ()) l = torCh (fun _ : Unit => w) s • l) (h0 : ⟪l, v⟫_ℂ = 0) : l = 0 := by
  have hf : HolFn (fun _ : Unit => Hm) (fun _ => q) (fun _ => x₀) (fun _ => w) fun u => ⟪l, σ (u ()) v⟫_ℂ := by
    refine GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun _ => h) _ (smFn_coef hσ.1 hv l) ?_
    rintro ⟨⟩ a c hac u hu
    rw [derC_coef h hσ.1 hv l _ hu, hk a c hac]
    split_ifs
    · rw [map_smul, inner_smul_right]
    · simp
  have hz := GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law _ _ _ _ _ _ (fun _ => h) _ hf (fun u hu s => by
    have hn : (starRingEnd ℂ) (torCh (fun _ : Unit => w) s) * torCh (fun _ : Unit => w) s = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [torCh, norm_prod, norm_zpow, Complex.norm_exp_ofReal_mul_I]
    have e := inner_iso _ (hσ.2.1 _ (hmem s)) l (σ (u ()) v)
    rw [hl, inner_smul_left] at e
    simp only [Pi.mul_apply]
    rw [hσ.1.2 _ (hmem s) _ (hu ()), ← e, ← mul_assoc, mul_comm (torCh _ s), hn, one_mul]
    rfl) (by
      simp only [Pi.one_apply]
      rw [hσ.1.1]
      exact h0)
  let P : Submodule ℂ H := ⨅ g ∈ Formalism.QuantumDeterminants.UH Hm, LinearMap.ker ((innerSL ℂ l).comp (σ g)).toLinearMap
  have hP : ∀ y, y ∈ P ↔ ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ⟪l, σ g y⟫_ℂ = 0 := fun y => by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hcl : IsClosed (P : Set H) := by
    have : (P : Set H) = ⋂ g ∈ Formalism.QuantumDeterminants.UH Hm, {y | ⟪l, σ g y⟫_ℂ = 0} := by
      ext y
      simp only [SetLike.mem_coe, hP, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (by fun_prop) continuous_const
  have hone : (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
    show _ = _
    simp
  rcases hirr P hcl (fun g hg y hy => (hP _).2 fun g' hg' => by
    have hgg : g' * g ∈ Formalism.QuantumDeterminants.UH Hm := by
      have e1 : gᴴ * Hm * g = Hm := hg
      have e2 : g'ᴴ * Hm * g' = Hm := hg'
      show _ = _
      rw [conjTranspose_mul]
      calc gᴴ * g'ᴴ * Hm * (g' * g) = gᴴ * (g'ᴴ * Hm * g') * g := by simp only [Matrix.mul_assoc]
        _ = Hm := by rw [e2, e1]
    have := (hP y).1 hy _ hgg
    rwa [hσ.1.2 _ hg' _ hg] at this) with hb | ht
  · have : v ∈ P := (hP v).2 fun g hg => hz (fun _ => g) fun _ => hg
    rw [hb] at this
    exact absurd this hv0
  · have := (hP l).1 (ht ▸ Submodule.mem_top) 1 hone
    rw [hσ.1.1] at this
    exact inner_self_eq_zero.1 this

theorem torEl_mem {q : ℕ} {x₀ : Mt n} (h : OrthFr Hm q x₀) (s : Unit → Fin n → ℝ) :
    torEl (fun _ : Unit => x₀) s () ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hx : IsUnit x₀.det := (dets_ne h).2.isUnit
  have hx' : IsUnit x₀ᴴ.det := by rw [det_conjTranspose]; exact hx.star
  set d : Mt n := diagonal fun a => Complex.exp ((s () a : ℂ) * Complex.I) with hd
  have e : dᴴ * (x₀ᴴ * Hm * x₀) * d = x₀ᴴ * Hm * x₀ := by
    rw [h.2, hd, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    change (starRingEnd ℂ) (Complex.exp ((s () i : ℂ) * Complex.I)) * _ * _ = _
    rw [mul_right_comm, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    simp
  show (x₀ * d * x₀⁻¹)ᴴ * Hm * (x₀ * d * x₀⁻¹) = Hm
  calc (x₀ * d * x₀⁻¹)ᴴ * Hm * (x₀ * d * x₀⁻¹) = (x₀ᴴ)⁻¹ * (dᴴ * (x₀ᴴ * Hm * x₀) * d) * x₀⁻¹ := by
        simp only [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc]
    _ = Hm := by
      rw [e, Matrix.mul_assoc x₀ᴴ, Matrix.nonsing_inv_mul_cancel_left _ _ hx', Matrix.mul_nonsing_inv_cancel_right _ _ hx]

theorem wt_int {ε : Fin n → Bool} {μ : Fin n → ℝ} (h1 : σ 1 = 1) (hv0 : v ≠ 0) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v)
    (a : Fin n) : ∃ m : ℤ, (m : ℝ) = μ a := by
  have h := hv (Pi.single a (2 * Real.pi)) (diag_mem _)
  have e : (diagonal fun b => Complex.exp ((((Pi.single a (2 * Real.pi) : Fin n → ℝ) b : ℝ) : ℂ) * Complex.I)) = (1 : Mt n) := by
    rw [← diagonal_one]
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb]
  rw [e, h1, Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp), Pi.single_eq_same] at h
  have h2 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 :=
    (smul_left_injective ℂ hv0 (h.symm.trans (one_smul ℂ v).symm))
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨m, ?_⟩
  have h3 : ((μ a : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = m * (2 * Real.pi * Complex.I) := by
    rw [← hm]; push_cast; ring
  exact_mod_cast (mul_right_cancel₀ Complex.two_pi_I_ne_zero h3).symm

theorem exists_ext_mem {ε : Fin n → Bool} {Λ : Fin n → ℝ} (hU : IsURepOn (UJset ε) σ) {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : ∃ w ∈ S, ‖w‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Λ (revNeg ε a)) w := by
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  have hK := pM_mem (revNeg ε) (eps_revNeg ε)
  have hn : ‖σ (pM (revNeg ε)) v‖ = ‖v‖ := hU.2.1 _ (kset_uj hK) v
  have hp : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • σ (pM (revNeg ε)) v, Submodule.smul_mem _ _ (hS.2.1 _ hK v hvS), ?_,
    isWtOn_smul (isWtOn_perm hU _ (eps_revNeg ε) hv) _⟩
  rw [norm_smul, hn, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hp]

end General

theorem torus_wt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {w : D.what₂.Tau → Fin V.rank → ℤ}
    (hw : WtIs M w) (τ : D.what₂.Tau) {l : M.H τ} (hl : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) l)
    (s : Unit → Fin V.rank → ℝ) (hx : (x0Mat M τ).det ≠ 0) :
    M.rep τ (torEl (fun _ : Unit => x0Mat M τ) s ()) l = torCh (fun _ : Unit => w τ) s • l := by
  set e := Equiv.ofBijective _ (arr_bijective (nNeg_le (M.ε τ))) with he
  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 := torus_x0Mat M τ fun a => Complex.exp ((s () (e.symm a) : ℂ) * Complex.I)
  have h2 : ∀ c, e.symm (arr (nNeg (M.ε τ)) c) = c := fun c => e.symm_apply_apply c
  simp only [h2] at h1
  have h3 : M.fr τ * torEl (fun _ : Unit => x0Mat M τ) s () * (M.fr τ)⁻¹ =
      diagonal fun a => Complex.exp ((s () (e.symm a) : ℂ) * Complex.I) := by
    unfold torEl
    rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ hx.isUnit, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hfr, Matrix.mul_nonsing_inv_cancel_right _ _ hfr]
  unfold DSModel.rep torCh
  rw [h3, hl (fun a => s () (e.symm a)) (diagonal_mem_Kset _ _), Fintype.prod_unique]
  congr 1
  rw [← e.sum_comp]
  simp only [← Complex.exp_int_mul, ← Complex.exp_sum, Equiv.symm_apply_apply]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : extWt M τ (e c) = (w τ c : ℝ) := (hw τ c).symm
  rw [h4]
  push_cast
  ring

theorem lowSm_and_lowIrr : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), HolShape M →
    LowSm M ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M := by
  intro D V S M hM
  choose S₀ hS₀ hsm using GlobalTheory.SmoothLowType.exists_lowK_le_sm D V S M
  have hU := fun τ => (M.ds τ).2.2.1
  choose v hvS hv1 hvw using fun τ => exists_ext_mem (hU τ) (hS₀ τ)
  have hv0 : ∀ τ, v τ ≠ 0 := fun τ h => by simpa [h] using hv1 τ
  choose w hw using fun τ c => wt_int (hU τ).1.1 (hv0 τ) (hvw τ) (arr (nNeg (M.ε τ)) c)
  have hW : WtIs M w := hw
  have hle : ∀ τ, S₀ τ ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := fun τ =>
    le_sSup (s := {S | IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S}) (hS₀ τ)
  have hE : IsExtVec M fun τ => ⟨v τ, hsm τ (hvS τ)⟩ := fun τ => ⟨hv1 τ, hle τ (hvS τ), hvw τ⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have key : ∀ τ, lowKSub (M.ε τ) (M.lam τ) (M.σ τ) = S₀ τ := fun τ => by
    refine le_antisymm (sSup_le fun T hT => ?_) (hle τ)
    have hT : IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) T := hT
    obtain ⟨v', hv'T, hv'1, hv'w⟩ := exists_ext_mem (hU τ) hT
    obtain ⟨hc, hR, hI, hx⟩ := GlobalTheory.HolDict.ModelRep.model_rep D V S M τ
    obtain ⟨ho, -⟩ := hx hM
    obtain ⟨hs, hk⟩ := GlobalTheory.HolDict.VKill.borel_extVec D θ V S M w _ hθ hM hW hE τ
    have hl : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (extWt M τ) (v' - ⟪v τ, v'⟫_ℂ • v τ) := fun t ht => by
      rw [map_sub, map_smul, hv'w t ht, hvw τ t ht, smul_sub, smul_comm]
      rfl
    have hz : v' - ⟪v τ, v'⟫_ℂ • v τ = 0 :=
      eq_zero_of_orth ho hR hI hs (hv0 τ) hk _ (torEl_mem ho) (fun s => torus_wt M hW τ hl s (dets_ne ho).2) (by
        rw [← inner_conj_symm, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv1]
        simp)
    have hv'S : v' ∈ S₀ τ := by
      rw [sub_eq_zero.1 hz]
      exact Submodule.smul_mem _ _ (hvS τ)
    rcases hT.2.2.1 (T ⊓ S₀ τ) inf_le_left (fun g hg y hy => ⟨hT.2.1 g hg y hy.1, (hS₀ τ).2.1 g hg y hy.2⟩) with h | h
    · have : v' ∈ T ⊓ S₀ τ := ⟨hv'T, hv'S⟩
      rw [h, Submodule.mem_bot] at this
      simp [this] at hv'1
    · exact h ▸ inf_le_right
  exact ⟨fun τ => key τ ▸ hsm τ, fun τ => key τ ▸ hS₀ τ⟩

end GlobalTheory.HolLowOnce
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrreduStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDiscreteSeries_lowestKType_smooth_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), HolShape M → LowSm M ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M := by
  first | exact @GlobalTheory.HolLowOnce.lowSm_and_lowIrr | exact GlobalTheory.HolLowOnce.lowSm_and_lowIrr | (intros; apply GlobalTheory.HolLowOnce.lowSm_and_lowIrr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCoordPre
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.PinsCoord

theorem extTo_basis {E : Type} [Field E] (n N : ℕ) (a : Fin n) (b : Fin N) (h : (a:ℕ) = b) : DiagSp.extTo (E := E) n N (Pi.basisFun E (Fin n) a) = Pi.basisFun E (Fin N) b := by
  funext i
  simp only [Pi.basisFun_apply]
  show (if h : (i:ℕ) < n then (Pi.single a (1:E) : Fin n → E) ⟨i, h⟩ else 0) = _
  by_cases e : i = b
  · subst e
    have : (i:ℕ) < n := h ▸ a.2
    rw [dite_eq_left this, show (⟨i, this⟩ : Fin n) = a from Fin.ext h.symm]; simp
  · rw [Pi.single_eq_of_ne e]
    split_ifs with h1
    · exact Pi.single_eq_of_ne (fun e' => e (Fin.ext (by rw [← h, ← e']))) _
    · rfl

end GlobalTheory.Mem.Col2.PinsCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHJsymIffJSymG
open Formalism.L2.Col

namespace GlobalTheory

theorem mem_HJsym_iff_JSymG : ∀ (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n), r = k + 2 * rS + 1 → 0 < t → n = r + m * t →
    ∀ M : GL (Fin n) κ, M ∈ HJsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t false := by
  intro κ _ n k r t m rS h hr ht hn M
  subst hr
  rw [HJsym_eq_JSymG ht (by omega) h]

end GlobalTheory
end
