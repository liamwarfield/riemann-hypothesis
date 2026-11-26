module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricLevelClausesHold
public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsView
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FnOfMapInjective
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Core

theorem fnOf_map_injective {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (sh : ι → ℤ) (s : K →+* ℂ) {F F' : MvPolynomial (ι × Fin n × Fin n) K}
    (h : fnOf G sh 1 (MvPolynomial.map s F) = fnOf G sh 1 (MvPolynomial.map s F')) : F = F' :=
  MvPolynomial.map_injective s s.injective
    (Formalism.L2.Col.fnOf_injective G sh 1 (fun _ => by simp)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}) h)

theorem exists_ptVal_at (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K) (x : (D.fm u).ptLat.V)
    (c : (D.fm u).clsP) : ∃ F : VV D.what₂.LL (sgT u),
      W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL F.1) := by
  obtain ⟨P, hP, hv⟩ := ((W.rat _).1 ⟨x, rfl⟩).2 c
  have e : Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) = Formalism.L2.Col.RatSpanG D.what₂.embLL (D.fm u).sg :=
    Formalism.L2.Col.RatSpanG_shW D.what₂.embLL (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
  have hP' : P ∈ Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) := by rw [e]; exact hP
  obtain ⟨F, hF, rfl⟩ := Formalism.L2.Col.exists_VV_of_mem_RatSpanG _ _ hP'
  exact ⟨⟨F, hF⟩, hv⟩

theorem exists_ptVal : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K), ∃ val : (D.fm u).ptLat.V →ₗ[D.what₂.LL] ((D.fm u).clsP → VV D.what₂.LL (sgT u)), (∀ x c, W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (val x c).1)) := by
  intro D u K W
  choose val hval using exists_ptVal_at D u K W
  refine ⟨{ toFun := val, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hval⟩
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    rw [← hval, Pi.add_apply, Submodule.coe_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ← hval, ← hval, Pi.add_apply]
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    have e : MvPolynomial.map D.what₂.embLL (a • (val x c).1) =
        D.what₂.embLL a • MvPolynomial.map D.what₂.embLL (val x c).1 := by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    rw [← hval, RingHom.id_apply, Pi.smul_apply, Submodule.coe_smul, e, LinearMap.map_smul, ← hval,
      LinearMap.map_smulₛₗ, LinearEquiv.map_smul, Pi.smul_apply]

end GlobalTheory.Core
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapAtEveryTrueColumnMember
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapOfSymmetricComparisonLowerMapFiniteChar
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPendingObjectSymmetricFormsLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PtCoMemIntSpan
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.PtCo

theorem intSpan_smul' (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem ptCo_one (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf)
    (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c))
    (w : D.what₂.places.Pl) (y : (D.fm u).ptLat.V) (hy : y ∈ (D.fm u).ptLat.L) (c : (D.fm u).clsP) :
    Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  obtain ⟨P, hP, hq⟩ := (Tf.valP.lat y).1 hy w c (B w c) (hB w c)
  rw [Matrix.coe_units_inv] at hq
  have e : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c = P := by
    change fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u))
      (atInf (embT D) ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹)
      (Tf.valP.eW ((D.fm u).ptEmb y) c) = P
    rw [hq, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ (Matrix.isUnits_det_units (B w c)))]
  rw [e]
  exact hP

theorem ptCo_mem_intSpan : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E), (∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c)) → ∀ w, ∀ y ∈ (D.fm u).SP w, ∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg := by
  intro D u Ch chOf Tf B hB w y hy c
  induction hy using Submodule.span_induction with
  | mem y hy => exact ptCo_one D u Ch chOf Tf B hB w y hy c
  | zero => rw [map_zero, map_zero, Pi.zero_apply]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), Pi.add_apply]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : D.what₂.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, map_smul, Pi.smul_apply]
    exact intSpan_smul' D w _ (r : D.what₂.LL) r.2 _ hy

end GlobalTheory.PtCo

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPtEmbOfCoordInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.FormsRatOfInt

theorem intSpan_le_ratSpan (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam ≤ Formalism.L2.Forms.RatSpan D lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan Formalism.L2.Forms.RatSpan
  apply AddSubgroup.closure_mono
  rintro p ⟨r, f, -, hf, rfl⟩
  exact ⟨r, f, hf, rfl⟩

theorem exists_ptEmb_of_coord_int : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl), ∀ z ∈ (D.fm u).ptC, (∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg) → ∃ y, (D.fm u).ptEmb y = z := by
  intro D u Ch chOf Tf B w z hz hint
  refine (Tf.valP.rat z).2 ⟨hz, fun c => ?_⟩
  have hB : IsUnit ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (B w c))
  obtain ⟨Q, hQ, hq⟩ := Formalism.L2.GlobalTheoryTheory.Br.eW_repS Tf _ hB z hz c
  have hco : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c = Q := by
    change fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u))
      (atInf (embT D) ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹)
      (Tf.valP.eW z c) = Q
    have hemb : Formalism.L2.embT D = embT D := rfl
    rw [hq, hemb, fnInv_fnOf _ _ _ (atInf_inv_isUnit _ hB)]
  have hQr : Q ∈ Formalism.L2.Forms.RatSpan D (D.fm u).sg := intSpan_le_ratSpan D w _ (hco ▸ hint c)
  obtain ⟨Q', hQ', he⟩ := GlobalTheory.LevelHecke.exists_ratSpan_fnOf_atInf (D.fm u).sg _ (shiftOf (sgT u))
    (((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹) hQr
  exact ⟨Q', hQ', hq.trans he⟩

end GlobalTheory.FormsRatOfInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoMTSOfGaInv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory

open Matrix MvPolynomial Formalism.L2.GlobalTheoryTheory.Br


set_option maxHeartbeats 1000000 in
theorem coMTS_of_gaInv : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B' : GL (Fin (D.R.N D.R.m)) D.host.E), IsUnit (B w c).det → (B' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) * bZg u Tf.til.z0 (B w c) → ∀ (f : (D.mem u).C.Y D.R.m → ℂ) (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ), (∀ z, f z = fnOf _ (shiftOf (lamT u D.R.m)) (atInf (embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) → Formalism.L2.GlobalTheoryTheory.Br.coMTS Tf B w c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) • P := by
  intro D u Ch chOf Tf B w c B' hBdet hB' f P hf
  have hg : ∃ g : GL (Fin (D.R.N D.R.m)) D.host.E, g = (Tf.til.ga c).1 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := hg
  rw [← hg] at hB'
  have hbZg := bZg_isUnitS Tf (B w c) hBdet
  have hU2 := atInf_inv_isUnit _ hbZg

  have hprod : ∀ τ, atInf (embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ *
      atInf (embT D) ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ =
      atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ := by
    intro τ
    simp only [atInf]
    rw [← Matrix.map_mul]
    congr 1
    have e1 : ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *
        ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) =
        (((g * B')⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    have e2 : ((g * B' : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = bZg u Tf.til.z0 (B w c) := by
      rw [Units.val_mul, hB', ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e1, Matrix.coe_units_inv, e2]
  subst hg
  have hT : trEvS Tf c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) •
      fnOf (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m))
        (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) P := by
    funext y
    simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, hf, Equiv.apply_symm_apply]
    congr 1
    have hemb : Formalism.L2.embT D = embT D := rfl
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, hemb, ← Matrix.mul_assoc, hprod]
  change fnInv (gramC (gramN D D.R.m le_rfl) (embT D)) (shiftOf (lamT u D.R.m))
    (atInf (embT D) (bZg u Tf.til.z0 (B w c))⁻¹) (trEvS Tf c f) = _
  rw [hT, map_smul, fnInv_fnOf _ _ _ hU2]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsLocBasisClsP
noncomputable section

namespace GlobalTheory.ClsPLocBasis

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem exists_isLocBasis_clsP : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (w : D.what₂.places.Pl) (c : (D.fm u).clsP),
    ∃ B : GL (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) B := by
  intro D u Ch chOf Tf w c
  have hL : Submodule.IsFullLattice D.host.E (Tf.clsP.lat c) :=
    Formalism.MainNotions.G.ChF.isLattice_of_hat Tf.clsP.lev.Lb (Tf.clsP.lat c) Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span
      (Tf.clsP.y c).1 (Tf.clsP.y_lat c)
  have hspan : Submodule.span D.host.E (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) = ⊤ := by
    have hG := Formalism.UG.P.csGlob_lattice (F := D.host.F) Tf.clsP.lev.Lb Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span (Tf.clsP.y c).1
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact Formalism.L2.GlobalTheoryTheory.Br.latS_mem_span (F := D.host.F) _ x ((Tf.clsP.y_lat c _).2 hx)
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (D.what₂.places.resChar w) D.host.E (Tf.clsP.lat c) hL.fg hspan

end GlobalTheory.ClsPLocBasis
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.RedPt0Pend

section LocalBases

open Matrix

theorem isLocBasis_of_split {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : n + 1 = N) {p : ℕ} (hp : p.Prime)
    (L : Set (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)) (B : GL (Fin n) E) (hB : IsLocBasis p (L' : Set (Fin n → E)) B)
    (B' : GL (Fin N) E)
    (h : ∀ v : Fin N → E, (B' : Matrix (Fin N) (Fin N) E) *ᵥ v ∈ L ↔
      (B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩) ∈ L' ∧
        v ⟨n, by omega⟩ ∈ (algebraMap (𝓞 E) E).range) : IsLocBasis p L B' := by
  intro x
  obtain ⟨v, rfl⟩ : ∃ v, x = (B' : Matrix (Fin N) (Fin N) E) *ᵥ v :=
    ⟨((B'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x, by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩
  have e1 : ((B'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ ((B' : Matrix (Fin N) (Fin N) E) *ᵥ v) = v := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hB1 := hB ((B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩))
  have e2 : ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ
      ((B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩)) = fun i : Fin n => v ⟨i, by omega⟩ := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rw [e2] at hB1
  rw [e1]
  set R := (algebraMap (𝓞 E) E).range
  have hR : ∀ (s : ℕ) {y : E}, y ∈ R → (s : E) * y ∈ R := fun s y hy => R.mul_mem (natCast_mem R s) hy
  have memL : ∀ s : ℕ, (s : E) • ((B' : Matrix (Fin N) (Fin N) E) *ᵥ v) ∈ L ↔
      (s : E) • ((B : Matrix (Fin n) (Fin n) E) *ᵥ (fun i : Fin n => v ⟨i, by omega⟩)) ∈ L' ∧ (s : E) * v ⟨n, by omega⟩ ∈ R := by
    intro s
    rw [← mulVec_smul, h, ← mulVec_smul]
    rfl
  have hnd : ∀ a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun a b ha hb h =>
    (hp.dvd_mul.mp h).elim ha hb
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨h1, h2⟩ := (memL s).mp hx
    obtain ⟨s', hs', h3⟩ := hB1.mp ⟨s, hs, h1⟩
    refine ⟨s * s', hnd _ _ hs hs', fun a => ?_⟩
    by_cases ha : (a : ℕ) < n
    · rw [Nat.cast_mul, mul_assoc]; exact hR s (h3 ⟨a, ha⟩)
    · have ea : a = ⟨n, by omega⟩ := Fin.ext (by have := a.2; simp only; omega)
      rw [ea, Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
  · rintro ⟨s, hs, h0⟩
    obtain ⟨s', hs', h3⟩ := hB1.mpr ⟨s, hs, fun a => h0 _⟩
    refine ⟨s * s', hnd _ _ hs hs', (memL _).mpr ⟨?_, ?_⟩⟩
    · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
      exact nsmul_mem h3 s
    · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' (h0 _)

theorem cols_mulVec {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (v : Fin N → E) :
    (Matrix.of fun a (b : Fin N) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ v =
      A *ᵥ (fun i : Fin n => v ⟨i, by omega⟩) + v ⟨n, by omega⟩ • z := by
  subst hN
  funext a
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, of_apply,
    Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, Fin.eta]
  rw [mul_comm (z a)]
  rfl

theorem hform_add_left' {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right' {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end LocalBases

section Dual

open Matrix Formalism.L2.GlobalTheoryTheory.Br Formalism.UG


set_option maxHeartbeats 1000000 in
theorem mem_dual_tilde_iff {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (Tf : FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (a : Fin (D.R.N D.R.m - 1) → D.host.E) (t : D.host.E) :
    iXc D a + (t / ((D.mem u).A.T : D.host.E)) • Tf.til.z0 ∈
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
        ((Tf.clsP.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {Tf.til.z0}) ↔
      a ∈ Tf.clsP.lat c ∧ t ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  obtain ⟨b, hb⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hzz := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have o1 : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) Tf.til.z0 = 0 := fun x => by
    rw [hb, hform_smul_rightB, hform_iXc_zc, mul_zero]
  have o2 : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Tf.til.z0 (iXc D x) = 0 := fun x => by
    rw [hb, hform_smul_leftB, hform_zc_iXc, mul_zero]
  have p1 : ∀ x, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x)
      (iXc D a + (t / ((D.mem u).A.T : D.host.E)) • Tf.til.z0) = hform (sigD D : D.host.E →+* D.host.E) (gramP D) x a := fun x => by
    rw [hform_add_right', hform_smul_rightB, o1, mul_zero, add_zero, hform_iXc]
  have p2 : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) Tf.til.z0
      (iXc D a + (t / ((D.mem u).A.T : D.host.E)) • Tf.til.z0) = t := by
    rw [hform_add_right', hform_smul_rightB, o2, zero_add, hzz, div_mul_cancel₀ _ hT]
  have hSD := (GlobalTheory.ClassLatticeSelfDual.classLattice_selfDual D u Tf.clsP c).2 a
  constructor
  · intro h
    refine ⟨hSD.2 fun x hx => ?_, ?_⟩
    · rw [← p1]
      exact h _ (Submodule.mem_sup_left ⟨x, hx, rfl⟩)
    · rw [← p2]
      exact h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · rintro ⟨ha, ht⟩ y hy
    obtain ⟨_, ⟨x, hx, rfl⟩, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy2
    have er : r • Tf.til.z0 = (r : D.host.E) • Tf.til.z0 := (algebraMap_smul D.host.E r _).symm
    have ex : ((iXc D).restrictScalars (𝓞 D.host.E)) x = iXc D x := rfl
    rw [hform_add_left', er, ex, hform_smul_leftB, p1, p2]
    refine add_mem (hSD.1 ha x hx) (mul_mem ?_ ht)
    exact ⟨⟨_, r.2.map (sigD D : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩


set_option maxHeartbeats 1000000 in
theorem exists_isLocBasis_dual (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) B) :
    ∃ B' : GL (Fin (D.R.N D.R.m)) D.host.E, (B' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) =
      ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *
        bZg u Tf.til.z0 (B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) ∧
      IsLocBasis (D.what₂.places.resChar w)
        (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (clsCrd D u D.R.m le_rfl ((D.fm u).til c))) B' := by
  have hU := bZg_isUnitS Tf (B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (Matrix.isUnits_det_units B)
  obtain ⟨Z, hZ⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hU
  refine ⟨((Tf.til.ga c).1)⁻¹ * Z, by rw [Units.val_mul, hZ], ?_⟩
  refine isLocBasis_of_split (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (D.what₂.places.resChar_prime w) _ (Tf.clsP.lat c) B hB _ fun v => ?_
  have hv : (Z : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *ᵥ v =
      iXc D ((B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) *ᵥ
        (fun i : Fin (D.R.N D.R.m - 1) => v ⟨i, by have := Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R; omega⟩)) +
      (v ⟨D.R.N D.R.m - 1, by have := Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R; omega⟩ / ((D.mem u).A.T : D.host.E)) • Tf.til.z0 := by
    rw [hZ]
    refine (cols_mulVec (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D * (B : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E))
      (fun a => Tf.til.z0 a / ((D.mem u).A.T : D.host.E)) v).trans ?_
    rw [← mulVec_mulVec, iXm, LinearMap.toMatrix'_mulVec]
    congr 1
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [← mem_dual_tilde_iff Tf c, ← hv, ← Tf.til.til_lat c, Units.val_mul, ← mulVec_mulVec]
  set y := (Z : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *ᵥ v
  have hy : (Tf.til.ga c).1.1 *ᵥ (((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *ᵥ y) = y := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  constructor
  · rintro h _ ⟨l, hl, rfl⟩
    have := h l hl
    rw [← ga_herm Tf c, hy] at this
    exact this
  · intro h l hl
    rw [← ga_herm Tf c, hy]
    exact h _ ⟨l, hl, rfl⟩

end Dual

section Localisation

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Col

theorem mem_localization_delAtr_of_basis {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
    (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
    (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
    {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (s : K →+* ℂ) (eT : ι → E →+* ℂ)
    (he : embAt s emb = eT) (J : Matrix (Fin n) (Fin n) E)
    (lam lam' : ι → DomWeight n) (hn : ∀ τ, (lam τ).natW = (lam' τ).natW)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M) (F : VV K lam) (w : Pl.Pl) (B : GL (Fin n) E)
    (hB : IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B)
    (h : Formalism.L2.Forms.fnInv (gramC J eT) (shiftOf lam) (atInf eT (B : Matrix (Fin n) (Fin n) E)⁻¹)
      (fnOf (gramC J eT) (shiftOf lam) 1 (MvPolynomial.map s F.1)) ∈ vlIntSpan s Pl w lam') :
    F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) := by
  subst he
  have e := vl_coord emb s J lam B F
  have e' : fnOf (gramC J (embAt s emb)) (shiftOf lam) 1 (MvPolynomial.map s F.1) = evV emb J lam s F := rfl
  rw [e', e, ← Matrix.coe_units_inv, Formalism.L2.Forms.fnInv_fnOf _ _ (atInf (embAt s emb) ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
    (fun τ => Matrix.isUnits_det_units (Matrix.GeneralLinearGroup.map (embAt s emb τ) B⁻¹))] at h
  exact (mem_localization_iff_forall_localBasis_of_valuation Pl pw hval emb s w J lam lam' hn (fun _ => M) (fun _ => hM) F (fun _ => B) (fun _ => hB)).2
    ⟨_, h, e⟩

theorem local_of_mem_delAtr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (Pl : Rows.Places K)
    (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
    (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))
    {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (s : K →+* ℂ) (eT : ι → E →+* ℂ)
    (he : embAt s emb = eT) (hpw : Function.Surjective pw) (J : Matrix (Fin n) (Fin n) E)
    (lam lam' : ι → DomWeight n) (hn : ∀ τ, (lam τ).natW = (lam' τ).natW)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsFullLattice E M) (F : VV K lam) (hF : F ∈ delAtr emb lam M)
    (w : Pl.Pl) (B : GL (Fin n) E) (hB : IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B) :
    ∃ P ∈ vlIntSpan s Pl w lam',
      fnOf (gramC J eT) (shiftOf lam) 1 (MvPolynomial.map s F.1) =
        fnOf (gramC J eT) (shiftOf lam) (atInf eT (B⁻¹ : GL (Fin n) E).1) P := by
  subst he
  have hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ M)) (vlBd emb B τ) := fun τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
      (vl_isBasisAt_tauLat Pl pw hval emb τ w M B hB)
  change F.1 ∈ transLat lam (delStd K lam) (fun τ => dualFr (tauLat emb τ M)) at hF
  rw [nb_mem_transLat] at hF
  exact ⟨_, vl_map_mem_intSpan Pl pw hval s w lam lam' hn (hF (pw w) _ hbas), vl_coord emb s J lam B F⟩


set_option maxHeartbeats 1000000 in
theorem mem_SP_of_coord_integral (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hB : ∀ w c, IsLocBasis (D.what₂.places.resChar w) (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)) (B w c))
    (w : D.what₂.places.Pl) (y : (D.fm u).ptLat.V)
    (h : ∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w ((D.fm u).ptEmb y) c ∈
        Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg) : y ∈ (D.fm u).SP w := by
  classical
  obtain ⟨val, hval⟩ := GlobalTheory.Core.exists_ptVal D u Tf.clsP Tf.valP
  have hK := fun c => Formalism.MainNotions.G.ChF.isLattice_of_hat Tf.clsP.lev.Lb
    (Tf.clsP.lat c) Tf.clsP.lev.Lb_fin Tf.clsP.lev.Lb_span (Tf.clsP.y c).1 (Tf.clsP.y_lat c)
  have he : embAt D.what₂.embLL (fun τ : D.what₂.Tau =>
      D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) = embT D := by
    funext τ
    ext y
    exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) y)
  have hc : ∀ c, val y c ∈ Formalism.HermitianLatticesTheory.localization₂ (D.plEq w).asIdeal (delAtr (fun τ : D.what₂.Tau =>
      D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)) (sgT u) (Tf.clsP.lat c)) := by
    intro c
    refine mem_localization_delAtr_of_basis D.what₂.places D.plEq D.val_eq _ D.what₂.embLL (embT D) he (gramP D) (sgT u) (D.fm u).sg
      (fun τ => natW_shW _ _) (Tf.clsP.lat c) (hK c) (val y c) w (B w c) (hB w c) ?_
    have := h c
    change fnInv (gramC (gramP D) (embT D)) (shiftOf (sgT u))
      (atInf (embT D) ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹)
      (Tf.valP.eW ((D.fm u).ptEmb y) c) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg at this
    rw [hval] at this
    exact this
  choose s hs hx using hc
  refine (vl_mem_span_intW_iff D.what₂.places (fun w => D.plEq w) D.val_eq w _ _).2 ⟨∏ c, s c, ?_, ?_⟩
  · intro hmem
    obtain ⟨c, -, hc⟩ := ((D.plEq w).isPrime.prod_mem_iff).1 hmem
    exact hs c hc
  · refine (Tf.valP.lat _).2 fun w' c B' hB' => ?_
    rw [hval]
    refine local_of_mem_delAtr D.what₂.places D.plEq D.val_eq _ D.what₂.embLL (embT D) he D.plEq.surjective (gramP D) (sgT u)
      (D.fm u).sg (fun τ => natW_shW _ _) (Tf.clsP.lat c) (hK c) _ ?_ w' B' hB'
    have e : (∏ c', s c') = (∏ c' ∈ Finset.univ.erase c, s c') * s c := (Finset.prod_erase_mul _ _ (Finset.mem_univ c)).symm
    have key : ∀ r : 𝓞 D.what₂.LL, val (r • y) c = r • val y c := fun r => by
      rw [← algebraMap_smul D.what₂.LL r y, map_smul, Pi.smul_apply, algebraMap_smul]
      rfl
    have hm := Submodule.smul_mem _ (∏ c' ∈ Finset.univ.erase c, s c') (hx c)
    rw [key, e]
    convert hm using 1
    exact mul_smul _ _ _

end Localisation

theorem intSpan_smul' (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem root_mem_intW (D : D7) (w : D.what₂.places.Pl) (r : D.what₂.LL) (n : ℕ) (hn : 0 < n) (h : r ^ n = 1) :
    r ∈ intW D.what₂.places w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w r
  have h1 : D.what₂.places.val w (r ^ n) = 0 := by rw [h, AddValuation.map_one]
  rw [AddValuation.map_pow] at h1
  by_contra hneg
  push_neg at hneg
  have : n • D.what₂.places.val w r < 0 := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, D.what₂.places.val w r = k := by
      rcases h2 : D.what₂.places.val w r with _ | k
      · rw [h2] at hneg; exact absurd hneg (not_lt.2 le_top)
      · exact ⟨k, rfl⟩
    rw [hk] at hneg ⊢
    have hk0 : k < 0 := by exact_mod_cast hneg
    have : (n : ℤ) * k < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hn) hk0
    rw [← WithTop.coe_nsmul]
    exact_mod_cast (by simpa [nsmul_eq_mul] using this)
  rw [h1] at this
  exact lt_irrefl _ this


set_option maxHeartbeats 4000000 in
theorem exists_integralPendingObject_symmetricFormsLevel : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → (∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)) → ∃ P : Formalism.MainNotions.product_first_zeroth_parts.Pend D u, Formalism.MainNotions.product_first_zeroth_parts.ArchimedeanSignatureMatching P := by
  intro D u Ch chOf Tf hMap hBe hχ
  choose B hB using GlobalTheory.ClsPLocBasis.exists_isLocBasis_clsP D u Ch chOf Tf
  obtain ⟨o, ho⟩ := Formalism.L2.GlobalTheoryTheory.Br.exists_onP Tf
  set Bm : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E :=
    fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) with hBm
  have hBu : ∀ w c, IsUnit (Bm w c).det := fun w c => (Matrix.isUnit_iff_isUnit_det _).1 (B w c).isUnit
  have hL : Formalism.L2.GlobalTheoryTheory.Br.LowerSymmetricCompatible Tf := ⟨hBe, hMap⟩
  refine Formalism.L2.GlobalTheoryTheory.Br.brExists_of_rest4S Tf hL Bm hBu (gPof Bm hBu o) ⟨?_, ?_,
    Formalism.L2.GlobalTheoryTheory.Br.ipV_co_ofS Tf Bm hBu o ho, Formalism.L2.GlobalTheoryTheory.Br.weightedInner_self_eq_sum_coords_of_orthonormal' Tf Bm hBu o (fun τ => Or.inl (ho τ))⟩
  · intro w x hx c
    obtain ⟨B', hB'eq, hB'⟩ := exists_isLocBasis_dual D u Ch chOf Tf w c (B w c) (hB w c)
    obtain ⟨n, hn, hχ'⟩ := hχ
    obtain ⟨hpow, r, hr⟩ := hχ' (Tf.tilAd.ka c)
    have hrn : r ^ n = 1 := by
      apply D.what₂.embLL.injective
      rw [map_pow, hr, map_one, hpow]
    have hr0 : r ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hrn; exact zero_ne_one hrn
    have hri : r⁻¹ ∈ intW D.what₂.places w := by
      have : r⁻¹ = r ^ (n - 1) := (eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hn.ne', hrn])).symm
      rw [this]; exact pow_mem (root_mem_intW D w r n hn hrn) _
    have hχr : ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) = D.what₂.embLL r⁻¹ := by
      rw [Units.val_inv_eq_inv_val, ← hr, map_inv₀]
    have hx' : x ∈ Submodule.span (intW D.what₂.places w) (((D.fm u).lat D.R.m).L : Set ((D.fm u).lat D.R.m).V) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨P, hP, hPv⟩ := ((Tf.val D.R.m le_rfl (Or.inr rfl)).lat y).1 hy w ((D.fm u).til c) B' hB'
      rw [GlobalTheory.coMTS_of_gaInv D u Ch chOf Tf Bm w c B' (hBu w c) hB'eq _ P hPv, hχr]
      exact intSpan_smul' D w _ _ hri P hP
    | zero => rw [map_zero, Pi.zero_apply, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), Pi.add_apply, map_add (f := _)]; exact add_mem hy hz
    | smul a y _ hy =>
      have e : a • y = (a : D.what₂.LL) • y := rfl
      rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, map_smul]
      exact intSpan_smul' D w _ (a : D.what₂.LL) a.2 _ hy
  · intro w z hz
    constructor
    · rintro ⟨y, hy, rfl⟩ c
      exact GlobalTheory.PtCo.ptCo_mem_intSpan D u Ch chOf Tf B hB w y hy c
    · intro h
      obtain ⟨y, rfl⟩ := GlobalTheory.FormsRatOfInt.exists_ptEmb_of_coord_int D u Ch chOf Tf B w z hz h
      exact ⟨y, mem_SP_of_coord_integral D u Ch chOf Tf B hB w y h, rfl⟩

end GlobalTheory.RedPt0Pend
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.RedPt0

theorem formsMap_of_symmetricComparison_lowerMap_finiteChar : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → (∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)) → Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u := by
  intro D u Ch chOf Tf hL hB hC
  obtain ⟨P, h4⟩ := GlobalTheory.RedPt0Pend.exists_integralPendingObject_symmetricFormsLevel D u Ch chOf Tf hL hB hC
  exact Formalism.MainNotions.product_first_zeroth_parts.classMap_estimate_of_partial P h4 (Formalism.L2.GlobalTheoryTheory.Br.symmetric_level_clauses_hold D u Ch chOf Tf hL hB)

end GlobalTheory.RedPt0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChiLastStepFiniteOrderSymTie
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLevHChiPowEqOneAndMemRange
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem gLevH_chi_pow_eq_one_and_mem_range : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))) (lam : ∀ a v h, H a v h →* ℂˣ) (_ : GLevH S G H lam) (K : Type) [Field K] (s : K →+* ℂ) (N : ℕ), (∀ i, (gp i).Prime) → (∀ a v h M, ((lam a v h M : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((lam a v h M : ℂˣ) : ℂ)) → ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G H lam L K _ s N _ hl x
  have hmul : ∀ a b : ℂ, (a ^ N = 1 ∧ ∃ r : K, s r = a) → (b ^ N = 1 ∧ ∃ r : K, s r = b) →
      ((a * b) ^ N = 1 ∧ ∃ r : K, s r = a * b) := by
    rintro a b ⟨ha, r, hr⟩ ⟨hb, r', hr'⟩
    exact ⟨by rw [mul_pow, ha, hb, one_mul], r * r', by rw [map_mul, hr, hr']⟩
  have hone : (1 : ℂ) ^ N = 1 ∧ ∃ r : K, s r = 1 := ⟨one_pow N, 1, map_one s⟩
  rw [L.chi_eq x]
  refine Finset.prod_induction _ (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hmul hone ?_
  intro a _
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro v
  refine finprod_induction (fun z : ℂ => z ^ N = 1 ∧ ∃ r : K, s r = z) hone hmul ?_
  intro h
  obtain ⟨h1, r, hr⟩ := hl a v h (L.red a v h x)
  exact ⟨by rw [inv_pow, h1, inv_one], r⁻¹, by rw [map_inv₀, hr]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LamJMemRangeAndPowEqOne
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → Nat.card k = p →
      (∃ ζ : K, IsPrimitiveRoot ζ p) → (∃ ζ : K, IsPrimitiveRoot ζ (p - 1)) →
      ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ)
        (M : Matrix (Fin n) (Fin n) k),
        (∃ r : K, s r = lamJ ψ χ a t nb skip M) ∧
          (lamJ ψ χ a t nb skip M ≠ 0 → lamJ ψ χ a t nb skip M ^ (p * (p - 1)) = 1) := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ ⟨ξ, hξ⟩ n ψ χ a t nb skip M
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  letI : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hψ : ∀ x : k, ψ x ^ p = 1 := by
    intro x
    rw [← AddChar.map_nsmul_eq_pow, ← hk, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  have hχ : ∀ (i : ℕ) (x : k), χ i x ≠ 0 → χ i x ^ (p - 1) = 1 := by
    intro i x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (MulChar.map_zero _)
    rw [← map_pow, ← hk', FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hψr : ∀ x : k, ψ x ∈ s.range := fun x =>
    complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ (hψ x)
  have hχr : ∀ (i : ℕ) (x : k), χ i x ∈ s.range := by
    intro i x
    by_cases hx : χ i x = 0
    · rw [hx]; exact zero_mem _
    · exact complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s (p - 1) ξ hp1 hξ _ (hχ i x hx)
  unfold lamJ
  refine ⟨?_, ?_⟩
  · exact mul_mem (hψr _) (prod_mem fun i _ => hχr i _)
  · intro h
    have h2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
    rw [mul_pow, pow_mul, hψ, one_pow, one_mul, mul_comm p, pow_mul, ← Finset.prod_pow,
      Finset.prod_eq_one (fun i hi => hχ i _ (h2 i hi)), one_pow]

end GlobalTheory
end

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem chi_last_step_finite_order_symTie : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) := by
  intro D u Ch chOf Tf hζ
  have hpos : ∀ i, 0 < D.host.g i * (D.host.g i - 1) := fun i =>
    Nat.mul_pos (D.host.g_prime i).pos (Nat.sub_pos_of_lt (D.host.g_prime i).one_lt)
  refine ⟨∏ i, D.host.g i * (D.host.g i - 1), Finset.prod_pos fun i _ => hpos i, ?_⟩
  refine GlobalTheory.gLevH_chi_pow_eq_one_and_mem_range _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glevM D.what₂.LL D.what₂.embLL _ D.host.g_prime ?_
  intro a v h M
  have key : (∃ r : D.what₂.LL, D.what₂.embLL r = ((Tf.lamM a v h M : ℂˣ) : ℂ)) ∧
      (((Tf.lamM a v h M : ℂˣ) : ℂ) ≠ 0 → ((Tf.lamM a v h M : ℂˣ) : ℂ) ^ (D.host.g a * (D.host.g a - 1)) = 1) := by
    rw [Tf.lamM_eq]
    unfold lamSym
    exact GlobalTheory.lamJ_mem_range_and_pow_eq_one _ D.what₂.LL D.what₂.embLL _ (D.host.g_prime a) (GlobalTheory.T.card_residue_field_totally_real_type_prime D a v h) (hζ a).1 (hζ a).2
      _ _ _ _ _ _ _ _
  refine ⟨?_, key.1⟩
  obtain ⟨c, hc⟩ : D.host.g a * (D.host.g a - 1) ∣ ∏ i, D.host.g i * (D.host.g i - 1) :=
    Finset.dvd_prod_of_mem (fun i => D.host.g i * (D.host.g i - 1)) (Finset.mem_univ a)
  rw [hc, pow_mul, key.2 (Units.ne_zero _), one_pow]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapAtEveryTrueColumnMember
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem formsMap_at_every_trueColumnMember : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (I.rec7 l Z) u := by
  intro B X I hOk hP l Z u
  obtain ⟨C, hC, -⟩ := GlobalTheory.Mem.Col2.TC.colsTiedSym_std I hOk hP l Z
  have hF := hC u
  have hL := GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie I hOk hP l Z u _ _ (C.forms u) hF
  have hB := GlobalTheory.Mem.Col2.TC.beOnTie_true I hOk hP l Z u
  have hR : ∀ i, (∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i)) ∧
      ∃ ζ : (I.rec7 l Z).what₂.LL, IsPrimitiveRoot ζ ((I.rec7 l Z).host.g i - 1) :=
    fun i => GlobalTheory.trueCols_exists_primitiveRoots I hOk l Z i
  exact GlobalTheory.RedPt0.formsMap_of_symmetricComparison_lowerMap_finiteChar (I.rec7 l Z) u _ _ (C.forms u) hL hB
    (GlobalTheory.chi_last_step_finite_order_symTie (I.rec7 l Z) u _ _ (C.forms u) hR)

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsMapAtEveryTrueColumnMemberStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_of_ok_of_pins : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (I.rec7 l Z) u := by
  first | exact @GlobalTheory.Mem.Col2.TC.formsMap_at_every_trueColumnMember | exact GlobalTheory.Mem.Col2.TC.formsMap_at_every_trueColumnMember | (intros; apply GlobalTheory.Mem.Col2.TC.formsMap_at_every_trueColumnMember <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferenceChainEvaluationBundlePointsOverColumnsA
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem constructedPoint_referenceChainWord_formsMap (Q : V4.Slot) (hQ : OverCols Q) (K : Ctx) (β : BPt K) (hq : β.Is Q) :
    ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 β.D u :=
  GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (fun _ _ _ w Z _ _ _ _ _ => GlobalTheory.T.aux_of_ok_of_pins w.I w.ok w.pins w.l Z)
    K β (hQ _ _ _ _ _ hq)

theorem referenceChainEvaluation_bundlePoints_overColumns : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints Q Lk :=
  fun Q hQ _ Lk => Row0.row (validForConstructedPointClasses_eventuallyWorkingClass (R := fun D _ => ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u)
    (EvP.of_all fun _ K _ β hq => constructedPoint_referenceChainWord_formsMap Q hQ K β hq)) Lk

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReferenceChainEvaluationBundlePointsOverColumnsAStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceChainEvaluationAtBundlePoints_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.ReferenceChainEvaluationAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.Fc.PeriodEntriesOverColumns.referenceChainEvaluation_bundlePoints_overColumns | exact GlobalTheory.Fc.PeriodEntriesOverColumns.referenceChainEvaluation_bundlePoints_overColumns | (intros; apply GlobalTheory.Fc.PeriodEntriesOverColumns.referenceChainEvaluation_bundlePoints_overColumns <;> assumption)
end
