module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecomposition
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDecomp

variable {D : D7}

theorem adj_eq' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := rfl

theorem frame_relations {V V' : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    adj D C' * V.gram * C = 1 ∧ (V'.gram⁻¹ * adj D B * V.gram) * C = 0 ∧
    (V'.gram⁻¹ * adj D B * V.gram) * C' = 0 ∧ (V'.gram⁻¹ * adj D B * V.gram) * B = 1 ∧
    adj D C * V.gram * C = 0 ∧
    C * (adj D C' * V.gram) + (B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram)) = 1 := by
  have hG : V.gramᴴ = V.gram := GlobalTheory.MixModel.gram_conjTranspose V
  have hC : Cᴴ * V.gram * C = 0 := by
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C = Cᴴ := adj_eq' C
    have := hs.frame.2.2
    rwa [e] at this
  have hB := hs.isom
  have hCB := hs.orth
  simp only [adj_eq'] at hB hCB h1 h2 h3 ⊢

  have hC'C : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose hCB
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hG' : V'.gram⁻¹ * V'.gram = 1 := Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V')
  have hPC : V'.gram⁻¹ * Bᴴ * V.gram * C = 0 := by
    simp only [Matrix.mul_assoc] at hBC ⊢; rw [hBC, Matrix.mul_zero]
  have hPC' : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0 := by
    simp only [Matrix.mul_assoc] at hBC' ⊢; rw [hBC', Matrix.mul_zero]
  have hPB : V'.gram⁻¹ * Bᴴ * V.gram * B = 1 := by
    simp only [Matrix.mul_assoc] at hB ⊢; rw [hB, hG']
  refine ⟨hC'C, hPC, hPC', hPB, hC, ?_⟩

  set P := V'.gram⁻¹ * Bᴴ * V.gram with hP
  let M : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E := Matrix.fromCols C (Matrix.fromCols B C')
  let N : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows (C'ᴴ * V.gram) (Matrix.fromRows P (Cᴴ * V.gram))
  have hNM : N * M = 1 := by
    simp only [N, M, Matrix.fromRows_mul, Matrix.mul_fromCols]
    ext (i | i | i) (j | j | j) <;>
      simp [hC'C, hPC, hPC', hPB, hC, h1, h2, h3, hCB, Matrix.one_apply]
  have hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have := hs.rank
    omega
  have hMN : M * N = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hNM
  simpa [M, N, Matrix.fromCols_mul_fromRows] using hMN


set_option maxHeartbeats 1000000 in
theorem decomp_exists : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  intro D V V' W r C B hs C' h1 h2 h3
  obtain ⟨hC'C, hPC, hPC', hPB, hCC, hid⟩ := frame_relations hs h1 h2 h3
  have hV'r := GlobalTheory.MixModel.ratL_eq W V'
  have hVr := GlobalTheory.MixModel.ratL_eq W V

  set f := incA D with hf
  set a := (adj D C' * V.gram).map f with ha
  set c := (adj D C * V.gram).map f with hc
  set p := (V'.gram⁻¹ * adj D B * V.gram).map f with hp
  set u := C.map f with hu
  set u' := C'.map f with hu'
  set b := B.map f with hb
  have m1 : ∀ {k l m : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E) (Y : Matrix (Fin l) (Fin m) D.host.E),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul).symm
  have z0 : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) D.host.E).map f = 0 := Matrix.map_zero _ (map_zero f)
  have o1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) D.host.E).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have au : a * u = 1 := by rw [ha, hu, m1, hC'C, o1]
  have cu : c * u = 0 := by rw [hc, hu, m1, hCC, z0]
  have pu : p * u = 0 := by rw [hp, hu, m1, hPC, z0]
  have au' : a * u' = 0 := by rw [ha, hu', m1, h2, z0]
  have cu' : c * u' = 1 := by rw [hc, hu', m1, h1, o1]
  have pu' : p * u' = 0 := by rw [hp, hu', m1, hPC', z0]
  have ab : a * b = 0 := by rw [ha, hb, m1, h3, z0]
  have cb : c * b = 0 := by rw [hc, hb, m1, hs.orth, z0]
  have pb : p * b = 1 := by rw [hp, hb, m1, hPB, o1]
  have key : u * a + (b * p + u' * c) = 1 := by
    rw [ha, hc, hp, hu, hu', hb, m1, m1, m1, ← Matrix.map_add f (map_add f), ← Matrix.map_add f (map_add f), hid, o1]

  have fwd : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      isoPart V W C' t + isoPart V W C y + midPart V V' W B x = t * a + y * c + x * p := fun _ _ _ => rfl
  have back : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      (t * a + y * c + x * p) * u = t ∧ (t * a + y * c + x * p) * u' = y ∧
        (t * a + y * c + x * p) * b = x := by
    intro t y x
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Matrix.add_mul, Matrix.mul_assoc, au, cu, pu, au', cu', pu', ab, cb, pb, Matrix.mul_one,
        Matrix.mul_zero, add_zero, zero_add]
  have cont : ∀ {k l m : ℕ} (Q : Mx D l m), Continuous fun z : Mx D k l => z * Q := by
    intro k l m Q
    exact continuous_id.matrix_mul continuous_const
  haveI := (GlobalTheory.MixModel.lattice_Mx D W.rank V.rank).1
  let e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W :=
    { toFun := fun q => isoPart V W C' q.1 + isoPart V W C q.2.1 + midPart V V' W B q.2.2
      invFun := fun w => (w * u, w * u', w * b)
      left_inv := by
        rintro ⟨t, y, x⟩
        simp only [fwd]
        rw [(back t y x).1, (back t y x).2.1, (back t y x).2.2]
      right_inv := by
        intro w
        simp only [fwd]
        calc w * u * a + w * u' * c + w * b * p = w * (u * a + (b * p + u' * c)) := by
              simp only [Matrix.mul_add, Matrix.mul_assoc]; abel
          _ = w := by rw [key, Matrix.mul_one]
      map_add' := by
        rintro ⟨t, y, x⟩ ⟨t', y', x'⟩
        simp only [fwd, Prod.mk_add_mk, Matrix.add_mul]
        abel
      continuous_toFun := by
        simp only [fwd]
        exact (((cont a).comp continuous_fst).add ((cont c).comp (continuous_fst.comp continuous_snd))).add
          ((cont p).comp (continuous_snd.comp continuous_snd))
      continuous_invFun := ((cont u).prodMk ((cont u').prodMk (cont b))) }
  refine ⟨e, fun t y x => rfl, fun t y x => ?_⟩
  change isoPart V W C' t + isoPart V W C y + midPart V V' W B x ∈ ratL W V ↔ _
  rw [fwd, hVr, hV'r]
  have hr : ∀ {k l : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E), X.map f ∈ GlobalTheory.MixModel.ratMx D k l :=
    fun X => GlobalTheory.MixModel.rat_mem X
  have hmul : ∀ {k l m : ℕ} {X : Mx D k l} {Y : Mx D l m},
      X ∈ GlobalTheory.MixModel.ratMx D k l → Y ∈ GlobalTheory.MixModel.ratMx D l m →
      X * Y ∈ GlobalTheory.MixModel.ratMx D k m := by
    intro k l m X Y hX hY
    obtain ⟨A, rfl⟩ := hX
    obtain ⟨B, rfl⟩ := hY
    change A.map f * B.map f ∈ GlobalTheory.MixModel.ratMx D k m
    rw [m1]
    exact hr (A * B)
  constructor
  · intro h
    obtain ⟨b1, b2, b3⟩ := back t y x
    refine ⟨?_, ?_, ?_⟩
    · rw [← b1]; exact hmul h (hr C)
    · rw [← b2]; exact hmul h (hr C')
    · rw [← b3]; exact hmul h (hr B)
  · rintro ⟨ht, hy, hx⟩
    exact add_mem (add_mem (hmul ht (hr _)) (hmul hy (hr _)))
      (hmul hx (hr _))

end GlobalTheory.TwistDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homSpace_dual_isotropic_middle_decomposition : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  first | exact @GlobalTheory.TwistDecomp.decomp_exists | exact GlobalTheory.TwistDecomp.decomp_exists | (intros; apply GlobalTheory.TwistDecomp.decomp_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScaling
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScaling
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviRes

variable {D : D7}

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat M) = GlobalTheory.MixModel.rat Mᴴ := by
  rw [← GlobalTheory.MixModel.cT_sig]
  ext i j
  simp [GlobalTheory.MixModel.adj, GlobalTheory.MixModel.rat, Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem symplOH_add_right (S T : HSp D) (x y z : WO S T) :
    symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add, map_add]

theorem symplOH_mul_rat (V W : HSp D) {s t : ℕ} (X : Matrix (Fin s) (Fin V.rank) D.host.E)
    (Y : Matrix (Fin t) (Fin V.rank) D.host.E) (hXY : X * V.gram⁻¹ * Yᴴ = 0) (q : Mx D W.rank s) (a : Mx D W.rank t) :
    symplOH V W (q * GlobalTheory.MixModel.rat X) (a * GlobalTheory.MixModel.rat Y) = 0 := by
  have hz : GlobalTheory.MixModel.rat X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Yᴴ = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hXY, GlobalTheory.MixModel.rat_zero]
  have hre : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj (a * GlobalTheory.MixModel.rat Y) * (GlobalTheory.MixModel.gA W * (q * GlobalTheory.MixModel.rat X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Yᴴ * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q)) * GlobalTheory.MixModel.rat X := by
    rw [GlobalTheory.MixModel.adj_mul, adj_rat]
    simp only [Matrix.mul_assoc]
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, hre, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero, map_zero]

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem iso_iso (hs : IsIsoSplit V V' C B) : (adj D C * V.gram) * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, h0]

theorem iso_mid (hs : IsIsoSplit V V' C B) :
    (adj D C * V.gram) * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * B = 0 := hs.orth
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

theorem periodic (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ y : Mx D W.rank r,
      f (isoPart V W C (γ + y) + midPart V V' W B x) = f (isoPart V W C y + midPart V V' W B x) := by
  intro γ hγ y
  obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
  have e1 : ∀ z : Mx D W.rank r, isoPart V W C z = z * GlobalTheory.MixModel.rat (adj D C * V.gram) := fun z => rfl
  have e2 : midPart V V' W B x = (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) := rfl
  have h0 : symplOH V W (GlobalTheory.MixModel.rat γ0 * GlobalTheory.MixModel.rat (adj D C * V.gram))
      (isoPart V W C y + midPart V V' W B x) = 0 := by
    rw [symplOH_add_right, e1, e2,
      symplOH_mul_rat V W (adj D C * V.gram) (adj D C * V.gram) (iso_iso hs) (GlobalTheory.MixModel.rat γ0) y,
      symplOH_mul_rat V W (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (iso_mid hs) (GlobalTheory.MixModel.rat γ0) x,
      add_zero]
  have hq : f (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram)) + (isoPart V W C y + midPart V V' W B x)) =
      ψ (-(symplOH V W (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram))) (isoPart V W C y + midPart V V' W B x))) *
        f (isoPart V W C y + midPart V V' W B x) :=
    hf.quasi (γ0 * (adj D C * V.gram)) (isoPart V W C y + midPart V V' W B x)
  rw [e1 (GlobalTheory.MixModel.rat γ0 + y), Matrix.add_mul, add_assoc, ← e1 y, ← GlobalTheory.MixModel.rat_mul, hq,
    GlobalTheory.MixModel.rat_mul, h0, neg_zero, AddChar.map_zero_eq_one, one_mul]

end Split

theorem mt_unitary (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.gA V := by
  rw [Matrix.mul_assoc]
  exact GlobalTheory.MixModel.mt_unitary V a

theorem mt_mul (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_mul_mt (S T : HSp D) (g : GA D S) (w : WO S T) :
    actO S T g 1 (HMul.hMul (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g)) = w := by
  rw [GlobalTheory.MixModel.actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.mul_one]

private lemma rat_adj_mul_gram_eq (V : HSp D) {s : ℕ} (B : Matrix (Fin V.rank) (Fin s) D.host.E) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) = GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) * GlobalTheory.MixModel.gA V := by
  rw [GlobalTheory.MixModel.rat_mul, adj_rat, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig, GlobalTheory.MixModel.gA]

private lemma gA_mul_mt_eq_adj_mt_inv_mul (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V := by
  calc GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a
      = (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V * Formalism.L2.Theta.mt V a⁻¹) * Formalism.L2.Theta.mt V a := by
        rw [mt_unitary]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V * (Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a) := by
        rw [Matrix.mul_assoc]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) * GlobalTheory.MixModel.gA V := by
        rw [← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem form_fix (V : HSp D) {s : ℕ} (a : GA D V) (B : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) * Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.rat (adj D B * V.gram) := by
  have hinv : Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv]

theorem form_scale (V : HSp D) {s : ℕ} (a : GA D V) (C : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C) :
    GlobalTheory.MixModel.rat (adj D C * V.gram) * Formalism.L2.Theta.mt V a =
      incA D (1 / 2) • GlobalTheory.MixModel.rat (adj D C * V.gram) := by
  have h2 : incA D (1 / 2) * (2 : AE D) = 1 := by
    rw [← map_ofNat (incA D) 2, ← map_mul]
    norm_num
  have hinv : Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
    calc Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C
        = (incA D (1 / 2) * (2 : AE D)) • (Formalism.L2.Theta.mt V a⁻¹ * GlobalTheory.MixModel.rat C) := by rw [h2, one_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ * ((2 : AE D) • GlobalTheory.MixModel.rat C)) := by
        rw [mul_smul, Matrix.mul_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ * (Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C)) := by rw [h]
      _ = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
        rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  have hc : cA D (incA D (1 / 2)) = incA D (1 / 2) := GlobalTheory.MixModel.cA_half
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv,
    GlobalTheory.MixModel.adj_smul, hc, Matrix.smul_mul]

theorem res_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ a : GA D V, a ∈ GQ V → HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ l : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (a, 1) f) = l • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hcov
  refine ⟨1, fun f hf => ?_⟩
  have hC' : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C := haC
  have hB' : Formalism.L2.Theta.mt V a * GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := haB
  have hsub : ∀ w : WO V W,
      ω (a, 1) f w = f (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a)) := by
    intro w
    have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω a haQ 1 (one_mem _) f hf
      (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a))
    rwa [actO_mul_mt] at h1
  have hiso : ∀ y : Mx D W.rank r,
      HMul.hMul (isoPart V W C y : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
        isoPart V W C (incA D (1 / 2) • y) := by
    intro y
    show y * GlobalTheory.MixModel.rat (adj D C * V.gram) * Formalism.L2.Theta.mt V a =
      (incA D (1 / 2) • y) * GlobalTheory.MixModel.rat (adj D C * V.gram)
    rw [Matrix.mul_assoc, form_scale V a C hC', Matrix.mul_smul, Matrix.smul_mul]
  rw [one_smul]
  funext x
  have hmid : HMul.hMul (midPart V V' W B x : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
      midPart V V' W B x := by
    show (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) * Formalism.L2.Theta.mt V a =
      (x : Mx D W.rank V'.rank) * GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram)
    rw [Matrix.mul_assoc V'.gram⁻¹ (adj D B) V.gram, GlobalTheory.MixModel.rat_mul]
    simp only [Matrix.mul_assoc]
    rw [form_fix V a B hB']
  calc res V V' W C B μ 𝓨 (ω (a, 1) f) x
      = ∫ y in 𝓨, f (isoPart V W C (incA D (1 / 2) • y) + midPart V V' W B x) ∂μ := by
        show ∫ y in 𝓨, ω (a, 1) f (isoPart V W C y + midPart V V' W B x) ∂μ = _
        congr 1
        funext y
        rw [hsub, Matrix.add_mul, hiso, hmid]
    _ = ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B x) ∂μ :=
        GlobalTheory.UnipMean.mean_smul hcov (c := 1 / 2) (by norm_num)
          (fun y => f (isoPart V W C y + midPart V V' W B x)) (periodic hs hf x)
    _ = res V V' W C B μ 𝓨 f x := rfl

end GlobalTheory.LeviRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScalingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestriction_invariant_rationalLeviScaling : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ a : GA D V, a ∈ GQ V → HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ l : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (a, 1) f) = l • res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.LeviRes.res_levi | exact GlobalTheory.LeviRes.res_levi | (intros; apply GlobalTheory.LeviRes.res_levi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceTensorLawBothOrdersOfCovers
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceTensorLawBothOrdersOfCovers
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.TensLawOf

section

variable {p q r s : ℕ}

theorem cJoint_swap {σ : Type} (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ)
    (Φ : MvPolynomial σ ℂ) (h : CJoint a₁ a₂ Λ₁ Λ₂ Φ) : CJoint a₂ a₁ Λ₂ Λ₁ Φ := by
  obtain ⟨⟨d, h0, h1, h2⟩, h3, h4⟩ := h
  exact ⟨⟨d, h0, h2, h1⟩, h4, h3⟩

theorem tIntw_swap {W : Type} [AddCommGroup W] [Module ℂ W] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ W)
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ W) (M₁ : GKMod p q) (M₂ : GKMod r s) (f : W →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V)
    (h : TIntw a₁ a₂ M₁ M₂ f) :
    TIntw a₂ a₁ M₂ M₁ ((TensorProduct.comm ℂ M₁.V M₂.V).toLinearMap ∘ₗ f) := by
  constructor
  · intro Y
    rw [LinearMap.comp_assoc, h.2 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp
  · intro Y
    rw [LinearMap.comp_assoc, h.1 Y, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    congr 1
    ext x y
    simp

theorem comm_comp_inj {W A B : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {f g : W →ₗ[ℂ] A ⊗[ℂ] B}
    (h : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f = (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ g) : f = g := by
  refine LinearMap.ext fun x => ?_
  exact (TensorProduct.comm ℂ A B).injective (LinearMap.congr_fun h x)

theorem range_swap {W A B C : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] (f : W →ₗ[ℂ] A ⊗[ℂ] B) (j : C →ₗ[ℂ] B)
    (h : LinearMap.range ((TensorProduct.comm ℂ A B).toLinearMap ∘ₗ f) =
      LinearMap.range (TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A))) :
    LinearMap.range f = LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j) := by
  have e : (TensorProduct.comm ℂ A B).toLinearMap ∘ₗ TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) j =
      TensorProduct.map j (LinearMap.id : A →ₗ[ℂ] A) ∘ₗ (TensorProduct.comm ℂ A C).toLinearMap := by
    ext x y
    simp
  apply Submodule.map_injective_of_injective (f := (TensorProduct.comm ℂ A B).toLinearMap)
    (TensorProduct.comm ℂ A B).injective
  rw [← LinearMap.range_comp, ← LinearMap.range_comp, h, e,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

end

theorem tensLaw_of : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), ARi X lam lam' → ARiiiUp X lam lam' → ARiiiDown X lam lam' → ARiiiLine X lam lam' → TensLaw (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) (X.ds r s lam') (blattner lam) (blattner lam') ∧ TensLaw (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam') (X.ds p q lam) (blattner lam') (blattner lam) := by
  intro X p q r s lam lam' h1 hU hD hL
  obtain ⟨hiff, hnorm, huniq⟩ := GlobalTheory.T.fockModel_jointHarmonics_form_normalisation_uniqueness X p q r s (blattner lam) (blattner lam')
  obtain ⟨Φ₀, hΦ₀⟩ := h1.1
  have hex : CJoint (fockAct1 p q r s) (fockAct2 p q r s) (blattner lam) (blattner lam') Φ₀ :=
    (hiff Φ₀).2 ⟨hΦ₀.1, hΦ₀.2.1, hΦ₀.2.2.1⟩
  refine ⟨⟨⟨Φ₀, hex⟩, huniq, ?_, hL⟩, ⟨⟨Φ₀, cJoint_swap _ _ _ _ _ hex⟩,
    fun Φ Φ' h h' => huniq Φ Φ' (cJoint_swap _ _ _ _ _ h) (cJoint_swap _ _ _ _ _ h'), ?_, ?_⟩⟩
  · intro MM f hf hf0
    obtain ⟨⟨N, -, e, he⟩, hΦ⟩ := hU MM f hf hf0
    refine ⟨⟨N, e, he⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ hJ
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, h0, smul_zero]), fun f' hf' h => g2 f' hf' ?_⟩
    rw [map_smul, map_smul, h]
  · intro MM f hf hf0
    have hf1 := tIntw_swap _ _ _ _ f hf
    obtain ⟨⟨N, -, e, he, hr⟩, hΦ⟩ := hD MM _ hf1
      (fun h => hf0 (comm_comp_inj (by rw [h, LinearMap.comp_zero])))
    refine ⟨⟨N, e, he, range_swap f _ hr⟩, fun Φ hJ => ?_⟩
    obtain ⟨c, -, hc⟩ := hnorm Φ (cJoint_swap _ _ _ _ _ hJ)
    obtain ⟨g1, g2⟩ := hΦ _ hc
    refine ⟨fun h0 => g1 (by rw [map_smul, LinearMap.comp_apply, h0, map_zero, smul_zero]), fun f' hf' h =>
      comm_comp_inj (g2 _ (tIntw_swap _ _ _ _ f' hf') ?_)⟩
    rw [map_smul, map_smul, LinearMap.comp_apply, LinearMap.comp_apply, h]
  · obtain ⟨f₀, hf₀, hne, hall⟩ := hL
    refine ⟨_, tIntw_swap _ _ _ _ f₀ hf₀,
      fun h => hne (comm_comp_inj (by rw [h, LinearMap.comp_zero])), fun f hf => ?_⟩
    obtain ⟨c, hc⟩ := hall _ (tIntw_swap _ _ _ _ f hf)
    refine ⟨c, comm_comp_inj ?_⟩
    rw [hc]
    refine LinearMap.ext fun x => ?_
    simp

end GlobalTheory.ArchRec.TensLawOf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceTensorLawBothOrdersOfCoversStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCorrespondenceTensorLaw_both_orders_of_covers : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), ARi X lam lam' → ARiiiUp X lam lam' → ARiiiDown X lam lam' → ARiiiLine X lam lam' → TensLaw (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) (X.ds r s lam') (blattner lam) (blattner lam') ∧ TensLaw (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam') (X.ds p q lam) (blattner lam') (blattner lam) := by
  first | exact @GlobalTheory.ArchRec.TensLawOf.tensLaw_of | exact GlobalTheory.ArchRec.TensLawOf.tensLaw_of | (intros; apply GlobalTheory.ArchRec.TensLawOf.tensLaw_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIsometryDiscreteSeriesModelDetCover
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIsometryDiscreteSeriesModelDetCover
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.KFiniteTie

open GlobalTheory.CoverModel GlobalTheory.Chain.RealIt.LocalFromCover
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (toFrame)

section Semi

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {cj : Bool} {U : H → H'}

theorem cjc_ofReal (cj : Bool) (r : ℝ) : cjc cj (r : ℂ) = r := by
  cases cj <;> simp [cjc]

theorem exists_real (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hb : Function.Bijective U) (hn : ∀ x, ‖U x‖ = ‖x‖) : ∃ L : H ≃ₗᵢ[ℝ] H', ∀ x, L x = U x := by
  let L₀ : H →ₗᵢ[ℝ] H' :=
    { toFun := U
      map_add' := hadd
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, hs, cjc_ofReal, Complex.coe_smul, RingHom.id_apply]
      norm_map' := hn }
  exact ⟨LinearIsometryEquiv.ofSurjective L₀ hb.2, fun _ => rfl⟩

theorem inner_map (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hn : ∀ x, ‖U x‖ = ‖x‖) (w x : H) : ⟪U w, U x⟫_ℂ = cjc cj ⟪w, x⟫_ℂ := by
  have hre : ∀ w x : H, (⟪U w, U x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := fun w x => by
    have h1 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) (U w) (U x)
    have h2 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) w x
    rw [← hadd, hn, hn, hn, ← h2] at h1
    exact h1
  have h1 := hre w x
  have h2 := hre w (Complex.I • x)
  rw [hs, inner_smul_right, inner_smul_right] at h2
  cases cj
  · apply Complex.ext <;> simp_all [cjc]
  · apply Complex.ext
    · simp only [cjc, if_true, Complex.conj_re]
      exact h1
    · simp only [cjc, if_true, Complex.conj_im] at h2 ⊢
      simpa using h2

end Semi

theorem isFormIso_phi {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) (br : Bool) :
    IsFormIso ε (phi br e) := by
  cases br
  · exact isFormIso_plainMat h
  · exact isFormIso_barMat h

theorem exists_kTie : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → (∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v)) → ∃ u, KTie R M τ lam c br cj e u := by
  intro D V S M τ p q T R lam c br cj e m U hpar hord hm hT hhi
  have hφ := isFormIso_phi hord.1 br
  obtain ⟨L, hL⟩ := exists_real hT.add hT.smul hT.bij hT.norm
  have hr : ∀ v : kfin M τ, ∃ y, R.ι y = U v := by
    rintro ⟨v, hv⟩
    change U v ∈ LinearMap.range R.ι
    induction hv using Submodule.span_induction with
    | mem x hx => exact (hT.kfin x).1 hx
    | zero => rw [← hL, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hT.add]; exact add_mem hx hy
    | smul z x _ hx => rw [hT.smul]; exact Submodule.smul_mem _ _ hx
  choose u hu using hr
  have hmC : (m : ℂ) = 2 * (c : ℂ) := by exact_mod_cast hm
  have hgrp : ∀ (g : T.G) (x : M.H τ), U (M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x) =
      ((T.sq g : ℂˣ) : ℂ) ^ m • R.U.π g (U x) := fun g x => by
    rw [hT.grp, smul_smul, ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]
  refine ⟨u, hpar, hord, fun x y => R.ι_inj ?_, fun z x => R.ι_inj ?_, ⟨fun x y h => ?_, fun y => ?_⟩, ?_,
    fun Z hZ v v' => ?_, fun v => hhi _ _ (hu v).symm, fun m' hm' g v w => ?_⟩
  · rw [map_add (f := _), hu, hu, hu, Submodule.coe_add, hT.add]
  · rw [map_smul, hu, hu, Submodule.coe_smul, hT.smul]
  · exact Subtype.ext (hT.bij.1 (by rw [← hu, ← hu, h]))
  · obtain ⟨x, hx⟩ := hT.bij.2 (R.ι y)
    exact ⟨⟨x, Submodule.subset_span ((hT.kfin x).2 ⟨y, hx.symm⟩)⟩, R.ι_inj (by rw [hu]; exact hx)⟩
  · change (fun Z => toFrame M τ (phi br e Z)) '' _ = _
    rw [← toFrame_image M τ, ← Set.image_image (toFrame M τ) (phi br e)]
    congr 1
    ext Y
    obtain ⟨Z, rfl⟩ := hφ.bij.2 Y
    rw [hφ.bij.1.mem_set_image, ← hφ.mem_lie]
    rfl
  · have h1 := (hasDerivAt_sq_zpow T m hZ).fun_smul (R.der Z hZ (u v))
    have h2 : HasDerivAt (fun t : ℝ => L (M.rep τ (NormedSpace.exp (t • phiFr (M.fr τ) br e Z)) (v : M.H τ)))
        (R.ι (R.HK.act Z (u v) + ((c : ℂ) * Z.trace) • u v)) 0 := by
      convert (preTransparency := .reducible) h1 using 1
      · funext t
        have h3 := rep_exp M τ (phi br e Z) t
        rw [hL, show phiFr (M.fr τ) br e Z = toFrame M τ (phi br e Z) from rfl, h3, hφ.exp,
          ← T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), hgrp, hu]
      · rw [hmC, show 2 * (c : ℂ) * (Z.trace / 2) = c * Z.trace by ring]
        simp [T.expt_zero]
    constructor
    · intro h
      have h3 := L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
      refine R.ι_inj ?_
      rw [hu, ← hL]
      exact h3.unique h2
    · intro h
      rw [← h, hu, ← hL] at h2
      have h3 := L.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      unfold VecDer
      convert h3 using 1
      · funext t; simp
      · simp
  · obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
    rw [← inner_map hT.add hT.smul hT.norm, hgrp, inner_smul_right, hu, hu]

end GlobalTheory.ArchRec.KFiniteTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIsometryDiscreteSeriesModelDetCoverStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kFiniteIsometry_discreteSeriesModel_detCover : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → (∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v)) → ∃ u, KTie R M τ lam c br cj e u := by
  first | exact @GlobalTheory.ArchRec.KFiniteTie.exists_kTie | exact GlobalTheory.ArchRec.KFiniteTie.exists_kTie | (intros; apply GlobalTheory.ArchRec.KFiniteTie.exists_kTie <;> assumption)
end
end
