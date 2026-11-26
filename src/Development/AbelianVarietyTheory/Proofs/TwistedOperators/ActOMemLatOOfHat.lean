module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StdHalfLat

variable {D : D7}

theorem idemSum_mul_eq_zero {P P' : Finset (Pl D.host.E)} {e e' : AE D} (he : IsIdemSum e P) (he' : IsIdemSum e' P')
    (hPP : ∀ w ∈ P, ∀ w' ∈ P', w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w') : e * (e' + cA D e') = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun w hw => ?_
  obtain ⟨h1, h2⟩ := hPP w hw w' hw'
  rw [mul_add, Formalism.IndefR.Fin.idem_orth (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h1,
    Formalism.IndefR.Fin.idem_orth_conj (Formalism.IndefR.Fin.idemAt_split (hes w hw)) (hes w hw) (hes' w' hw') h2, add_zero]

theorem ne_and_not_conj {S : Finset ℕ} {w w' : Pl D.host.E} (hw : ¬ Off S w) (hw' : Off S w') :
    w ≠ w' ∧ ¬ Formalism.IndefR.Lev.IsConjPl (D := D) w w' := by
  unfold Off at hw hw'
  push_neg at hw
  obtain ⟨q, hq, hqw⟩ := hw
  refine ⟨fun h => hw' q hq (h ▸ hqw), fun h => ?_⟩
  obtain ⟨c', hc', hc'eq⟩ := h _ hqw
  apply hw' q hq
  have : c' = (q : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    rw [hc'eq]
    simp
  rwa [this] at hc'

theorem actO_eq_self_of_half {S T : HSp D} {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0)
    {g : GA D S} {h : GA D T} (hg : SuppAt a S g) (hh : SuppAt b T h) {x : WO S T} (hx : IsHalf e x) :
    actO S T g h x = x := by
  have hx' : ∀ c : AE D, e * c = 0 → (1 - c) • x = x := fun c hc => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← hx i j, ← mul_assoc, sub_mul, one_mul, mul_comm c e, hc, sub_zero]
  unfold actO
  have k1 : HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    conv_lhs => rw [← hx' _ hb]
    rw [Matrix.mul_smul, ← Matrix.smul_mul, GlobalTheory.SplitScalar.off_smul_mt hh, Matrix.smul_mul, Matrix.one_mul, hx' _ hb]
  rw [k1]
  conv_lhs => rw [← hx' _ ha]
  rw [Matrix.smul_mul, ← Matrix.mul_smul, GlobalTheory.SplitScalar.off_smul_mt_inv hg, Matrix.mul_smul, Matrix.mul_one, hx' _ ha]

theorem suppAt_inv' {a : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt a V g) : SuppAt a V g⁻¹ := by
  have h := GlobalTheory.SplitScalar.off_smul_mt_inv hg
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, sub_eq_zero] at h
  exact fun i j => (congrFun (congrFun h i) j).symm

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem actO_mem_latO_of_hat {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    {u : WO S T} (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    actO S T g h u ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    exact GlobalTheory.AdelicLatMove.rankOne_mem_latO S T ΛS' ΛT' a ha _
      (hS _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛS 1 (one_mem _) s hs)) _
      (hT _ (GlobalTheory.AdelicLatMove.pure_mem_hatL ΛT α hα t ht))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem mem_latO_iff_of_half {S T : HSp D} (g : GA D S) (h : GA D T)
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT ΛT' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS,
      (mt S g).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS')
    (hS' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS',
      (mt S g⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS)
    (hT : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT,
      (mt T h).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT')
    (hT' : ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT',
      (mt T h⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT)
    {e a b : AE D} (ha : e * (a + cA D a) = 0) (hb : e * (b + cA D b) = 0) (hg : SuppAt a S g) (hh : SuppAt b T h)
    {x : WO S T} (hx : IsHalf e x) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      x ∈ latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  constructor
  · intro hm
    have := actO_mem_latO_of_hat g h hS hT hm
    rwa [actO_eq_self_of_half ha hb hg hh hx] at this
  · intro hm
    have := actO_mem_latO_of_hat g⁻¹ h⁻¹ hS' hT' hm
    rwa [actO_eq_self_of_half ha hb (suppAt_inv' hg) (suppAt_inv' hh) hx] at this

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.StdHalfLat

open Matrix

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hat_moves {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {X : Node} (hX : DefNode D.R.m X) :
    (∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)),
      (mt (G.V X) (N.u X).1).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X)) ∧
    ∀ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X),
      (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X)) := by
  refine ⟨fun v hv => (N.u_lat X hX v).1 hv, fun v hv => (N.u_lat X hX _).2 ?_⟩
  have e : (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1).1 *ᵥ ((mt (G.V X) (N.u X).1⁻¹).map (toEAf D) *ᵥ v) = v := by
    rw [show (mt (G.V X) (N.u X).1⁻¹).map (toEAf D) = (Formalism.IndefR.Lev.finE (G.V X) (N.u X).1⁻¹).1 from rfl,
      Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact hv

theorem exists_kill {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (N : Std G U)
    {t : T} (ht : t ∈ U) {p : Pair T} (d : FinDatum G t p) {X : Node} (hX : DefNode D.R.m X) :
    ∃ a : AE D, d.e * (a + cA D a) = 0 ∧ SuppAt a (G.V X) (N.u X).1 := by
  obtain ⟨P', e', he', hsupp, hoff⟩ := N.u_supp X hX
  refine ⟨e', idemSum_mul_eq_zero d.e_is he' fun w hw w' hw' => ne_and_not_conj ?_ (hoff w' hw'), hsupp⟩
  intro hw0
  have h3 := N.off w hw0
  rcases d.P_over w hw with h | ⟨w'', hw'', h⟩
  · exact h3.1 h
  · exact h3.2.1 t ht w'' hw'' h

end GlobalTheory.StdHalfLat

namespace GlobalTheory.LastVertexMove

open GlobalTheory.StdHalfLat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem isSBHalf_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {p : Pair T}, DefPair D.R.m p → ∀ d : FinDatum G t p,
    d.P = locPl G t → IsSBHalf d.e (stdLat S p) d.fn := by
  intro D T L sc G W U S t ht p hp d _
  have key : ∀ x, IsHalf d.e x →
      (x ∈ latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) (fun _ => True) ↔ x ∈ stdLat S p) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hp.nodes
    rcases p with ⟨i, j⟩ | ⟨t', i, j⟩ | i | ⟨t', j⟩
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h2
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h1
      have m2 := hat_moves S.N h2
      have m1 := hat_moves S.N h1
      exact (mem_latO_iff_of_half (negGA _ (S.N.u (.grid (i + 1) j)).1) (S.N.u (.grid i j)).1
        m2.1 (fun v hv => by rw [← map_inv]; exact m2.2 v hv) m1.1 m1.2 ha hb hga hgb hx).symm
    · exact hp.elim
    · exact hp.elim
    · obtain ⟨a, ha, hga⟩ := exists_kill S.N ht d h1
      obtain ⟨b, hb, hgb⟩ := exists_kill S.N ht d h2
      have m1 := hat_moves S.N h1
      have m2 := hat_moves S.N h2
      exact (mem_latO_iff_of_half (S.N.u (.top j)).1 (S.N.u (.top (j + 1))).1
        m1.1 m1.2 m2.1 m2.2 ha hb hga hgb hx).symm
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := d.sb
  refine ⟨hsupp, k, hk, fun u hu hub y => hinv u ((key u hub).2 hu) hub y, fun y hy => ?_⟩
  exact (key _ (half_nsmul (hsupp y hy) k)).1 (hfin y hy)

end GlobalTheory.LastVertexMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLift
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_inFin (v : Pl (F := F)) (a : Fv F v) : At (evFin F v) (inFin v a) := by
  intro u hu
  have h := GlobalTheory.InertDetChr.at_inFin_one (F := F) v u hu
  rw [smul_eq_mul] at h ⊢
  rw [show a = 1 * a from (one_mul a).symm, inFin_mul, ← mul_assoc, h, zero_mul]

theorem compFin_smul_inclR (v : Pl (F := F)) (a : AF F) (y : E) :
    compFin F E v (a • inclR (F := F) (AF F) y) = evFin F v a ⊗ₜ[F] y := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.InertDetChr.compFin_algebraMap]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this]
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem comp_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : compFin F E v ∘ z ∈ latLoc F W.L v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    convert tmul_mem_latLoc ha hy using 1
    funext i
    exact compFin_smul_inclR v a (y i)
  | zero =>
    convert zero_mem (latLoc F W.L v) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

theorem mulVec_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (g : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ y ∈ latLoc F W.L v, (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v := by
  intro y hy
  refine latLoc_induction (p := fun y => (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v)
    (fun a ha x hx => ?_) (by rw [Matrix.mulVec_zero]; exact zero_mem _)
    (fun _ _ h h' => by rw [Matrix.mulVec_add]; exact add_mem h h')
    (fun _ h => by rw [Matrix.mulVec_neg]; exact neg_mem h) hy
  have hz : (inFin v a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt W v :=
    AddSubgroup.subset_closure ⟨inFin v a, at_inFin v a, by rwa [GlobalTheory.InertDetChr.evFin_inFin_self], x, hx, rfl⟩
  have e1 : (fun i => a ⊗ₜ[F] x i) = compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i)) := by
    funext i
    show _ = compFin F E v (inFin v a • inclR (F := F) (AF F) (x i))
    rw [compFin_smul_inclR, GlobalTheory.InertDetChr.evFin_inFin_self]
  rw [e1]
  have e2 : (compFin F E v).mapMatrix g *ᵥ (compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) =
      compFin F E v ∘ (g *ᵥ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) :=
    funext fun i => (RingHom.map_mulVec (compFin F E v) g _ i).symm
  rw [e2]
  exact comp_mem_latLoc W v (hg _ hz)

theorem det_mem_intLoc {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl (F := F)} (P : GL (Fin d) (Fv F v ⊗[F] E))
    (hP : ∀ y : Fin d → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ P.1 *ᵥ y ∈ latLoc F L v)
    (g : GL (Fin d) (Fv F v ⊗[F] E)) (hg : ∀ y ∈ latLoc F L v, g.1 *ᵥ y ∈ latLoc F L v) :
    ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  set Q : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E) := (P⁻¹ * g * P).1 with hQ
  have hent : ∀ i j, Q i j ∈ intLoc F E v := by
    intro i j
    have h1 : P.1 *ᵥ (Pi.single j 1) ∈ latLoc F L v := (hP _).1 (fun k => by
      by_cases e : k = j
      · subst e; simp
      · simp [e])
    have h2 := (hP (Q *ᵥ Pi.single j 1)).2 (by
      rw [hQ, Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul,
        ← Matrix.mulVec_mulVec]
      exact hg _ h1)
    have := h2 i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  let Q' : Matrix (Fin d) (Fin d) (intLoc F E v) := fun i j => ⟨Q i j, hent i j⟩
  have hQ' : (intLoc F E v).subtype.mapMatrix Q' = Q := rfl
  have hdet : Q.det = ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    rw [hQ, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      mul_comm _ (Matrix.GeneralLinearGroup.det P), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hdet, ← hQ', ← RingHom.map_det]
  exact (Matrix.det Q').2

end GlobalTheory.SplitDetChr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormula
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.HeisDerivArch

open GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

theorem actsD_heisLine_heisD {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f
      (heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2 f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  intro r hr x
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, GlobalTheory.HeisDeriv.evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add (f := _),
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, GlobalTheory.HeisDeriv.evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

theorem at_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (liftV (F := F) y) := by
  intro a ha
  funext i
  refine Prod.ext ?_ ?_
  · have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
    show a.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = 0
    rw [h1, zero_mul]
  · show a.2 * 0 = 0
    exact mul_zero _

end GlobalTheory.HeisDerivArch


open GlobalTheory.HeisDeriv GlobalTheory.HeisDerivArch in
theorem GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
    ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ ∀ f g : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) ⇑f ⇑g → ∀ y, g y =
        fderiv ℝ (⇑f) y v.1 - 2 * Real.pi * Complex.I * (trP F (Fin n × Fin d) y v.2 : ℂ) * f y := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ v
  set u := M.co.e.symm (liftV v.1, liftV v.2) with hu
  have heu : M.co.e u = (liftV v.1, liftV v.2) := by rw [hu, LinearEquiv.apply_symm_apply]
  refine ⟨u, ?_, ?_⟩
  · intro a ha
    have e1 : a • u = M.co.e.symm (a • (liftV v.1, liftV v.2)) := by rw [hu, map_smul]
    rw [e1, Prod.smul_mk, at_liftV v.1 a ha, at_liftV v.2 a ha, Prod.mk_zero_zero, map_zero]
  · intro f g hg y
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
    have hr := hR f
    set x : Fin n × Fin d → AF F := liftV y with hx
    have hd1 := hg R hr x
    have hd2 := actsD_heisLine_heisD M ψ hψ u f R hr x
    have huniq := hd1.unique hd2
    have hRx : R x = R 0 := by
      have := hr.1 0 x (at_liftV y)
      rwa [zero_add] at this
    have hlx : (fun i => evI F (x i)) = y := Coord.loc_lift y
    simp only [tens, hlx, hRx] at huniq
    have huniq' := mul_right_cancel₀ hR0 huniq
    rw [huniq', heisD_apply, mult_apply, heu]
    have hv1 : (fun i => evI F ((liftV (F := F) v.1) i)) = v.1 := Coord.loc_lift v.1
    simp only [hv1, trForm_apply]
    have hv2 : ∀ i, evI F ((liftV (F := F) v.2) i) = v.2 i := fun i => congrFun (Coord.loc_lift v.2) i
    simp only [hv2, trP]
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormulaStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergLine_derivative_formula : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
    ∃ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u ∧ ∀ f g : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) ⇑f ⇑g → ∀ y, g y =
        fderiv ℝ (⇑f) y v.1 - 2 * Real.pi * Complex.I * (trP F (Fin n × Fin d) y v.2 : ℂ) * f y := by
  first | exact @GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq | exact GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq | (intros; apply GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorSymplecticFormAtSplitFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairChangeBasis
namespace GlobalTheory.TracePairingBasisChange

open Matrix

theorem pair_eq_trace {K : Type} [Field K] {n d : ℕ} (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = Matrix.trace (Xᵀ * Y) := by
  unfold GlobalTheory.FlipMatch.pairM
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem pair_change_basis {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin d) (Fin d) K) (b : GL (Fin n) K) (c : GL (Fin d) K)
    (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM
                 ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
                 (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B *
                   (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  rw [pair_eq_trace, Matrix.mul_neg, Matrix.trace_neg, neg_inj]
  have hb : Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K) * Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have key : Matrix.transpose ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K)) *
      (Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K)) =
      (↑c⁻¹ : Matrix (Fin d) (Fin d) K) * ((Matrix.transpose P * (A * (Q * Matrix.transpose B))) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K)), hb, Matrix.one_mul]
  rw [key, Matrix.trace_mul_comm, Matrix.mul_assoc, hc, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TracePairingBasisChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumFourSwap
namespace GlobalTheory.SumFourSwap

theorem sum_four_swap {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : α, ∑ c : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end GlobalTheory.SumFourSwap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorSymplecticFormAtSplitFinitePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch.SplitSymp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA' {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem piW_incl {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (e : E) :
    piW τ (inclR (F := F) (AF F) e) = τ e := by
  change GlobalTheory.AdelicU.evFin F v 1 * τ e = τ e
  simp

end GlobalTheory.FlipMatch.SplitSymp

namespace GlobalTheory.FlipMatch.SplitSymp

theorem pairM_comm {K : Type} [CommRing K] {n d : ℕ} (P Q : Matrix (Fin n) (Fin d) K) :
    pairM P Q = pairM Q P := by
  simp only [pairM, mul_comm]

theorem pairM_chart {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    pairM ((b⁻¹).1 * P * (c⁻¹).1ᵀ) (-(b.1ᵀ * A * Q * Bᵀ * c.1)) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  first
  | exact @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis
  | (apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePairingBasisChange.pair_change_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePairingBasisChange.pair_change_basis ..)

theorem sum_four_swap_pairs_alt {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ a, ∑ b, f a b c e := by
  first
  | exact @_root_.GlobalTheory.SumFourSwap.sum_four_swap
  | exact _root_.GlobalTheory.SumFourSwap.sum_four_swap
  | (apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumFourSwap.sum_four_swap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumFourSwap.sum_four_swap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumFourSwap.sum_four_swap ..)

theorem symp_at_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → ∀ (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) x → At (evFin F v) u →
    ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u) - pairM (coY σ X Y t b c x) (coX t b c u)) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hX hY ψ v t b c x u hx hu
  have hss := GlobalTheory.AdelicU.comp_conj_conj hcm t
  have hz : At (evFin F v) ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) *
      GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) := by
    intro r hr
    have h : ∀ i j, r • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx r hr) i) j
      simpa using this
    rw [← mul_smul_comm]
    unfold GlobalTheory.WeilM.hTens
    simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]
  unfold GlobalTheory.WeilM.symp
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hz]
  change psiLoc ψ v _ = psiLoc ψ v _
  congr 1
  rw [pairM_comm (coY σ X Y t b c x), coX, coX, coY, coY, pairM_chart, pairM_chart]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_neg, map_one, neg_one_mul, GlobalTheory.WeilM.hTens, map_sum, piW_cA', piW_incl,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hss, AlgHom.comp_apply, hX, hY]
  rw [sub_eq_add_neg]
  congr 1
  rw [neg_neg]
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.FlipMatch.SplitSymp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorSymplecticFormAtSplitFinitePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorSymplecticForm_at_split_finite_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), (∀ r s, σ (X.J s r) = X.J r s) → (∀ r s, σ (Y.J s r) = -Y.J r s) → ∀ (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    At (evFin F v) x → At (evFin F v) u →
    ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x u) =
      psiLoc ψ v (pairM (coX t b c x) (coY σ X Y t b c u) - pairM (coY σ X Y t b c x) (coX t b c u)) := by
  first | exact @GlobalTheory.FlipMatch.SplitSymp.symp_at_split | exact GlobalTheory.FlipMatch.SplitSymp.symp_at_split | (intros; apply GlobalTheory.FlipMatch.SplitSymp.symp_at_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVac
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.FockOff

theorem latO_le {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {p q : HeightOneSpectrum (𝓞 D.host.F) → Prop} (h : ∀ v, p v → q v) : latO S T LS LT p ≤ latO S T LS LT q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

end GlobalTheory.EvenOnto.FockOff


open GlobalTheory.EvenOnto.FockOff in
theorem GlobalTheory.EvenOnto.fock_sph_vac : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D c hc k hk s s' hs hs' p hp φ
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hv := hp.pre.vac
  have hF : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) :=
    GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ
  have hpt : ∀ φ', IsThetaFunO c.ψ s.V s'.V (p.pt φ') := fun φ' =>
    (GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hv.theta hv.vac φ').1
  have hle : latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S) ≤ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      fun _ => True := latO_le _ _ _ _ fun _ _ => trivial
  have fix : ∀ u ∈ latO s.V s'.V (s.Λ : Set (Fin s.V.rank → D.host.E)) (s'.Λ : Set (Fin s'.V.rank → D.host.E))
      (fun v => v ∉ c.S), heisO c.ψ s.V s'.V u p.f = p.f → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hθ _ _ _ _ p.f hpt u
      (GlobalTheory.VacGood.infPart_latO (hle hu)) h0 φ
  have hsph := hp.pre.sph
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) :=
    ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hsph.1 u hu),
      fun e he u hu hh => fix u hu (hsph.2 e he u hu hh)⟩
  refine ⟨hF.1, hF, hS, fun v hv => ⟨hF.1, ?_, ?_⟩⟩
  · intro u hu
    exact hS.1 u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu)
  · intro e he u hu hh
    exact hS.2 e he u (latO_le _ _ _ _ (fun w hw => hw ▸ hv) hu) hh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ) := by
  first | exact @GlobalTheory.EvenOnto.fock_sph_vac | exact GlobalTheory.EvenOnto.fock_sph_vac | (intros; apply GlobalTheory.EvenOnto.fock_sph_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaHeisCLM

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

theorem exists_schr_pureA_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g' ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F (T f) g' := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  refine ⟨(SchwartzMap.smulLeftCLM ℂ (fun y => eChar ((-trL c) y + -k))).comp (SchwartzMap.compSubConstCLM ℂ (-t)),
    finS ψ g d s (p2 h), finS_mem ψ hψ.1 hg d s (p2 h), fun f => funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (GlobalTheory.HeisSchA.mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add (f := _), RingHom.map_dotProduct]
        rfl
      rw [e1, map_add (f := _), eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add (f := _), RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem exists_clm_thetaSum_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g) = L f := by
  obtain ⟨l, hl, hl'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F κ
  obtain ⟨L, hL⟩ := hl g hg
  exact ⟨L, fun f => (hl' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hL f)⟩

theorem exists_clm_thetaSum_rho_pure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ Λ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f,
      GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = Λ f := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ hG u φ hSB hvac
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hG.std).mono fun v h => h.1.trans h.2
  have hg : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈ GlobalTheory.WeilM.SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  obtain ⟨T, g', hg', hT⟩ := exists_schr_pureA_eq ψ hψ (M.co.e u) hg
  obtain ⟨L, hL⟩ := exists_clm_thetaSum_pureA hg'
  refine ⟨L.comp T, fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← hL, ← hT]
  rfl

end GlobalTheory.ThetaHeisCLM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

open Matrix

theorem mulVec_conj_mulVec_eq {n : ℕ} {R : Type} [CommRing R] (a g : GL (Fin n) R) (v : Fin n → R) :
    (a : Matrix (Fin n) (Fin n) R) *ᵥ (((a⁻¹ * g * a : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) R) *ᵥ ((a : Matrix (Fin n) (Fin n) R) *ᵥ v) := by
  simp only [Matrix.mulVec_mulVec, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]


set_option maxHeartbeats 1000000 in
theorem moved_keeps_std : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  intro D T L sc G W U S t j hj k hk v
  have hD : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨hj.le, rfl⟩
  have hmax : finG (G.V (.grid (j + 1) D.R.m)) k ∈ G.levMax (.grid (j + 1) D.R.m) := by
    rw [← GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA W S t j hj.le]
    exact Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  rw [GridData.levMax, congLev_top] at hmax
  have hst := (Subgroup.mem_inf.1 hmax).2
  have e : Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1)⁻¹ * finG (G.V (.grid (j + 1) D.R.m)) k * Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (S.N.u (.grid (j + 1) D.R.m)).1 := by
    rw [moved]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  rw [S.N.u_lat _ hD v, S.N.u_lat _ hD, e, mulVec_conj_mulVec_eq]
  exact hst _

end GlobalTheory.RowVertexInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedLevelElementKeepsStandardLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedLevelElement_keeps_standardLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ v : Fin (G.V (.grid (j + 1) D.R.m)).rank → Formalism.IndefR.Lev.EAf D, (v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m))) ↔ Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V (.grid (j + 1) D.R.m)) (moved S j k)).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.grid (j + 1) D.R.m)))) := by
  first | exact @GlobalTheory.RowVertexInv.moved_keeps_std | exact GlobalTheory.RowVertexInv.moved_keeps_std | (intros; apply GlobalTheory.RowVertexInv.moved_keeps_std <;> assumption)
end
end
