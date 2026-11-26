module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGoodEv

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIdemEx

variable {D : D7}

theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := _root_.PositivityTheory.Rg.Rsw.L.LGoodEv.ae_ext z z' hi hf


open Classical in
def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

theorem compInf_cA (w : InfinitePlace D.host.F) (z : AE D) :
    compInf D.host.F D.host.E w (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F w.Completion) D.sp.cm.sig).toRingHom (compInf D.host.F D.host.E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]
  | tmul a x => rfl

theorem cv_cA (v : Pl D) (z : AE D) :
    cv D v (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).toRingHom (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]
  | tmul a x => rfl

theorem idem_props (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) : e * e = e ∧ cA D e = e := by
  classical
  refine ⟨ae_ext _ _ (fun w => ?_) (fun v => ?_), ae_ext _ _ (fun w => ?_) (fun v => ?_)⟩
  · rw [map_mul, he.1 w, one_mul]
  · rw [map_mul, he.2 v]
    split_ifs <;> simp
  · rw [compInf_cA, he.1 w, RingHom.map_one]
  · rw [cv_cA, he.2 v]
    split_ifs <;> simp

end PositivityTheory.Rg.Rsw.L.LIdemEx

namespace PositivityTheory.Rg.Rsw.L

theorem idemEx : IdemEx := fun _ S =>
  ⟨⟨_, LIdemEx.isIdem_eS S⟩, fun e he => LIdemEx.idem_props S e he⟩

end PositivityTheory.Rg.Rsw.L

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWB
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct
open IsDedekindDomain NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]


variable (F E) in
abbrev bE : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E

abbrev bV (v : HeightOneSpectrum (𝓞 F)) : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (bE F E)

theorem bV_apply (v : HeightOneSpectrum (𝓞 F)) (k : Fin (Module.finrank F E)) : bV (E := E) v k = 1 ⊗ₜ[F] bE F E k :=
  Algebra.TensorProduct.basis_apply _ _

theorem crd_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) (k : Fin (Module.finrank F E)) :
    (bV v).repr (a ⊗ₜ[F] e) k = a * algebraMap F (Fv F v) ((bE F E).repr e k) := by
  simp [bV, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem exists_den (x : E) : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, by rwa [zsmul_eq_mul] at hi⟩

def den (x : E) : ℤ := Classical.choose (exists_den x)

theorem den_ne (x : E) : den x ≠ 0 := (Classical.choose_spec (exists_den x)).1

theorem den_int (x : E) : IsIntegral ℤ ((den x : E) * x) := (Classical.choose_spec (exists_den x)).2


variable (F E) in
def trM : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F := fun i j => Algebra.trace F E (bE F E i * bE F E j)

theorem trM_det : (trM F E).det ≠ 0 := by
  have h := Algebra.discr_not_zero_of_basis F (bE F E)
  rw [Algebra.discr_def] at h
  convert h using 2
  ext i j
  simp [trM, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

def IsGood (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (∀ (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)),
      algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F) ∧
    (∀ k, algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F) ∧
    algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F

theorem eventually_int (x : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2

theorem eventually_good : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IsGood F E v :=
  (eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_all.2 fun _ => eventually_int _).and
    ((eventually_all.2 fun _ => eventually_int _).and (eventually_int _))))

theorem eventually_coord (y : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
    ∀ k, algebraMap F (Fv F v) ((bE F E).repr y k) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun _ => eventually_int _

variable {v : HeightOneSpectrum (𝓞 F)}

theorem IsGood.half (hv : IsGood F E v) : algebraMap F (Fv F v) (2 : F)⁻¹ ∈ v.adicCompletionIntegers F := hv.2.2.2.2

theorem IsGood.ogen (hv : IsGood F E v) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((bE F E).repr ((RingOfIntegers.basis E l : 𝓞 E) : E) k) ∈ v.adicCompletionIntegers F :=
  hv.1 l k

theorem IsGood.deninv (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ∈ v.adicCompletionIntegers F := hv.2.1 k

theorem IsGood.trinv (hv : IsGood F E v) (i j : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) ((trM F E)⁻¹ i j) ∈ v.adicCompletionIntegers F := hv.2.2.1 i j

theorem IsGood.trb (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) ∈ v.adicCompletionIntegers F := hv.2.2.2.1 k

theorem one_tmul_b_mem (hv : IsGood F E v) (k : Fin (Module.finrank F E)) :
    (1 : Fv F v) ⊗ₜ[F] bE F E k ∈ intLoc F E v := by
  have hN : (den (bE F E k) : F) ≠ 0 := by exact_mod_cast den_ne (bE F E k)
  let o : 𝓞 E := ⟨(den (bE F E k) : E) * bE F E k, den_int (bE F E k)⟩
  have ho : (o : E) = (den (bE F E k) : E) * bE F E k := rfl
  have e : (1 : Fv F v) ⊗ₜ[F] bE F E k = algebraMap F (Fv F v) ((den (bE F E k) : F))⁻¹ ⊗ₜ[F] (o : E) := by
    rw [ho]
    have : ((den (bE F E k) : E) * bE F E k) = (den (bE F E k) : F) • bE F E k := by
      rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hN,
      map_one]
  rw [e]
  exact tmul_mem_intLoc (hv.deninv k) o

theorem tmul_one_mem {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) ha (1 : 𝓞 E)

theorem mem_intLoc_iff (hv : IsGood F E v) (z : Fv F v ⊗[F] E) :
    z ∈ intLoc F E v ↔ ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F := by
  constructor
  · intro hz
    refine intLoc_induction (p := fun z => ∀ k, (bV v).repr z k ∈ v.adicCompletionIntegers F) (fun a ha x k => ?_)
      (fun k => by simp) (fun y z hy hz k => by rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy k) (hz k))
      (fun y hy k => by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy k)) hz
    rw [crd_tmul]
    refine mul_mem ha ?_
    let L : 𝓞 E →+ F := ((Finsupp.applyAddHom k).comp (bE F E).repr.toLinearMap.toAddMonoidHom).comp
      (algebraMap (𝓞 E) E).toAddMonoidHom
    have e : L x = ∑ l, ((RingOfIntegers.basis E).repr x l) • L (RingOfIntegers.basis E l) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_zsmul]
    change algebraMap F (Fv F v) (L x) ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine sum_mem fun l _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (hv.ogen l k) _
  · intro h
    rw [← (bV v).sum_repr z]
    refine sum_mem fun k _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have e : (bV v).repr z k ⊗ₜ[F] bE F E k = ((bV v).repr z k ⊗ₜ[F] (1 : E)) * ((1 : Fv F v) ⊗ₜ[F] bE F E k) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact mul_mem (tmul_one_mem (h k)) (one_tmul_b_mem hv k)

theorem trace_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F (Fv F v) (Algebra.trace F E e) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace (bV v), Algebra.trace_eq_matrix_trace (bE F E), Matrix.trace, Matrix.trace,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    bV_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, crd_tmul]

theorem trace_eq_sum (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z =
      ∑ k, (bV v).repr z k * algebraMap F (Fv F v) (Algebra.trace F E (bE F E k)) := by
  conv_lhs => rw [← (bV v).sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, trace_tmul]

theorem trace_mem (hv : IsGood F E v) {z : Fv F v ⊗[F] E} (hz : z ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
  rw [trace_eq_sum]
  exact sum_mem fun k _ => mul_mem (((mem_intLoc_iff hv z).1 hz) k) (hv.trb k)

theorem mem_of_trace (hv : IsGood F E v) (c : Fv F v ⊗[F] E)
    (h : ∀ t ∈ intLoc F E v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * t) ∈ v.adicCompletionIntegers F) :
    c ∈ intLoc F E v := by
  classical
  set u : Fin (Module.finrank F E) → Fv F v := fun j => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (1 ⊗ₜ[F] bE F E j))
  have hu : ∀ j, u j ∈ v.adicCompletionIntegers F := fun j => h _ (one_tmul_b_mem hv j)
  have hu' : ∀ j, u j = ∑ l, (bV v).repr c l * algebraMap F (Fv F v) (trM F E l j) := by
    intro j
    simp only [u]
    conv_lhs => rw [← (bV v).sum_repr c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [bV_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      trace_tmul]
    rfl
  have hT : trM F E * (trM F E)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 trM_det)
  refine (mem_intLoc_iff hv c).2 fun k => ?_
  have e : (bV v).repr c k = ∑ j, u j * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) := by
    have h1 : ∀ l, ∑ j, algebraMap F (Fv F v) (trM F E l j) * algebraMap F (Fv F v) ((trM F E)⁻¹ j k) =
        if l = k then 1 else 0 := by
      intro l
      have := congrFun (congrFun hT l) k
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [← map_mul, ← map_sum, this]
      split_ifs <;> simp
    simp_rw [hu', Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, h1]
    simp
  rw [e]
  exact sum_mem fun j _ => mul_mem (hu j) (hv.trinv j k)

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FromColsSmulApply
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMuId

variable {D : D7} {a b r t n : ℕ}

scoped instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩
scoped instance scMx (m n : ℕ) : SecondCountableTopology (Mx D m n) := (GlobalTheory.MixModel.lattice_Mx D m n).2.2.1

theorem fromCols_smul_apply (e : AE D) (x : Mx D a r) (v : Mx D a t) (i : Fin a) :
    ∀ k, Matrix.fromCols (e • x) (e • v) i k = e • Matrix.fromCols x v i k := by
  rintro (k | k) <;> rfl

theorem jn_smul (hn : r + t = n) (e : AE D) (x : Mx D a r) (v : Mx D a t) : jn hn (e • x) (e • v) = e • jn hn x v := by
  ext i j
  exact fromCols_smul_apply e x v i _

theorem jn_inl (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (k : Fin r) :
    jn hn x v i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl k)) = x i k := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromCols_apply_inl]

theorem jn_inr (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (k : Fin t) :
    jn hn x v i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr k)) = v i k := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromCols_apply_inr]

theorem intOff_jn (S : Finset (Pl D)) (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) :
    IntOff S (jn hn x v) ↔ IntOff S x ∧ IntOff S v := by
  constructor
  · intro h
    refine ⟨fun w hw i k => ?_, fun w hw i k => ?_⟩
    · simpa only [jn_inl] using h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl k))
    · simpa only [jn_inr] using h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr k))
  · rintro ⟨hx, hv⟩ w hw i j
    obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
    rcases k with k | k
    · rw [jn_inl]; exact hx w hw i k
    · rw [jn_inr]; exact hv w hw i k

theorem good_pos {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (h : Good S e Φ) {x : Mx D a b} (hx : IntOff S x) :
    Φ x = Φ (e • x) := by
  rw [h x, if_pos hx]

theorem good_neg {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (h : Good S e Φ) {x : Mx D a b} (hx : ¬ IntOff S x) :
    Φ x = 0 := by
  rw [h x, if_neg hx]

theorem continuous_jn (hn : r + t = n) : Continuous fun z : Mx D a r × Mx D a t => jn hn z.1 z.2 := by
  have h : Continuous fun z : Mx D a r × Mx D a t => Matrix.fromCols z.1 z.2 := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    rcases k with k | k
    · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
    · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_snd)
  exact h.matrix_submatrix _ _

theorem continuous_yv (V : HSp D) (b₀ : HermE D r) : Continuous fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z :=
  continuous_const.matrix_mul ((continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd))

theorem measurable_sm (e : AE D) : Measurable fun z : Mx D a r × Mx D a t => (e • z.1, e • z.2) :=
  ((continuous_const_smul e).measurable.comp measurable_fst).prodMk ((continuous_const_smul e).measurable.comp measurable_snd)

theorem map_ne_zero (ν : Measure (Mx D a r × Mx D a t)) (s : Set (Mx D a r × Mx D a t)) (e : AE D) (hs : ν s ≠ 0) :
    (ν.restrict s).map (fun z => (e • z.1, e • z.2)) ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure _ => μ Set.univ) h
  simp only [Measure.map_apply (measurable_sm e) MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ,
    Measure.coe_zero, Pi.zero_apply] at this
  exact hs this

theorem transfer (hn : r + t = n) {V : HSp D} {b₀ : HermE D r} {S : Finset (Pl D)} {e : AE D}
    (ν : Measure (Mx D V.rank r × Mx D V.rank t))
    (hyv : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 →
      IntOff S (yv V b₀ z) ∧ yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z)
    (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ) (hΦc : Continuous Φ) (hηc : Continuous η) (hΦ : Good S e Φ)
    (hη : Good S e η) :
    ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) ∂((ν.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map
      fun z => (e • z.1, e • z.2)) = ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) ∂ν := by
  set F : Mx D V.rank r × Mx D V.rank t → ℂ := fun z => Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) with hF
  set s : Set (Mx D V.rank r × Mx D V.rank t) := {z | IntOff S z.1 ∧ IntOff S z.2} with hs
  have hFc : Continuous F := (hΦc.comp (continuous_jn hn)).mul (Complex.continuous_conj.comp (hηc.comp (continuous_yv V b₀)))
  have hfc : Continuous fun z : Mx D V.rank r × Mx D V.rank t => (e • z.1, e • z.2) :=
    ((continuous_const_smul e).comp continuous_fst).prodMk ((continuous_const_smul e).comp continuous_snd)
  have key : ∀ z ∈ s, F (e • z.1, e • z.2) = F z := by
    rintro z ⟨h1, h2⟩
    obtain ⟨hy, hye⟩ := hyv z h1 h2
    have hj : IntOff S (jn hn z.1 z.2) := (intOff_jn S hn z.1 z.2).2 ⟨h1, h2⟩
    simp only [hF, hye, jn_smul]
    rw [← good_pos hΦ hj, ← good_pos hη hy]
  have off : ∀ z ∉ s, F z = 0 := by
    intro z hz
    have hj : ¬ IntOff S (jn hn z.1 z.2) := fun h => hz ((intOff_jn S hn z.1 z.2).1 h)
    simp only [hF, good_neg hΦ hj, zero_mul]
  rw [integral_map (measurable_sm e).aemeasurable hFc.aestronglyMeasurable]
  have hae : ∀ᵐ z ∂(ν.restrict s), F (e • z.1, e • z.2) = F z := by
    have hm : MeasurableSet {a : Mx D V.rank r × Mx D V.rank t | ¬F (e • a.1, e • a.2) = F a} :=
      (isOpen_ne_fun (hFc.comp hfc) hFc).measurableSet
    rw [ae_iff, Measure.restrict_apply hm]
    convert measure_empty (μ := ν)
    exact Set.eq_empty_iff_forall_notMem.2 fun z hz => hz.1 (key z hz.2)
  rw [integral_congr_ae hae, setIntegral_eq_integral_of_forall_compl_eq_zero off]

theorem orb_null {V : HSp D} {b₀ : HermE D r} {e : AE D} {ν : Measure (Mx D V.rank r × Mx D V.rank t)}
    (hν : IsOrb V b₀ e ν) (hfree : ν {z | ¬ Free e z} = 0)
    (hno : ∀ z : Mx D V.rank r × Mx D V.rank t, Free e z →
      ¬ (ip V z.1 z.1 = e • rat b₀.1 ∧ e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ qv V b₀ z = 0)) : ν = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  refine le_antisymm ?_ bot_le
  calc ν Set.univ ≤ ν ({z | ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)} ∪
        {z | ¬ Free e z}) := by
        refine measure_mono fun z _ => ?_
        by_cases hz : Free e z
        · left
          rintro ⟨h1, h2, h3, h4⟩
          exact hno z hz ⟨h3, h1, h2, h4⟩
        · right; exact hz
    _ ≤ _ := measure_union_le _ _
    _ = 0 := by rw [hν.supp, hfree, add_zero]

end PositivityTheory.Rg.Rsw.L.LMuId

open PositivityTheory.Rg.Rsw.L.LMuId in
theorem PositivityTheory.Rg.Rsw.L.muId : IdemEx → GoodEv → BumpEx → ThProd → EisMeas → NullSing → Uniq → NoFrame → ThetaSideMeasure → ToS →
    MuId := by
  classical
  intro hI hG _ _ hE hN hU hF hT hS D n t B W d hn ψ χ θ μB μW ωB ωW hst mu hmu M m b₀ hb₀ hRho I
  have hdet : b₀.1.det ≠ 0 := hb₀.2
  have hθ : IsInfFam θ := hst.hθ
  obtain ⟨S₁, hS₁⟩ := hE D n t B W d hn ψ χ θ μB μW ωB ωW hst mu hmu M m b₀ hb₀ hRho
  have hΩc : ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → Continuous (Ω 1) := fun Ω hΩ =>
    hΩ.cont.comp (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_⟩
  · intro hno Φ Ω hΩ hcs
    obtain ⟨S₂, hS₂⟩ := hF D t B W ⟨d⟩ b₀ hdet hno
    obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
    obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
    set S := S₁ ∪ S₂ ∪ S₃ ∪ S₄ with hSdef
    obtain ⟨e, he⟩ := (hI D S).1
    obtain ⟨ν, hν, hint⟩ := hS₁ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
    have h0 : ν = 0 := orb_null hν (hN D W.rank t B b₀ hdet S e he ν hν)
      (hS₂ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
    rw [hint Φ (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) Ω hΩ
      (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) hcs, h0, integral_zero_measure]
  · intro x₀ hx₀
    have : m.μ.IsAddHaarMeasure := m.hμ.1
    obtain ⟨ν₂, hν₂, ⟨S₅, hS₅⟩, hT2⟩ := hT D n t B W d hn I θ hθ m.μ inferInstance b₀ hdet x₀ hx₀
    obtain ⟨S₆, hS₆⟩ := hS D W.rank t B b₀ hdet
    have core : ∀ S, S₁ ⊆ S → S₅ ⊆ S → S₆ ⊆ S → ∀ e, IsIdem S e → ∃ c : ℂ, ∀ (Φ : schwartzA θ B.rank n) Ω,
        IsTh ψ χ θ b₀ m.μ Ω → HasCompactSupport (Ω 1) → Good S e Φ.1 → Good S e (Ω 1) →
        mu (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω) =
          c * ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv B b₀ z)) ∂ν₂ := by
      intro S h1 h5 h6 e he
      obtain ⟨ν, hν, hint⟩ := hS₁ S h1 e he
      obtain ⟨hOrb, hyv⟩ := hS₆ S h6 e he ν₂ hν₂
      obtain ⟨κ, hκ⟩ := hU D W.rank t B b₀ hdet S e he ν _ hν hOrb (map_ne_zero ν₂ _ e (hS₅ S h5))
      refine ⟨((κ : ℝ) : ℂ), fun Φ Ω hΩ hcs hΦg hΩg => ?_⟩
      rw [hint Φ hΦg Ω hΩ hΩg hcs, hκ, integral_smul_nnreal_measure,
        transfer hn ν₂ hyv Φ.1 (Ω 1) (GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ _ _ Φ.1 Φ.2).1 (hΩc Ω hΩ) hΦg hΩg,
        NNReal.smul_def, Complex.real_smul]
    by_cases hex : ∃ (Φ₀ : schwartzA θ B.rank n) (Ω₀ : G D t → Mx D W.rank t → ℂ), IsTh ψ χ θ b₀ m.μ Ω₀ ∧
        HasCompactSupport (Ω₀ 1) ∧ ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂ ≠ 0
    · obtain ⟨Φ₀, Ω₀, hΩ₀, hcs₀, hI₀⟩ := hex
      refine ⟨mu (Rsec M m ψ b₀ (fun g => (ωB g Φ₀).1 0) 1 Ω₀) /
        ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂, fun Φ Ω hΩ hcs => ?_⟩
      obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
      obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
      obtain ⟨S₇, hS₇⟩ := hG D θ hθ B.rank n Φ₀.1 Φ₀.2
      obtain ⟨S₈, hS₈⟩ := hG D θ hθ W.rank t (Ω₀ 1) (hΩ₀.mem 1)
      set S := S₁ ∪ S₅ ∪ S₆ ∪ S₃ ∪ S₄ ∪ S₇ ∪ S₈ with hSdef
      obtain ⟨e, he⟩ := (hI D S).1
      obtain ⟨c, hc⟩ := core S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
      have h₀ := hc Φ₀ Ω₀ hΩ₀ hcs₀ (hS₇ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₈ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
      have h := hc Φ Ω hΩ hcs (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
      have hcv : c = mu (Rsec M m ψ b₀ (fun g => (ωB g Φ₀).1 0) 1 Ω₀) /
          ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂ := (eq_div_iff hI₀).mpr h₀.symm
      rw [h, ← hcv, (hT2 Φ.1 Φ.2 (Ω 1) (hΩ.mem 1)).2.2]
    · push Not at hex
      refine ⟨0, fun Φ Ω hΩ hcs => ?_⟩
      obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
      obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
      set S := S₁ ∪ S₅ ∪ S₆ ∪ S₃ ∪ S₄ with hSdef
      obtain ⟨e, he⟩ := (hI D S).1
      obtain ⟨c, hc⟩ := core S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
      rw [hc Φ Ω hΩ hcs (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he), hex Φ Ω hΩ hcs, mul_zero,
        zero_mul]

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.JstTranspose
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LWa1

theorem dense_loc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (hne : ∃ z, σ z ≠ z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0) :
    Dense {h : HA (Fv F v) σ J | HA.mat (Fv F v) σ J h ∈ HFin (Fv F v) σ J} := by
  classical
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  have : Nontrivial (Fv F v ⊗[F] E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := Fv F v) (B := E)
      (algebraMap F E).injective).nontrivial
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have b1 : IsOpen {x : Fv F v | IsUnit x} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne
  have b2 : ∀ x : Fv F v, IsUnit x → ContinuousAt Ring.inverse x := by
    intro x hx
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hx.ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.RealApprox.units_of_free (A := Fv F v) (R := Fv F v ⊗[F] E)
    (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)) b1 b2
  refine GlobalTheory.RealApprox.dense_unitary (inclR (F := F) (Fv F v)) (σ : E →+* E) (sigR (Fv F v) σ) (fun x => ?_) hc
    hne (fun x => ?_) ?_ (fun y => ?_) h1 h2 J hJ hdet
  · simp [sigR, inclR]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [sigR, hc]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  · exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).toLinearMap
  · let S : AddSubgroup (Fv F v ⊗[F] E) :=
      (inclR (F := F) (E := E) (Fv F v)).toAddMonoidHom.range.topologicalClosure
    have hS : IsClosed (S : Set (Fv F v ⊗[F] E)) := AddSubgroup.isClosed_topologicalClosure _
    show y ∈ S
    induction y using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add a b ha hb => exact S.add_mem ha hb
    | tmul a x =>
      have hc : Continuous fun a : Fv F v => a ⊗ₜ[F] x := by
        have : (fun a : Fv F v => a ⊗ₜ[F] x) = fun a : Fv F v => a • ((1 : Fv F v) ⊗ₜ[F] x) := by
          funext a
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Continuous.smul (f := fun a : Fv F v => a)
          (g := fun _ : Fv F v => ((1 : Fv F v) ⊗ₜ[F] x : Fv F v ⊗[F] E)) continuous_id continuous_const
      refine DenseRange.induction_on (HeightOneSpectrum.denseRange_algebraMap F v) a
        (p := fun a => a ⊗ₜ[F] x ∈ S) (hS.preimage hc) fun f => ?_
      refine AddSubgroup.le_topologicalClosure _ ⟨f • x, ?_⟩
      show (1 : Fv F v) ⊗ₜ[F] (f • x) = algebraMap F _ f ⊗ₜ[F] x
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem uj_smul {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) {δ : A}
    (hδ : IsUnit δ) : Formalism.UG.UJ σ (δ • J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ g.1 * (δ • J) * g.1 = δ • J ↔ Formalism.UG.cT σ g.1 * J * g.1 = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hδ.smul_left_cancel

theorem jst_cases (D : D7) (n : ℕ) (P : Fin (n + n) → Fin (n + n) → Prop)
    (h : ∀ a b, P (finSumFinEquiv a) (finSumFinEquiv b)) : ∀ i j, P i j := by
  intro i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  exact h a b

theorem jst_transpose (D : D7) (n : ℕ) : (Jst D n)ᵀ = -Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, eq_comm]

theorem jst_map (D : D7) (n : ℕ) : (Jst D n).map (D.sp.cm.sig : D.host.E →+* D.host.E) = Jst D n := by
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Jst, blk4, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, apply_ite]

theorem jst_mul (D : D7) (n : ℕ) : Jst D n * Jst D n = -1 := by
  simp only [Jst, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  ext i j
  revert i j
  refine jst_cases D n _ fun a b => ?_
  simp only [Matrix.submatrix_apply, Matrix.neg_apply, Equiv.symm_apply_apply]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv.symm : Fin (n + n) ≃ Fin n ⊕ Fin n)]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.one_apply, Equiv.eq_symm_apply, Equiv.symm_apply_eq, Fin.ext_iff] <;> omega

theorem jst_det (D : D7) (n : ℕ) : (Jst D n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (jst_mul D n)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact (neg_one_pow_ne_zero (R := D.host.E) _) this.symm

theorem sig_sig (D : D7) (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  simp [Formalism.BasicNotions.CMData.sig]

theorem sig_ne (D : D7) : ∃ z, D.sp.cm.sig z ≠ z := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  have hall : ∀ a : D.host.E, a ∈ (algebraMap D.host.F D.host.E).range := fun a =>
    (D.sp.cm.fixed a).1 (by simpa [Formalism.BasicNotions.CMData.sig, starRingEnd_apply] using h a)
  have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    ext a
    simp only [Algebra.mem_top, iff_true, Algebra.mem_bot]
    obtain ⟨b, hb⟩ := hall a
    exact ⟨b, hb⟩
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
  rw [D.sp.cm.deg2] at this
  norm_num at this

theorem exists_skew (D : D7) : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
  obtain ⟨z, hz⟩ := sig_ne D
  refine ⟨z - D.sp.cm.sig z, sub_ne_zero.2 (Ne.symm hz), ?_⟩
  rw [map_sub, sig_sig]
  ring

theorem approx_loc (D : D7) (n : ℕ) (v : Pl D) (x : GLoc D.sp.cm.sig (Jst D n) v)
    (O : Set (GLoc D.sp.cm.sig (Jst D n) v)) (hO : IsOpen O) (hx : x ∈ O) :
    ∃ γ : GRat D.sp.cm.sig (Jst D n), ratLoc D.sp.cm.sig (Jst D n) v γ ∈ O := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_skew D
  have hJ' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) = δ • Jst D n := by
    have e1 : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n j i) = -Jst D n i j := by
      intro i j
      have a1 := congrFun (congrFun (jst_map D n) j) i
      have a2 := congrFun (congrFun (jst_transpose D n) i) j
      simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply] at a1 a2
      rw [a1, a2]
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [e1]
    have hδ' : (D.sp.cm.sig : D.host.E →+* D.host.E) δ = -δ := hδ
    rw [hδ', neg_mul_neg]
  have hdet' : (δ • Jst D n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hδ0) (jst_det D n)
  have hE : Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (δ • Jst D n) =
      Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := uj_smul _ _ (Ne.isUnit hδ0)
  have hR : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) = HR (Fv D.host.F v) D.sp.cm.sig (Jst D n) := by
    show Formalism.UG.UJ _ (JR _ _) = Formalism.UG.UJ _ (JR _ _)
    have e : JR (F := D.host.F) (Fv D.host.F v) (δ • Jst D n) =
        inclR (F := D.host.F) (Fv D.host.F v) δ • JR (F := D.host.F) (Fv D.host.F v) (Jst D n) := by
      ext i j
      simp [JR, map_mul]
    rw [e]
    exact uj_smul _ _ ((Ne.isUnit hδ0).map _)
  have hd := dense_loc D.host.F D.host.E v D.sp.cm.sig (sig_sig D) (sig_ne D) (δ • Jst D n) hJ' hdet'
  have hind := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)).isInducing
  have hind' := (isEmbedding_matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n)).isInducing
  obtain ⟨O₀, hO₀, rfl⟩ := hind.isOpen_iff.1 hO
  let x' : HA (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) :=
    (⟨matHom _ _ _ x, by rw [hR]; exact x.2⟩ : HR (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n))
  have hU : IsOpen (matHom (Fv D.host.F v) D.sp.cm.sig (δ • Jst D n) ⁻¹' O₀) := hind'.continuous.isOpen_preimage _ hO₀
  obtain ⟨h', h'O, h'A⟩ := hd.inter_open_nonempty _ hU ⟨x', hx⟩
  obtain ⟨γ', hγ', e⟩ := Subgroup.mem_map.1 h'A
  refine ⟨⟨γ', hE ▸ hγ'⟩, ?_⟩
  show matHom _ _ _ _ ∈ O₀
  have e2 : matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (ratLoc D.sp.cm.sig (Jst D n) v ⟨γ', hE ▸ hγ'⟩) =
      Formalism.UG.bc (inclR (F := D.host.F) (Fv D.host.F v)) γ' := rfl
  rw [e2, e]
  exact h'O

end PositivityTheory.Rg.Rsw.L.LWa1

namespace PositivityTheory.Rg.Rsw.L

open LWa1 in
theorem wa1 : WeakApproximationFinitePlace := by
  intro D n v U hU g
  set x := proj D.sp.cm.sig (Jst D n) v g with hxdef
  let V : Subgroup (GLoc D.sp.cm.sig (Jst D n) v) := U.comap (emb D.sp.cm.sig (Jst D n) v)
  have hV : IsOpen (V : Set (GLoc D.sp.cm.sig (Jst D n) v)) := hU.preimage (continuous_emb _ _ v)
  have hO : IsOpen {y : GLoc D.sp.cm.sig (Jst D n) v | y⁻¹ * x ∈ V} :=
    hV.preimage (continuous_inv.mul continuous_const)
  obtain ⟨γ, hγ⟩ := approx_loc D n v x _ hO (by simp [V])
  set k := emb D.sp.cm.sig (Jst D n) v ((ratLoc D.sp.cm.sig (Jst D n) v γ)⁻¹ * x) with hk
  refine ⟨ratEmb D.sp.cm.sig (Jst D n) γ, ?_, (ratEmb D.sp.cm.sig (Jst D n) γ)⁻¹ * g * k⁻¹, ?_, k, hγ, ?_, by group⟩
  · show _ ∈ ratPts _ _
    rw [← range_ratEmb]
    exact ⟨γ, rfl⟩
  · rw [map_mul, map_mul, map_inv, map_inv, proj_ratEmb, hk, proj_emb_self, ← hxdef]
    group
  · rw [← range_emb]
    exact ⟨_, rfl⟩

end PositivityTheory.Rg.Rsw.L
end
end
