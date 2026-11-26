module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetLatHLoc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TupSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.SelfDualMeasureLatticeOne
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.EvalVSingleVSame
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evalV_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evalV F v a = a v := rfl

open Classical in
theorem evalV_singleV_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_same _ _ _

open Classical in
theorem evalV_singleV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v) : evalV F w (singleV F v y) = 0 := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ _ h

theorem addChar_sum {A M ι : Type} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem AF_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

theorem psi_split (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ x : AF F,
      (∀ v, v ∉ S → evalV F v (sndA F x) ∈ v.adicCompletionIntegers F) →
      ψ x = psiInf F ψ (fstA F x) * ∏ v ∈ S, psiV F ψ v (evalV F v (sndA F x)) := by
  classical
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat ξ)
  refine ⟨hfin.toFinset, fun S hS x hx => ?_⟩
  set xf : Af F := sndA F x with hxf
  set r : Af F := xf - ∑ v ∈ S, singleV F v (evalV F v xf) with hr
  have hdec : x = pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r := by
    refine AF_ext ?_ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), map_sum, fstA_pairA, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, add_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), map_sum, sndA_pairA, sndA_pairA]
        simp only [sndA_pairA, hr, hxf]
        abel
  have hrv : ∀ v, evalV F v r = if v ∈ S then 0 else evalV F v xf := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr, map_sub, map_sum]
    by_cases hv : v ∈ S
    · rw [if_pos hv, Finset.sum_eq_single v]
      · rw [evalV_singleV_same, sub_self]
      · intro w _ hw
        exact evalV_singleV_ne (Ne.symm hw) _
      · intro h; exact absurd hv h
    · rw [if_neg hv, Finset.sum_eq_zero, sub_zero]
      intro w hw
      exact evalV_singleV_ne (by rintro rfl; exact hv hw) _
  have hmem : algebraMap F (Af F) ξ * r ∈ GroundTheory.Global.finiteInvDifferent F := by
    intro v
    have e1 : (algebraMap F (Af F) ξ * r) v = algebraMap F (Fv F v) ξ * evalV F v r := rfl
    rw [e1, hrv v]
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_zero]
      exact zero_mem _
    · rw [if_neg hv]
      have hξv : algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F := by
        by_contra h
        exact hv (hS (hfin.mem_toFinset.2 h))
      exact GroundTheory.Global.mem_localInvDifferent_of_mem (mul_mem hξv (hx v hv))
  have hr1 : ψ (pairA F 0 r) = 1 := by
    rw [hξ]
    have e2 : algebraMap F (AF F) ξ * pairA F 0 r = pairA F 0 (algebraMap F (Af F) ξ * r) := by
      refine AF_ext ?_ ?_
      · rw [map_mul, fstA_pairA, fstA_pairA, mul_zero]
      · rw [map_mul, sndA_pairA, sndA_pairA, AlgHom.commutes]
    rw [e2]
    have hm2 : pairA F 0 (algebraMap F (Af F) ξ * r) ∈ GroundTheory.Global.invDifferentAdeles F :=
      GroundTheory.Global.mem_invDifferentAdeles.mpr hmem
    rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hm2]
    simp [pairA]
  have h1 : ψ x = ψ (pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r) :=
    congrArg ψ hdec
  rw [h1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, addChar_sum, hr1, mul_one]
  rfl

end PositivityTheory.SiegelWeilFormula.GFac

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TrPairGramFE
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Tens

variable {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']

abbrev fE (f : R →ₐ[F] R') : R ⊗[F] E →ₐ[F] R' ⊗[F] E := Algebra.TensorProduct.map f (AlgHom.id F E)

theorem fE_comp (f : R →ₐ[F] R') (g : R' →ₐ[F] R'') (x : R ⊗[F] E) :
    fE (E := E) g (fE f x) = fE (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [fE]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fE_inclR (f : R →ₐ[F] R') (e : E) : fE f (inclR R e) = inclR R' e := by
  simp [fE, inclR]

theorem trace_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') (x : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) x) = Algebra.trace R' (R' ⊗[F] E) (fE f x) := by
  have h1 := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map (AlgHom.id F R) bs x
  have h2 := GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.trace_map f bs x
  have h3 : Algebra.TensorProduct.map (AlgHom.id F R) (AlgHom.id F E) x = x := by
    rw [Algebra.TensorProduct.map_id]; rfl
  rw [h3] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fE, h2, h1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, AlgHom.commutes]
  rfl

theorem sigR_fE (σ : E →ₐ[F] E) (f : R →ₐ[F] R') (x : R ⊗[F] E) : sigR R' σ (fE f x) = fE f (sigR R σ x) :=
  GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_map f σ x

theorem trPair_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) :
    f (trPair R A B) = trPair R' (A.map (fE f)) (B.map (fE f)) := by
  simp only [trPair, map_mul, AlgHom.commutes]
  rw [trace_fE bs]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, Matrix.map_apply]

theorem gramR_fE (σ : E →ₐ[F] E) (f : R →ₐ[F] R') {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → R ⊗[F] E) :
    (gramR R σ J Y).map (fE f) = gramR R' σ J (fun a i => fE f (Y a i)) := by
  ext a c
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_fE, fE_inclR]

theorem trPair_gram_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (f : R →ₐ[F] R') {M m : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) (Y : Fin m → Fin M → R ⊗[F] E) :
    f (trPair R B (gramR R σ J Y)) = trPair R' (B.map (fE f)) (gramR R' σ J (fun a i => fE f (Y a i))) := by
  rw [trPair_fE bs, gramR_fE]

theorem trPair_T_fE {d : ℕ} (bs : Module.Basis (Fin d) F E) (f : R →ₐ[F] R') {m : ℕ}
    (T : Matrix (Fin m) (Fin m) E) (B : Matrix (Fin m) (Fin m) (R ⊗[F] E)) :
    f (trPair R (T.map (inclR R)) B) = trPair R' (T.map (inclR R')) (B.map (fE f)) := by
  rw [trPair_fE bs]
  congr 1
  ext a c
  simp [Matrix.map_apply, fE_inclR]

end Tens

theorem hermInf_val (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = matInf (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
  rfl

theorem hermV_val (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermV σ v (hermFin σ b) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      matV v (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) := by
  ext i j
  simp only [hermV, hermFin, GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap, matV, Matrix.map_apply]
  exact fE_comp (sndA F) (evalV F v) _

theorem hermV_val' (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (b : HermR (AF F) σ n) :
    ((hermV σ v (hermFin σ b) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (fE ((evalV F v).comp (sndA F))) := by
  rw [hermV_val]; rfl

theorem projV_projFin {M n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E) :
    projV v (projFin X) = fun a i => fE ((evalV F v).comp (sndA F)) (X a i) := by
  funext a i
  exact fE_comp (sndA F) (evalV F v) _

theorem projInf_eq {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projInf X = fun a i => fE (fstA F) (X a i) := rfl

end PositivityTheory.SiegelWeilFormula.GFac

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.AlgebraMapMemIntE
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (Fv F v ⊗[F] E) :=
  {e | ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr e k ∈ v.adicCompletionIntegers F}

structure Good (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  one : (1 : Fv F v ⊗[F] E) ∈ intE bs v
  mul : ∀ e e', e ∈ intE bs v → e' ∈ intE bs v → e * e' ∈ intE bs v
  sig : ∀ e, e ∈ intE bs v → sigR (Fv F v) σ e ∈ intE bs v
  tr : ∀ e, e ∈ intE bs v → Algebra.trace (Fv F v) (Fv F v ⊗[F] E) e ∈ v.adicCompletionIntegers F
  half : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F
  hJ : ∀ i j, inclR (Fv F v) (J i j) ∈ intE bs v
  hT : ∀ i j, inclR (Fv F v) (T i j) ∈ intE bs v

theorem add_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {e e' : Fv F v ⊗[F] E}
    (he : e ∈ intE bs v) (he' : e' ∈ intE bs v) : e + e' ∈ intE bs v := by
  intro k
  simp only [map_add (f := _), Finsupp.add_apply]
  exact add_mem (he k) (he' k)

theorem zero_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    (0 : Fv F v ⊗[F] E) ∈ intE bs v := by
  intro k
  simp only [map_zero, Finsupp.zero_apply]
  exact zero_mem _

theorem sum_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ intE bs v) : ∑ i ∈ s, f i ∈ intE bs v := by
  classical
  exact Finset.sum_induction f (· ∈ intE bs v) (fun _ _ ha hb => add_mem_intE bs v ha hb) (zero_mem_intE bs v) hf

theorem algebraMap_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (1 : Fv F v ⊗[F] E) ∈ intE bs v) {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) r ∈ intE bs v := by
  intro k
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hr (h1 k)

theorem repr_tmul_apply {d : ℕ} (bs : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R] (c : R) (x : E)
    (k : Fin d) : (Algebra.TensorProduct.basis R bs).repr (c ⊗ₜ[F] x) k = c * algebraMap F R (bs.repr x k) := by
  simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]

theorem eq_sum_tmul {d : ℕ} (bs : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R] (e : R ⊗[F] E) :
    e = ∑ k, (Algebra.TensorProduct.basis R bs).repr e k ⊗ₜ[F] bs k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R bs).sum_repr e]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

def OkE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (x : E) : Prop :=
  ∀ m, algebraMap F (Fv F v) (bs.repr x m) ∈ v.adicCompletionIntegers F

theorem ev_okE {d : ℕ} (bs : Module.Basis (Fin d) F E) (x : E) : ∀ᶠ v in cofinite, OkE bs v x :=
  Filter.eventually_all.2 fun m => GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat _

theorem tmul_mem_intE {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {c : Fv F v} {x : E}
    (hc : c ∈ v.adicCompletionIntegers F) (hx : OkE bs v x) : c ⊗ₜ[F] x ∈ intE bs v := fun m => by
  rw [repr_tmul_apply]
  exact mul_mem hc (hx m)

theorem eventually_good (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ v in cofinite, Good σ bs J T v := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis bs
  have h2 : ∀ᶠ v in cofinite, ∀ k l, OkE bs v (bs k * bs l) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => ev_okE bs _
  have h3 : ∀ᶠ v in cofinite, ∀ k, OkE bs v (σ (bs k)) := Filter.eventually_all.2 fun k => ev_okE bs _
  have h4 : ∀ᶠ v in cofinite, ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (bs k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat _
  have h6 : ∀ᶠ v in cofinite, ∀ i j, OkE bs v (J i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_okE bs _
  have h7 : ∀ᶠ v in cofinite, ∀ i j, OkE bs v (T i j) :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_okE bs _
  filter_upwards [ev_okE bs (1 : E), h2, h3, h4, GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat (1 / 2 : F), h6, h7]
    with v h1 h2 h3 h4 h5 h6 h7
  have hone : (1 : Fv F v ⊗[F] E) ∈ intE bs v := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_intE bs v (one_mem _) h1
  refine ⟨hone, fun e e' he he' => ?_, fun e he => ?_, fun e he => ?_, h5, fun i j => ?_, fun i j => ?_⟩
  · rw [eq_sum_tmul bs (Fv F v) e, eq_sum_tmul bs (Fv F v) e', Finset.sum_mul_sum]
    refine sum_mem_intE bs v _ _ fun k _ => sum_mem_intE bs v _ _ fun l _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_intE bs v (mul_mem (he k) (he' l)) (h2 k l)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bs (Fv F v) e, map_sum]
    refine sum_mem_intE bs v _ _ fun k _ => ?_
    have : sigR (Fv F v) σ ((Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] bs k) =
        (Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] σ (bs k) := by
      simp [sigR]
    rw [this]
    exact tmul_mem_intE bs v (he k) (h3 k)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bs (Fv F v) e, map_sum]
    refine sum_mem fun k _ => ?_
    rw [GlobalTheory.CompanionTheory.SW.HermSd.trace_tmul]
    exact mul_mem (he k) (h4 k)
  · simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    exact tmul_mem_intE bs v (one_mem _) (h6 i j)
  · simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    exact tmul_mem_intE bs v (one_mem _) (h7 i j)

theorem diag_eq_halfTrace (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (e : Fv F v ⊗[F] E)
    (he : sigR (Fv F v) σ e = e) :
    e = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) e) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
  obtain ⟨bs⟩ : Nonempty (Module.Basis (Fin (Module.finrank F E)) F E) := ⟨Module.finBasis F E⟩
  have h2 : e + e = algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) e) := by
    conv_lhs => rw [show e + e = e + sigR (Fv F v) σ e by rw [he]]
    rw [eq_sum_tmul bs (Fv F v) e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hs : sigR (Fv F v) σ ((Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] bs k) =
        (Algebra.TensorProduct.basis (Fv F v) bs).repr e k ⊗ₜ[F] σ (bs k) := by
      simp [sigR]
    rw [hs, ← TensorProduct.tmul_add, GlobalTheory.SplitAdeleTrace.add_conj_eq_trace hCM, GlobalTheory.CompanionTheory.SW.HermSd.trace_tmul,
      Algebra.algebraMap_eq_smul_one (Algebra.trace F E (bs k)), ← TensorProduct.smul_tmul]
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.smul_def, mul_comm]
  have hh : algebraMap F (Fv F v ⊗[F] E) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v ⊗[F] E)) 2, ← map_mul]
    norm_num
    rfl
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← h2]
  calc e = (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * 2) * e := by rw [hh, one_mul]
    _ = _ := by ring

theorem herm_entries (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (b : HermR (Fv F v) σ m) (hb : b ∈ latH σ bs v m) (i j : Fin m) :
    (b : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) i j ∈ intE bs v := by
  have hsym : ∀ a c, sigR (Fv F v) σ ((b : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) c a) =
      (b : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) a c := b.2
  rcases lt_trichotomy i j with h | h | h
  · exact hb.2 i j h
  · subst h
    rw [diag_eq_halfTrace σ hCM v _ (hsym i i)]
    exact algebraMap_mem_intE bs v hv.one (hb.1 i)
  · rw [← hsym i j]
    exact hv.sig _ (hb.2 j i h)

theorem gram_entries (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (Y : Fin m → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV bs v) (a c : Fin m) :
    gramR (Fv F v) σ J Y a c ∈ intE bs v := by
  simp only [gramR, hR, hform, JR, Matrix.map_apply]
  refine sum_mem_intE bs v _ _ fun i _ => sum_mem_intE bs v _ _ fun j _ => ?_
  exact hv.mul _ _ (hv.mul _ _ (hv.sig _ (hY a i)) (hv.hJ i j)) (hY c j)

theorem trPair_int (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (A B : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hA : ∀ i j, A i j ∈ intE bs v)
    (hB : ∀ i j, B i j ∈ intE bs v) : trPair (Fv F v) A B ∈ v.adicCompletionIntegers F := by
  unfold trPair
  refine mul_mem hv.half (hv.tr _ ?_)
  exact sum_mem_intE bs v _ _ fun i _ => sum_mem_intE bs v _ _ fun j _ => hv.mul _ _ (hA i j) (hB j i)

theorem mulVec_latO (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    {m : ℕ} (B : Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) (hB : ∀ i j, B i j ∈ intE bs v)
    (y : Fin m → Fv F v ⊗[F] E) (hy : y ∈ latO bs v) : B.mulVec y ∈ latO bs v := by
  intro a
  show (B.mulVec y) a ∈ intE bs v
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem_intE bs v _ _ fun j _ => hv.mul _ _ (hB a j) (hy j)

end PositivityTheory.SiegelWeilFormula.GFac

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cpow_mul_nonneg (x r : ℝ) (hr : 0 ≤ r) (w : ℂ) :
    (((x * r : ℝ)) : ℂ) ^ w = (x : ℂ) ^ w * (r : ℂ) ^ w := by
  rcases hr.lt_or_eq with hr | hr
  · by_cases hx : x = 0
    · subst hx
      by_cases hw : w = 0
      · simp [hw]
      · simp [Complex.zero_cpow hw]
    · have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hxr : ((x * r : ℝ) : ℂ) ≠ 0 := by push_cast; exact mul_ne_zero hx' hr'
      rw [Complex.cpow_def_of_ne_zero hxr, Complex.cpow_def_of_ne_zero hx', Complex.cpow_def_of_ne_zero hr',
        ← Complex.exp_add]
      congr 1
      have : Complex.log ((x * r : ℝ) : ℂ) = Complex.log (x : ℂ) + Complex.log (r : ℂ) := by
        rw [show ((x * r : ℝ) : ℂ) = (r : ℂ) * (x : ℂ) by push_cast; ring, Complex.log_ofReal_mul hr hx',
          Complex.ofReal_log hr.le]
        ring
      rw [this]
      ring
  · subst hr
    by_cases hw : w = 0
    · simp [hw]
    · simp [Complex.zero_cpow hw]

theorem cpow_mul_prod {ι : Type} (x : ℝ) (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (w : ℂ) :
    (((x * ∏ i ∈ s, r i : ℝ)) : ℂ) ^ w = (x : ℂ) ^ w * ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ w := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have e : x * (r j * ∏ i ∈ s, r i) = (x * ∏ i ∈ s, r i) * r j := by ring
    rw [e, cpow_mul_nonneg _ _ (hr j (Finset.mem_insert_self j s)),
      ih x (fun i hi => hr i (Finset.mem_insert_of_mem hi))]
    ring

theorem self_dual_measure_lattice_one (σ : E →ₐ[F] E) {d M n : ℕ} (bs : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E)
    (T : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (hv : Good σ bs J T v)
    (lam : Measure (Fin n → Fv F v ⊗[F] E)) (hlam : lam.IsAddHaarMeasure) (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (hco : IsCO L₁) (h1 : (L₁ : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (h2 : (L₂ : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v)
    (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (hB : ∀ i j, B i j ∈ intE bs v) :
    nu2 lam L₁ L₂ B = 1 := by
  have hset : {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + B.mulVec y'} = (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext x
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      have hy'' : y' ∈ latO bs v := by rw [← h2]; exact hy'
      have hB' : B.mulVec y' ∈ (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := by
        rw [h1]; exact mulVec_latO σ bs J T v hv B hB y' hy''
      exact L₁.add_mem hy hB'
    · intro hx
      exact ⟨x, hx, 0, L₂.zero_mem, by simp⟩
  have hpos : lam (L₁ : Set (Fin n → Fv F v ⊗[F] E)) ≠ 0 :=
    (hco.1.measure_pos lam ⟨0, L₁.zero_mem⟩).ne'
  have hfin : lam (L₁ : Set (Fin n → Fv F v ⊗[F] E)) ≠ ⊤ := hco.2.measure_lt_top.ne
  unfold nu2
  rw [hset, ENNReal.div_self hpos hfin]
  rfl

theorem psiT_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d M n : ℕ} (bs : Module.Basis (Fin d) F E)
    (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ b ∈ UH σ bs n S,
      ψ (-trPair (AF F) (T.map (inclR (AF F))) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
        psiInf F ψ (-trPair (Ainf F) (T.map (inclR (Ainf F)))
          (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) *
        ∏ v ∈ S, psiV F ψ v (-trPair (Fv F v) (T.map (inclR (Fv F v)))
          (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
  classical
  obtain ⟨Sψ, hSψ⟩ := psi_split ψ hψ
  have hfin := Filter.eventually_cofinite.1 (eventually_good σ hCM bs J T)
  refine ⟨Sψ ∪ hfin.toFinset, fun S hS b hb => ?_⟩
  have hgood : ∀ v, v ∉ S → Good σ bs J T v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h)))
  have hcomp : ∀ v, evalV F v (sndA F (-trPair (AF F) (T.map (inclR (AF F))) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))) =
      -trPair (Fv F v) (T.map (inclR (Fv F v))) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
    intro v
    have h3 := trPair_T_fE bs ((evalV F v).comp (sndA F)) T (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    rw [AlgHom.comp_apply] at h3
    rw [map_neg, map_neg, h3, hermV_val']
  have hinf : fstA F (-trPair (AF F) (T.map (inclR (AF F))) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
      -trPair (Ainf F) (T.map (inclR (Ainf F))) (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := by
    rw [map_neg, trPair_T_fE bs (fstA F) T, hermInf_val]
    rfl
  have hint : ∀ v, v ∉ S → evalV F v (sndA F (-trPair (AF F) (T.map (inclR (AF F)))
      (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))) ∈ v.adicCompletionIntegers F := by
    intro v hv
    rw [hcomp v]
    have hbv : hermV σ v (hermFin σ b) ∈ latH σ bs v n := hb v hv
    exact neg_mem (trPair_int σ bs J T v (hgood v hv) _ _ (fun i j => (hgood v hv).hT i j)
      (herm_entries σ hCM bs J T v (hgood v hv) _ hbv))
  rw [hSψ S (fun v hv => hS (Finset.mem_union_left _ hv)) _ hint, hinf]
  congr 1
  exact Finset.prod_congr rfl fun v _ => by rw [hcomp v]

theorem continuous_locI (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (hφ : Continuous φ) :
    Continuous (fun Y => φ Y * psiV F ψ v (trPair (Fv F v) B (gramR (Fv F v) σ J Y))) := by
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨-, -, -, -, -, htr, -, -, -, hgr⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  have hpsi : Continuous (psiV F ψ v) := by
    unfold psiV
    exact hψ.comp ((continuous_const.prodMk continuous_id).comp (GlobalTheory.CompanionTheory.AdelicCharLocal.continuous_singleV F v))
  refine hφ.mul (hpsi.comp ?_)
  unfold trPair
  refine continuous_const.mul (htr.comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ => ?_
  exact continuous_const.mul ((continuous_apply a).comp ((continuous_apply c).comp (hgr n M J)))

theorem jt_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n d : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (P : ι → PX M n) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (pure : IsPureFin bs Φf Φv) (prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf) (sdW : SdW F E σ M J (AF F) ψ n μ)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ b ∈ UH σ bs n S,
      jtR (AF F) σ J ψ μ Φ b = jtR (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (hermInf σ b) *
        ∏ v ∈ S, jtR (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (hermV σ v (hermFin σ b)) := by
  classical
  obtain ⟨Sψ, hSψ⟩ := psi_split ψ hψ
  obtain ⟨St, hSt⟩ := tup_split σ hCM ψ hψ M n d J hJ bs μ sdW μi hμi μv hμv
  have hfing := Filter.eventually_cofinite.1 (eventually_good σ hCM bs J T)
  have hfinp := Filter.eventually_cofinite.1 pure.2.1
  refine ⟨Sψ ∪ St ∪ hfing.toFinset ∪ hfinp.toFinset, fun S hS b hb => ?_⟩
  have hSψS : Sψ ⊆ S := fun v hv => hS (by simp [hv])
  have hStS : St ⊆ S := fun v hv => hS (by simp [hv])
  have hgood : ∀ v, v ∉ S → Good σ bs J T v := fun v hv => by
    by_contra h
    exact hv (hS (by simp [hfing.mem_toFinset.2 h]))
  have hpv : ∀ v, v ∉ S → Φv v = (latV bs v).indicator 1 := fun v hv => by
    by_contra h
    exact hv (hS (by simp [hfinp.mem_toFinset.2 h]))
  have hbv : ∀ v, v ∉ S → hermV σ v (hermFin σ b) ∈ latH σ bs v n := fun v hv => hb v hv
  let gi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => phiInf θ l fr g P Y *
    psiInf F ψ (trPair (Ainf F) (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (gramR (Ainf F) σ J Y))
  let gv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ := fun v Y => Φv v Y *
    psiV F ψ v (trPair (Fv F v) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y))
  have hmeas : ∀ v ∈ S, AEStronglyMeasurable (gv v) (μv v) := by
    intro v _
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
    exact (continuous_locI σ hCM ψ hψ.1 v J _ (Φv v) (pure.1 v).1.continuous).aestronglyMeasurable
  have key := hSt S hStS gi gv hmeas
  have hlat := (GlobalTheory.T.adelic_tuple_projections F E σ hCM d bs n M).2.2.2.2.2.1
  have hpt : ∀ Y, Φ Y * ψ (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (gramR (AF F) σ J Y)) =
      (GlobalTheory.CompanionTheory.SW.intOff bs S).indicator (fun X => gi (projInf X) * ∏ v ∈ S, gv v (projV v (projFin X))) Y := by
    intro Y
    by_cases hY : Y ∈ GlobalTheory.CompanionTheory.SW.intOff bs S
    · rw [Set.indicator_of_mem hY]
      have hYv : ∀ v, v ∉ S → projV v (projFin Y) ∈ latV bs v := hY
      have hΦ : Φ Y = phiInf θ l fr g P (projInf Y) * ∏ v ∈ S, Φv v (projV v (projFin Y)) := by
        rw [prod Y, pure.2.2 (projFin Y), finprod_eq_prod_of_mulSupport_subset]
        intro v hv
        by_contra hvS
        apply hv
        show Φv v (projV v (projFin Y)) = 1
        rw [hpv v hvS, Set.indicator_of_mem (hYv v hvS)]
        rfl
      have hc : ∀ v, evalV F v (sndA F (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (gramR (AF F) σ J Y))) =
          trPair (Fv F v) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
            (gramR (Fv F v) σ J (projV v (projFin Y))) := by
        intro v
        have h3 := trPair_gram_fE bs σ ((evalV F v).comp (sndA F)) J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) Y
        rw [AlgHom.comp_apply] at h3
        rw [h3, hermV_val', projV_projFin]
      have hi : fstA F (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (gramR (AF F) σ J Y)) =
          trPair (Ainf F) (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (gramR (Ainf F) σ J (projInf Y)) := by
        rw [trPair_gram_fE bs σ (fstA F) J, hermInf_val, projInf_eq]
        rfl
      have hint : ∀ v, v ∉ S → evalV F v (sndA F (trPair (AF F) (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
          (gramR (AF F) σ J Y))) ∈ v.adicCompletionIntegers F := by
        intro v hv
        rw [hc v]
        exact trPair_int σ bs J T v (hgood v hv) _ _ (herm_entries σ hCM bs J T v (hgood v hv) _ (hbv v hv))
          (gram_entries σ bs J T v (hgood v hv) _ (hYv v hv))
      rw [hΦ, hSψ S hSψS _ hint, hi]
      simp only [gi, gv, hc]
      rw [Finset.prod_mul_distrib]
      ring
    · rw [Set.indicator_of_notMem hY]
      have hY' : ¬ ∀ v, v ∉ S → projV v (projFin Y) ∈ latV bs v := hY
      push_neg at hY'
      obtain ⟨v, hvS, hYv⟩ := hY'
      have hsupp : (Function.mulSupport fun w => Φv w (projV w (projFin Y))).Finite := by
        refine (hfinp.union (Filter.eventually_cofinite.1 (hlat (projFin Y)))).subset ?_
        intro w hw
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        apply hw
        show Φv w (projV w (projFin Y)) = 1
        rw [hcon.1, Set.indicator_of_mem hcon.2]
        rfl
      rw [prod Y, pure.2.2 (projFin Y), finprod_eq_zero _ v _ hsupp, mul_zero, zero_mul]
      rw [hpv v hvS, Set.indicator_of_notMem hYv]
  unfold jtR
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), key]

theorem whI_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n d : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (P : ι → PX M n) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (haar : ∀ v, (lam v).IsAddHaarMeasure) (co : ∀ v, IsCO (L₁ v) ∧ IsCO (L₂ v))
    (std : ∀ᶠ v in cofinite, (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧ (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v)
    (pure : IsPureFin bs Φf Φv) (prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf) (sdW : SdW F E σ M J (AF F) ψ n μ)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) (z : ℂ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∀ b ∈ UH σ bs n S,
      whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b =
        whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z (hermInf σ b) *
        ∏ v ∈ S, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z
          (hermV σ v (hermFin σ b)) := by
  classical
  obtain ⟨S1, h1⟩ := jt_split σ hCM M n d J hJ T bs ψ hψ θ l fr g P Φ Φf Φv μ pure prod sdW μi hμi μv hμv
  obtain ⟨S2, h2⟩ := psiT_split σ hCM bs J T ψ hψ
  have hfing := Filter.eventually_cofinite.1 (eventually_good σ hCM bs J T)
  have hstd := Filter.eventually_cofinite.1 std
  refine ⟨S1 ∪ S2 ∪ hfing.toFinset ∪ hstd.toFinset, fun S hS b hb => ?_⟩
  have hS1 : S1 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv)))
  have hS2 : S2 ⊆ S := fun v hv => hS (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
  have hgood : ∀ v, v ∉ S → Good σ bs J T v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_left _ (Finset.mem_union_right _ (hfing.mem_toFinset.2 h))))
  have hL : ∀ v, v ∉ S → (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧
      (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v := fun v hv => by
    by_contra h
    exact hv (hS (Finset.mem_union_right _ (hstd.mem_toFinset.2 h)))
  have hbv : ∀ v, v ∉ S → hermV σ v (hermFin σ b) ∈ latH σ bs v n := fun v hv => hb v hv
  have hnu : nuA θ g lam L₁ L₂ (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) =
      nuInf θ g (hermInf σ b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        ∏ v ∈ S, nu2 (lam v) (L₁ v) (L₂ v) (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
    unfold nuA
    rw [hermInf_val]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset]
    · exact Finset.prod_congr rfl fun v _ => by rw [hermV_val]
    · intro v hv
      by_contra hvS
      apply hv
      show nu2 (lam v) (L₁ v) (L₂ v) (matV v (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) = 1
      rw [← hermV_val]
      exact self_dual_measure_lattice_one σ bs J T v (hgood v hvS) (lam v) (haar v) (L₁ v) (L₂ v) (co v).1 (hL v hvS).1 (hL v hvS).2 _
        (herm_entries σ hCM bs J T v (hgood v hvS) _ (hbv v hvS))
  unfold whI
  rw [hnu, cpow_mul_prod _ S (fun v => nu2 (lam v) (L₁ v) (L₂ v)
      (hermV σ v (hermFin σ b) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) (fun v _ => ENNReal.toReal_nonneg), h1 S hS1 b hb, h2 S hS2 b hb,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end PositivityTheory.SiegelWeilFormula.GFac

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TendstoUH
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_UH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (bs : Module.Basis (Fin d) F E) (n : ℕ)
    (ν : Measure (HermR (AF F) σ n)) (f : HermR (AF F) σ n → ℂ) (hf : Integrable f ν) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ∫ b in UH σ bs n S, f b ∂ν) atTop (nhds (∫ b, f b ∂ν)) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have he : ∀ S, ∫ b in UH σ bs n S, f b ∂ν = ∫ b, (UH σ bs n S).indicator f b ∂ν := fun S =>
    (integral_indicator (measurableSet_UH σ hCM bs n S)).symm
  simp_rw [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall fun S => hf.aestronglyMeasurable.indicator (measurableSet_UH σ hCM bs n S)
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_
    by_cases h : y ∈ UH σ bs n S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ bs v n}.Finite :=
      Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_latH σ bs y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : y ∈ UH σ bs n S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [Set.indicator_of_mem hmem]

end PositivityTheory.SiegelWeilFormula.GFac

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem factor_core (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M n d : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (T : Matrix (Fin n) (Fin n) E) (bs : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    {ι : Type} [Fintype ι] (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (fr : ι → GL (Fin M) ℂ) (g : ι → GL (Fin n) ℂ)
    (P : ι → PX M n) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)) (ν : Measure (HermR (AF F) σ n))
    (haar : ∀ v, (lam v).IsAddHaarMeasure) (co : ∀ v, IsCO (L₁ v) ∧ IsCO (L₂ v))
    (std : ∀ᶠ v in cofinite, (L₁ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v ∧ (L₂ v : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v)
    (pure : IsPureFin bs Φf Φv) (prod : IsProdInfFin Φ (phiInf θ l fr g P) Φf) (sdW : SdW F E σ M J (AF F) ψ n μ)
    (sdH : SdHerm F E σ (AF F) ψ n ν)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (νi : Measure (HermR (Ainf F) σ n))
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n))
    (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi) (hνi : SdHerm F E σ (Ainf F) (psiInf F ψ) n νi)
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) (hνv : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v))
    (z : ℂ) (hI : Integrable (whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z) ν)
    (hIv : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z)
        (νv v)) :
    Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) =>
        (∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi) *
        ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b
          ∂(νv v))
      atTop (nhds (∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν)) := by
  classical
  obtain ⟨S₀, hS₀⟩ := herm_split σ hCM ψ hψ n d bs ν sdH νi hνi νv hνv
  obtain ⟨S₁, hS₁⟩ := whI_split σ hCM M n d J hJ T bs ψ hψ θ l fr g P lam L₁ L₂ Φ Φf Φv μ haar co std pure prod sdW
    μi hμi μv hμv z
  refine (tendsto_UH σ hCM bs n ν _ hI).congr' ?_
  filter_upwards [eventually_ge_atTop (S₀ ∪ S₁)] with S hS
  have h0 : S₀ ⊆ S := fun v hv => hS (Finset.mem_union_left _ hv)
  have h1 : S₁ ⊆ S := fun v hv => hS (Finset.mem_union_right _ hv)
  rw [setIntegral_congr_fun (measurableSet_UH σ hCM bs n S) (fun b hb => hS₁ S h1 b hb)]
  exact hS₀ S h0 _ _ (fun v _ => (hIv v).aestronglyMeasurable)

theorem factorX : FactorX := by
  intro F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν h μi νi μv νv hμi hνi hμv hνv z hI _ hIv
  exact factor_core σ h.cm M n d J h.herm T bs ψ h.chr θ l fr g P lam L₁ L₂ Φ Φf Φv μ ν h.haar h.co h.std h.pure h.prod
    h.sdW h.sdH μi νi μv νv hμi hνi hμv hνv z hI hIv

end PositivityTheory.SiegelWeilFormula.GFac

end
