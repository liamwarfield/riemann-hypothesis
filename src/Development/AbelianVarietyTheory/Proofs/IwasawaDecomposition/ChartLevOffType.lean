module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIffRead
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section Read

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {j : ℕ} {Ch : Type} {chOf : (I.stp u I.mu0 j).Cl → Ch}
  {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
  {y : (I.stp u I.mu0 j).Cl → GA B (B.R.N j)} {st : ∀ c, (I.stp u I.mu0 j).Stab c → GL (Fin (B.R.N j)) B.host.E}
  {k : Ch → GA B (B.R.N j)}


set_option maxHeartbeats 2000000 in
theorem mem_iff_read (H : I.Reads u I.mu0 j chOf Lb U chi y st k) (c : (I.stp u I.mu0 j).Cl) (x : GA B (B.R.N j))
    (hx : x ∈ UAd B.sp.cm (B.R.N j)) :
    x ∈ U (chOf c) ↔ ∃ (hJ : x ∈ J0 B.sp.cm (B.R.N j) ((B.primes X).vT u))
      (hm : (redG B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp),
      cosetIn ((I.stp u I.mu0 j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u I.mu0 j).rep c)) = cosetIn ((I.stp u I.mu0 j).rep c) := by
  constructor
  · intro hxU
    obtain ⟨q, hq⟩ := OneLevel.pt_exists I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) hx
    obtain ⟨κ, h1, h2, h3⟩ := (H.lev c x q hq).1 hxU
    subst h2
    obtain ⟨γ, h, θ⟩ := κ
    obtain rfl : γ = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h1.trans (map_one _).symm))
    obtain ⟨hJ, hr⟩ := OneLevel.pt_read I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) h.1 θ.1 hq
    obtain rfl : θ = 1 := Subtype.ext (funext fun P => (Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P.1 P.2).elim)
    refine ⟨hJ, hr ▸ h.2, ?_⟩
    have e : (⟨_, hr ▸ h.2⟩ : (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp) = h := Subtype.ext hr
    rw [e]
    exact h3
  · rintro ⟨hJ, hm, hc⟩
    exact OneLevel.mem_of_read H c x hJ hm hc

end Read

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Put

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

theorem put_mem_J0 (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) : rll_put n v x ∈ J0 hc n ST := by
  have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
  rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
  exact Subgroup.one_mem _

theorem red_put_off (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST)
    (w : SG) (hw : ¬ IsOver v w.1) : redG hc n ST SG ⟨rll_put n v x, hJ⟩ w = 1 :=
  rll_put_red n v x (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 hw

theorem red_put_at {gp : Fin 2 → ℕ} (G : GLoc F E hc.sig gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal)
    (w : SG) (e : (𝓞 E ⧸ w.1.asIdeal) ≃+* kv F v)
    (hcomp : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST) :
    ((redG hc n ST SG ⟨rll_put n v x, hJ⟩ w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).map e =
      redM F v (G.mat a v h 1 x) := by
  have hcomp' : ∀ (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z) := hcomp
  have hw := GlobalTheory.Mem.LevStd.gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have hgE := GlobalTheory.Mem.LevStd.gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
  have hG : G.mat a v h 1 x = ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) (rll_put n v x)) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [rll_put_self]; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
  rw [hG, ← h1]
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, hgE]
  rfl

end Put

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Coset

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

def cvec (p : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) : Fin (R.N j) → 𝓞 X.E ⧸ P.1.asIdeal :=
  redV P.1 ((qOf P.1 : X.E) • Classical.epsilon fun z => z ∈ cosetIn p P)

end Coset

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Fix

variable {K L : Type} [CommRing K] [CommRing L] {n : ℕ}

theorem fix_inv_iff (M : GL (Fin n) K) (c : Fin n → K) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = c ↔ (M : Matrix (Fin n) (Fin n) K) *ᵥ c = c := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem fix_map_iff (e : K ≃+* L) (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    M.map e *ᵥ (fun i => e (c i)) = (fun i => e (c i)) ↔ M *ᵥ c = c := by
  have h : M.map e *ᵥ (fun i => e (c i)) = fun i => e ((M *ᵥ c) i) := by
    have := RingHom.map_mulVec (e : K →+* L) M c
    funext i
    exact (this i).symm
  rw [h]
  constructor
  · intro h'
    funext i
    exact e.injective (congrFun h' i)
  · intro h'
    rw [h']

end Fix

end GlobalTheory.Mem.Col2.TypeRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMemChartLevelIffReductionFixesTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetReductionFixedIffResidues
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetReductionFixedIffResidues
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section CosetFixAux

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem redV_qsmul_of_mem {v : Sp E n} (hv : v ∈ stdAt E n P) : redV P (((qOf P : ℕ) : E) • v) = 0 := by
  funext i
  show redP P (((qOf P : ℕ) : E) * v i) = 0
  rw [reduction_mul (GlobalTheory.TopStep.intAt_nat _) (GlobalTheory.TopStep.mem_stdAt.1 hv i), GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_mul]

theorem mem_stdAt_iff_redV_qsmul (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {v : Sp E n}
    (hv : ((qOf P : ℕ) : E) • v ∈ stdAt E n P) : v ∈ stdAt E n P ↔ redV P (((qOf P : ℕ) : E) • v) = 0 := by
  refine ⟨redV_qsmul_of_mem, fun h => GlobalTheory.TopStep.mem_stdAt.2 fun i => ?_⟩
  have hi : IntAt P (((qOf P : ℕ) : E) * v i) := GlobalTheory.TopStep.mem_stdAt.1 hv i
  have h0 : redP P (((qOf P : ℕ) : E) * v i) = 0 := congrFun h i
  have := GlobalTheory.TopStep.intAt_div_of_redP hq hi h0
  rwa [mul_div_cancel_left₀ _ (GlobalTheory.TopStep.qOf_ne_zero (P := P))] at this

theorem redV_sub_of_mem {v w : Sp E n} (hv : v ∈ stdAt E n P) (hw : w ∈ stdAt E n P) :
    redV P (v - w) = redV P v - redV P w := by
  funext i
  exact GlobalTheory.TopStep.reduction_sub (GlobalTheory.TopStep.mem_stdAt.1 hv i) (GlobalTheory.TopStep.mem_stdAt.1 hw i)

theorem redV_qsmul_eq {a b : Sp E n} (hba : b - a ∈ stdAt E n P) (ha : ((qOf P : ℕ) : E) • a ∈ stdAt E n P) :
    redV P (((qOf P : ℕ) : E) • b) = redV P (((qOf P : ℕ) : E) • a) := by
  have hd : ((qOf P : ℕ) : E) • (b - a) ∈ stdAt E n P := by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hba _
  have hb : ((qOf P : ℕ) : E) • b ∈ stdAt E n P := by
    have := add_mem hd ha
    rwa [← smul_add, sub_add_cancel] at this
  have h1 := redV_sub_of_mem hb ha
  rw [← smul_sub, redV_qsmul_of_mem hba] at h1
  exact (sub_eq_zero.1 h1.symm)

end CosetFixAux

theorem setOf_sub_mem_eq_iff {V : Type} [AddCommGroup V] {A : Type} [Ring A] [Module A V] (M : Submodule A V) (a b : V) :
    {z | z - b ∈ M} = {z | z - a ∈ M} ↔ b - a ∈ M := by
  constructor
  · intro h
    have hb : b ∈ {z | z - b ∈ M} := by simp
    rw [h] at hb
    exact hb
  · intro h
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hz
      have := add_mem hz h
      rwa [sub_add_sub_cancel] at this
    · intro hz
      have := sub_mem hz h
      rwa [sub_sub_sub_cancel_right] at this

section CosetFix


set_option maxHeartbeats 1000000 in
theorem cosetIn_smul_eq_iff : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  intro X Pr R sel S mu cst u j hj p p' h h1 h2 P hP hdu
  classical
  obtain ⟨y, hy, hY⟩ := p.mem_ybSet hj
  have hyP : ((qOf P.1 : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
    have := (Submodule.mem_iInf _).1 hy P
    simpa [Submodule.mem_comap, hP] using this
  have hN : p'.1.1.deco.1.N = p.1.1.deco.1.N := by
    rw [h1]
    exact Submodule.map_id _
  have hY' : p'.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) p'.1.1.deco.1.N
      fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)} := by
    rw [h2, hN]
    exact hY
  have hc := GlobalTheory.BaseCosetPt.cosetIn_eq_of p P hP y _ (by simp [hP]) hY
  have hc' := GlobalTheory.BaseCosetPt.cosetIn_eq_of p' P hP y _ (by simp [hP]) hY'
  set w : Pr.vGs := ⟨P.1, hP⟩ with hw
  have hf : GlobalTheory.TopStep.IsLiftFr p.1.1.deco.1 w (frsF sel mu p.1.1 P) := by
    unfold frsF
    rw [dite_eq_left hP]
    exact GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
  have key : ∀ q : ChPt (R := R) sel mu u j,
      q = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 →
      GlobalTheory.TopStep.IsLiftFr (p.1.1.deco.1.act 1 h) w (q.deco.1.liftFr w) := by
    intro q hq
    have := GlobalTheory.TopStep.liftFr_spec q.deco.2 w
    subst hq
    exact this
  have hf' : GlobalTheory.TopStep.IsLiftFr (p.1.1.deco.1.act 1 h) w (frsF sel mu p'.1.1 P) := by
    unfold frsF
    rw [dite_eq_left hP]
    exact key _ h1
  set κ := GlobalTheory.TopStep.passFr 1 h hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL _ P.1 κ = h w := GlobalTheory.TopStep.redGL_passFr 1 h hf hf'
  set a := (frsF sel mu p.1.1 P).symm y with ha
  have hκa : κ.1 a = (frsF sel mu p'.1.1 P).symm y := by
    change (frsF sel mu p'.1.1 P).symm ((frsF sel mu p.1.1 P) a) = _
    rw [ha, LinearEquiv.apply_symm_apply]
  have hqa : ((qOf P.1 : ℕ) : X.E) • a ∈ stdAt X.E (R.N j) P.1 := by
    rw [ha, ← map_smul]
    exact GlobalTheory.BaseCosetPt.frsF_symm_mem p.1.1 P hyP
  have hqd : ((qOf P.1 : ℕ) : X.E) • (κ.1 a - a) ∈ stdAt X.E (R.N j) P.1 := by
    rw [smul_sub, ← map_smul]
    exact sub_mem (GlobalTheory.TopStep.glint_mem κ hqa) hqa
  have hcv : cvec p P = redV P.1 (((qOf P.1 : ℕ) : X.E) • a) := by
    unfold cvec
    have hm : ∃ z, z ∈ cosetIn p P := ⟨a, by rw [hc]; simp⟩
    have hε := Classical.epsilon_spec (p := fun z => z ∈ cosetIn p P) hm
    generalize Classical.epsilon (fun z => z ∈ cosetIn p P) = ε at hε ⊢
    rw [hc] at hε
    exact redV_qsmul_eq hε hqa
  rw [hc, hc', ← hκa, setOf_sub_mem_eq_iff, mem_stdAt_iff_redV_qsmul hdu.2 hqd, smul_sub, ← map_smul,
    redV_sub_of_mem (GlobalTheory.TopStep.glint_mem κ hqa) hqa, GlobalTheory.TopStep.redV_redGL κ hqa, hred, sub_eq_zero, hcv]

end CosetFix

end GlobalTheory.Mem.Col2.TypeRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetReductionFixedIffResiduesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  exact @GlobalTheory.Mem.Col2.TypeRead.cosetIn_smul_eq_iff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMemChartLevelIffReductionFixesTypePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


open GlobalTheory.Mem.Col2.TypeRead in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.typeRead_core : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ x, x ∈ F.levJ.Uloc v → (rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.U ↔ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF hfr h1 β0
  classical
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  obtain ⟨c, rfl⟩ := H.onto β0
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  haveI : NeZero (B.R.N (B.R.m - 1)) := ⟨by unfold Ranks.N; have := B.R.m_add_three_le_k; omega⟩
  have hX := (base_fields_primes_ok B X).1
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨wOf, hwOf, hwP, -⟩ := GlobalTheory.Mem.TypePrimes.primes_over_places B.fields (B.primes X) B.sp.cm hPr
  have hres := fun (a : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g a : 𝓞 B.host.F) ∈ v.asIdeal) =>
    GlobalTheory.SplitResidue.exists_residue_equiv B.host.F B.host.E v (wOf a v h).1 (F.gl.phi a v h)
    (B.fields.conjO ((B.primes X).piG a)) (fun t => congrArg Prod.fst (F.gl.sp_alg a v h t)) (by
      have := F.gl.sp_pi a v h
      rw [hF.gl.piG] at this
      exact this) (hwP a v h).1
  choose ρ e hρ hρe using hres
  let P0 : ∀ a v h, rowSG (B.primes X) I.sel (I.tup I.mu0) := fun a v h => ⟨(wOf a v h).1, Finset.mem_union_left _ (wOf a v h).2⟩
  refine ⟨fun a v h i => e a v h (cvec ((I.stp u I.mu0 (B.R.m - 1)).rep c) (P0 a v h) i), fun v hv x hx => ?_⟩

  obtain ⟨a, ha⟩ := hv
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  have hB := basePi_of_ok hX hPr u
  have hLb : F.levJ.Lb = baseLb B.host.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) := by
    ext y
    rw [← F.levJ_Lb h1 (chOf0 _ c)]
    refine (H.lb _ y).trans (Iff.trans ?_ (rll_mem_baseLb _ _ y).symm)
    simp only [baseL, Set.mem_setOf_eq]
    have hl : (lastIdx (B.R.N (B.R.m - 1))).1 + 1 = B.R.N (B.R.m - 1) := by
      have := NeZero.pos (B.R.N (B.R.m - 1)); simp only [lastIdx]; omega
    constructor
    · intro h
      choose r hr1 hr2 using h
      exact ⟨r, fun i => (hr1 i).symm, (hB.dvd _).2 (hr2 _ hl)⟩
    · rintro ⟨r, hr1, hr2⟩ i
      refine ⟨r i, (hr1 i).symm, fun hi => ?_⟩
      obtain rfl : i = lastIdx (B.R.N (B.R.m - 1)) := Fin.ext (by omega)
      exact (hB.dvd _).1 hr2
  have hxL : x ∈ levelVL B.sp.cm.sig (1 : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) B.host.E) v
      (baseLb B.host.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u)) := by
    have := F.levJ.Uloc_lev v hx
    have hgram' : gramN (I.rec7 l Z) ((I.rec7 l Z).R.m - 1) (Nat.sub_le _ _) = 1 := hgram
    rw [hLb] at this
    rw [hgram'] at this
    exact this
  have hT : v ∉ plUnder B.host.F ((B.primes X).vT u) := fun hvT => rls_T_notUnder hPr u v
      ((mem_plUnder_iff_norm B.sp.cm (rls_vT_iff hX hPr u) ((B.primes X).T u) (hPr.piT_norm u) v).1 hvT)
      ⟨(wOf a v ha).1, (wOf a v ha).2, (hwOf a v ha _).2 rfl⟩
  have hJ := put_mem_J0 B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) v hT x hxL
  have hUA := congruence_le_adelic_unitary B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) hJ
  refine (mem_iff_read H c _ hUA).trans ?_

  obtain ⟨b, hb⟩ : ∃ b, (c.1 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1)).1 = some b :=
    Option.isSome_iff_exists.1 (c.1.2.2 (by omega))
  have hgrp : levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1 = (I.idx I.mu0).levG (B.R.m - 1) b := by
    simp only [levGAt, hb, Option.elim]
  have hred := fun a' (h' : (B.host.g a' : 𝓞 B.host.F) ∈ v.asIdeal) => red_put_at B.sp.cm _ _ (B.primes X).vGs F.gl a' v h' (wOf a' v h') (e a' v h')
    (fun z => ⟨hρ a' v h' z ▸ (ρ a' v h' z).2, (congrArg (IsLocalRing.residue _) (Subtype.ext (hρ a' v h' z).symm)).trans (hρe a' v h' z)⟩) x hJ
  have hm0 : (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩)⁻¹ ∈
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1).grp := by
    rw [hgrp]
    refine inv_mem (fun w _ => ?_)
    by_cases hw : w = wOf a v ha
    · subst hw
      apply GlobalTheory.Mem.LastGrp.mem_levG_last _ _ _ _ _ _ _ hX hPr hI.sel_ok (hI.idx_ok I.mu0) (hI.sharp I.mu0) (B.R.m - 1) hmj b
        (wOf a v ha) _ (e a v ha)
      obtain ⟨M, hM, hMe⟩ := (F.glevJ.mem a v ha x (F.levJ.Uloc_lev v hx)).1 hx
      rw [hfr a v ha] at hMe
      have e2 : Matrix.GeneralLinearGroup.map (e a v ha).toRingHom
          (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩ (wOf a v ha)) = M := by
        apply Units.ext
        refine Eq.trans ?_ ((hred a ha).trans hMe.symm)
        rfl
      rw [e2]
      exact hM
    · have e1 := red_put_off B.sp.cm (B.R.N (B.R.m - 1)) _ (B.primes X).vGs v x hJ w (fun h => hw ((hwOf a v ha w).1 h))
      show _ ∈ ((I.idx I.mu0).levG (B.R.m - 1) b w).H
      erw [e1]
      exact one_mem _

  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact twistPrimes_trivialTuple_empty I.sel I.S
  have hvG : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right fun h => by simp [hQ] at h
  have hdeg : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 := fun P =>
    GlobalTheory.UnfoldTwoSided.degOne_bad hX hPr hI.sel_ok P
  have hcos := fun P => GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues hmj ((I.stp u I.mu0 (B.R.m - 1)).rep c)
    ((I.stp u I.mu0 (B.R.m - 1)).act c.1 (1, ⟨_, hm0⟩, 1) ((I.stp u I.mu0 (B.R.m - 1)).rep c))
    (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩)⁻¹ rfl (Set.image_id _) P (hvG P) (hdeg P)
  constructor
  · rintro ⟨hJ', hm', hc'⟩ j hv
    have hfix := (hcos (P0 j v hv)).1 (congrFun hc' _)
    have hfix' := (fix_inv_iff _ _).1 hfix
    have key := (fix_map_iff (e j v hv) _ _).2 hfix'
    rw [hfr j v hv]
    have hM : redM (I.rec7 l Z).host.F v (F.gl.mat j v hv 1 x) = _ := (hred j hv).symm
    rw [hM]
    exact key
  · intro hall
    refine ⟨hJ, hm0, funext fun P => (hcos P).2 ?_⟩
    refine (fix_inv_iff _ _).2 ?_
    by_cases hw : (⟨P.1, hvG P⟩ : (B.primes X).vGs) = wOf a v ha
    · have hP : P = P0 a v ha := Subtype.ext (show P.1 = (wOf a v ha).1 from congrArg Subtype.val hw)
      subst hP
      have h2 := hall a ha
      rw [hfr a v ha] at h2
      refine (fix_map_iff (e a v ha) _ _).1 ?_
      have hM : redM (I.rec7 l Z).host.F v (F.gl.mat a v ha 1 x) = _ := (hred a ha).symm
      rw [hM] at h2
      exact h2
    · have e1 := red_put_off B.sp.cm (B.R.N (B.R.m - 1)) _ (B.primes X).vGs v x hJ ⟨P.1, hvG P⟩
        (fun h => hw ((hwOf a v ha _).1 h))
      erw [e1]
      simp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMemChartLevelIffReductionFixesTypePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_mem_chartLevel_iff_reduction_fixes_typePrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ x, x ∈ F.levJ.Uloc v → (rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.U ↔ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  first | exact @GlobalTheory.Mem.Col2.TC.typeRead_core | exact GlobalTheory.Mem.Col2.TC.typeRead_core | (intros; apply GlobalTheory.Mem.Col2.TC.typeRead_core <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.chartLev_off_type : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → ∀ x, x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc v ↔ x ∈ F.levJ.Uloc v := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF h1 β0 v hv x
  have hi : B.R.m - 1 ≤ (I.rec7 l Z).R.m := Nat.sub_le _ _
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) hi).1
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  have hLbE : (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Lb = F.levJ.Lb := F.levJ_Lb h1 β0
  have hLb : ∀ x, x ∈ F.levJ.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N (B.R.m - 1)) (X.piT u) := by
    intro x
    rw [← hLbE]
    exact H.lb _ x
  have hL : F.levJ.Lb = rll_dLat ((I.rec7 l Z).R.N (B.R.m - 1)) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 F.levJ.Lb ?_
    rw [hF.piU]; exact hLb
  have hnb : v ∉ badG (I.rec7 l Z) := by
    rintro (h | h)
    · exact hv 0 h
    · exact hv 1 h
  by_cases hT : (((I.rec7 l Z).mem u).A.T : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · have e1 := GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev F.atT.piU (s F.atT.piU) rfl hpq hTp (hLbE.trans hL) v hT (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v hT) x
    have e2 := GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram F.levJ F.atT.piU (s F.atT.piU) rfl hpq hTp hL v hT (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v hT) x
    rw [hLbE] at e1
    exact e1.trans e2.symm
  · have e1 := (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc_hyp v hnb hT
    have e2 := F.levJ.Uloc_hyp v hnb hT
    rw [hLbE] at e1
    rw [e1, e2]
    exact Iff.rfl


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.chartLev_stab_vec : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) x, x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.Uloc v ↔ (x ∈ F.levJ.Uloc v ∧ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF hfr h1 β0
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  obtain ⟨w, hw⟩ := GlobalTheory.T.level_mem_chartLevel_iff_reduction_fixes_typePrime I hI hP l Z u F hF hfr h1 β0
  refine ⟨w, fun v x => ?_⟩
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  by_cases hv : ∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · have hput : ∀ (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f (badG (I.rec7 l Z))),
        x ∈ S.Uloc v ↔ rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ S.U := by
      intro S
      constructor
      · intro hx
        have hxU := S.Uloc_le v hx
        rw [hgram] at hxU
        refine (S.U_eq _).2 ⟨?_, fun v' => ?_⟩
        · have := rll_put_mem_UAd (I.rec7 l Z).sp.cm ((I.rec7 l Z).R.N (B.R.m - 1)) v hxU
          rw [hgram]; exact this
        · by_cases e : v' = v
          · subst e; rw [rll_put_self]; exact hx
          · rw [rll_put_ne _ v v' e]; exact one_mem _
      · intro hx
        have := ((S.U_eq _).1 hx).2 v
        rwa [rll_put_self] at this
    rw [hput]
    constructor
    · intro hx
      have hJ : rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ F.levJ.U := F.levJ_le h1 β0 hx
      have hxJ : x ∈ F.levJ.Uloc v := by
        have := ((F.levJ.U_eq _).1 hJ).2 v
        first
          | (convert this using 2; exact (rll_put_self _ v x).symm)
          | exact (congrArg (· ∈ F.levJ.Uloc v) (rll_put_self ((I.rec7 l Z).R.N (B.R.m - 1)) v x)).mp this
          | exact (rll_put_self ((I.rec7 l Z).R.N (B.R.m - 1)) v x) ▸ this
      exact ⟨hxJ, (hw v hv x hxJ).1 hx⟩
    · rintro ⟨hxJ, hs⟩
      exact (hw v hv x hxJ).2 hs
  · push_neg at hv
    rw [GlobalTheory.Mem.Col2.TC.chartLev_off_type I hI hP l Z u F hF h1 β0 v (fun j => hv j) x]
    exact ⟨fun h => ⟨h, fun j hj => absurd hj (hv j)⟩, fun h => h.1⟩

end
