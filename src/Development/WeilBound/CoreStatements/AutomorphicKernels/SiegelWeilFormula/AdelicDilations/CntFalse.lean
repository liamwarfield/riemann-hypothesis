module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CntFalse
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem T_sub (d : SD σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  funext X
  simp only [SD.T, Pi.sub_apply]
  rw [← map_sub]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_sub]

theorem vac_tens {d : SD σ} (R : RD d) (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.vac) :
    ∃ Ψ ∈ R.away w, f = R.tens w (fP 1) Ψ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, hg, rfl⟩ := hf
    refine ⟨fun X => (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2,
      Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩, ?_⟩
    funext X
    simp only [RD.tens]
    rw [← mul_assoc, Finset.mul_prod_erase _ (fun w' => fP 1 (R.loc w' X)) (Finset.mem_univ w)]
  | zero => exact ⟨0, zero_mem _, by funext X; simp [RD.tens]⟩
  | add f f' _ _ h h' =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    obtain ⟨Ψ', hΨ', rfl⟩ := h'
    exact ⟨Ψ + Ψ', add_mem hΨ hΨ', by funext X; simp [RD.tens, mul_add]⟩
  | smul a f _ h =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    exact ⟨a • Ψ, Submodule.smul_mem _ a hΨ, by funext X; simp [RD.tens]; ring⟩

theorem ndA (H : Hyps) {d : SD σ} (R : RD d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) :
    ∀ L ∈ d.lamSet, L (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) = 0 := by
  intro L hL
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩ := hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  show fc d.B.ψ d.b nb lam 𝓖 (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) T x = 0
  rw [← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _

theorem cnt_true (m : ℕ) : cnt (fun _ : Fin m => true) true = m := by
  simp [cnt]

theorem cnt_false (m : ℕ) : cnt (fun _ : Fin m => true) false = 0 := by
  simp [cnt]

theorem exists_isHolW_iteratedDeriv (H : Hyps) {d : SD σ} (R : RD d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
    (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (w : InfinitePlace F) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∃ (pp qq : ℕ) (e : ℤ), (pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) ∧
      ∀ g, IsHolW pp qq e fun y => iteratedDeriv j (Ê · (g * R.ι w y)) (s0 d.m d.n) := by
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := H.auxEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  obtain ⟨Ψ, hΨ, hTΨ⟩ := vac_tens R w _ hv
  obtain ⟨Lop, hLop⟩ := H.locOpEx F E σ d R w
  obtain ⟨φ, hφ⟩ := H.liftEx F E σ d R w Ψ hΨ
  obtain ⟨sL, ρ, pp, qq, e, -, hLD, hsL, -⟩ := H.locInst F E σ d R w Lop hLop
  have hΦφ : φ 1 = Φ := by
    have h0 := (H.tAll.1 F E σ d).2.2 (φ 1 - Φ) (sub_mem (hφ 1).1 hΦ) (by rw [T_sub, (hφ 1).2, hTΨ, sub_self])
    exact sub_eq_zero.1 h0
  have hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m := by
    rcases hLD.sign with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · left; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
  refine ⟨pp, qq, e, hpq, ?_⟩
  haveI := hTG; haveI := hLC; haveI := hT2; haveI := hSC
  refine H.holLead d.m d.n pp qq e d.ok.hm hmn hpq d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht (d.sec0 Φ)
    (R.cont w) ?_ U p Ê t hUo hR hs hd hcont (fun z hz => ⟨(hfar z hz).1, fun g => (hfar z hz).2 g⟩) j hlow ?_
  · intro g
    obtain ⟨x, y, c, r, hr, hg, hxy⟩ := H.gSplit F E σ d R w Lop hLop Ψ hΨ φ hφ g
    refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hxy y').1, ?_⟩⟩
    rw [← hΦφ, (hxy y').2 1, ← hsL, hLD.vac]
  · intro ψ hψ nb hnb g a b
    exact H.lamSing F E σ d R w _ hAc hAi (ndA H R hmn hΦ hv hE j hj) ψ hψ nb hnb g a b

end PositivityTheory.SiegelWeilFormula.AStep

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace COneB

variable {d : SD σ} (L : LD d)

def Nu (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩

theorem Nu_mul (u v : Fin L.n → AE F E) : Nu L u * Nu L v = 0 := by
  simp only [Nu, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  apply Matrix.single_mul_single_of_ne
  exact em_ne L _

theorem Nu_add (u v : Fin L.n → AE F E) : Nu L (u + v) = Nu L u + Nu L v := by
  simp only [Nu, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

theorem Nu_cont : Continuous (Nu L) := by
  have e : Nu L = fun u => ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; simp only [Nu, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const


omit L in
theorem unit_frame (d : SD σ) (x : d.G) : ∃ e : AE F E,
    (inFrame d.b x)ᵀ * Matrix.fromBlocks 0 1 (e • 1) 0 * (inFrame d.b x).map (cA σ) = Matrix.fromBlocks 0 1 (e • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨((ε : ℤ) : AE F E), ?_⟩
  have hF := kfour.frameEq_adelic (F := F) (Y := d.Y) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]

omit L in
theorem blk_unit (d : SD σ) (x : d.G) (a a' : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a 0 0 a') : aᵀ * a'.map (cA σ) = 1 := by
  obtain ⟨e, he⟩ := unit_frame d x
  rw [hx] at he
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one] at he
  have := (Matrix.fromBlocks_inj.1 he).2.1
  exact this

omit L in
theorem cA_cA_mat (d : SD σ) {p q : Type} (M : Matrix p q (AE F E)) : (M.map (cA σ)).map (cA σ) = M := by
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good d.ok.good
  ext i j; simp [kfour.cA_cA' σ hσ]

theorem uM_frame {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (1 + Nu L u) 0 0 (((1 - Nu L u)ᵀ).map (cA σ)) := by
  obtain ⟨a', ha'⟩ := hu.1 u
  have ha : inFrame d.b (uM u) = Matrix.fromBlocks (1 + Nu L u) 0 0 a' := ha'
  rw [ha]
  have h1 := blk_unit d _ _ _ ha
  have h2 : (1 - Nu L u)ᵀ * (1 + Nu L u)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Nu_mul, sub_zero,
      sub_add_cancel, Matrix.transpose_one]
  have h3 : a'.map (cA σ) = (1 - Nu L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - Nu L u)ᵀ * (1 + Nu L u)ᵀ) * a'.map (cA σ) := by rw [h2, Matrix.one_mul]
      _ = (1 - Nu L u)ᵀ * ((1 + Nu L u)ᵀ * a'.map (cA σ)) := by rw [Matrix.mul_assoc]
      _ = (1 - Nu L u)ᵀ := by rw [h1, Matrix.mul_one]
  have h4 : a' = ((1 - Nu L u)ᵀ).map (cA σ) := by rw [← h3, cA_cA_mat d]
  rw [h4]

theorem uM_add {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  apply kfour.inFrame_injective d.b
  rw [SiegelEisensteinSeries.Grp.inFrame_mul, uM_frame L hu, uM_frame L hu, uM_frame L hu, Matrix.fromBlocks_multiply]
  have e1 : (1 + Nu L u) * (1 + Nu L v) = 1 + Nu L (u + v) := by
    rw [Nu_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Nu_mul, add_zero]
    abel
  have e2 : ((1 - Nu L u)ᵀ).map (cA σ) * ((1 - Nu L v)ᵀ).map (cA σ) = ((1 - Nu L (u + v))ᵀ).map (cA σ) := by
    have hm := Matrix.map_mul (L := (1 - Nu L u)ᵀ) (M := (1 - Nu L v)ᵀ) (f := (cA σ).toRingHom)
    erw [← hm]
    rw [← Matrix.transpose_mul, Nu_add, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Nu_mul,
      sub_zero]
    congr 2
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]

theorem uM_zero {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : uM 0 = 1 := by
  have h := uM_add L hu 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem uM_neg {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (uM u)⁻¹ = uM (-u) := by
  have h := uM_add L hu (-u) u
  rw [neg_add_cancel, uM_zero L hu] at h
  exact (eq_inv_of_mul_eq_one_left h.symm).symm

theorem uM_cont {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : Continuous uM := by
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hmat : Continuous fun u => mat2 (uM u) := by
    have e : (fun u => mat2 (uM u)) = fun u => incM F d.b.1 * Matrix.fromBlocks (1 + Nu L u) 0 0
        (((1 - Nu L u)ᵀ).map (cA σ)) * incM F (d.b⁻¹).1 := by
      funext u; rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b, uM_frame L hu]
    rw [e]
    refine (continuous_const.matrix_mul (Continuous.matrix_fromBlocks (continuous_const.add (Nu_cont L))
      continuous_const continuous_const ?_)).matrix_mul continuous_const
    exact ((continuous_const.sub (Nu_cont L)).matrix_transpose).matrix_map hcA
  have hinv : Continuous fun u => mat2 (uM u)⁻¹ := by
    simp only [uM_neg L hu]
    exact hmat.comp continuous_neg
  refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
  exact Units.continuous_iff.2 ⟨hmat, hinv⟩

theorem ratV_cocompact : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ u, ∃ r ∈ L.ratV, r + u ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi (fun _ => C), isCompact_univ_pi (fun _ => hC), fun u => ?_⟩
  choose x hx using fun j => hCx (u j)
  refine ⟨GlobalTheory.ThK.incV F x, AddSubgroup.subset_closure ⟨x, rfl⟩, fun j _ => ?_⟩
  simpa [GlobalTheory.ThK.incV] using hx j

end COneB

end PositivityTheory.SiegelWeilFormula.AStep

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneAdr
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def adr [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : AF F :=
  ((fun u => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm (if u = w then r else 1),
    (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem adr_fst [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) :
    (adr w r).1 u = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).symm (if u = w then r else 1) := rfl

theorem adr_snd [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : (adr (F := F) w r).2 = 1 := rfl

theorem adr_mul [IsTotallyReal F] (w : InfinitePlace F) (r s : ℝ) : adr w r * adr w s = adr (F := F) w (r * s) := by
  refine Prod.ext (funext fun u => ?_) (mul_one _)
  show (adr w r).1 u * (adr w s).1 u = (adr w (r * s)).1 u
  rw [adr_fst, adr_fst, adr_fst, ← map_mul]
  congr 1
  split_ifs <;> simp

theorem adr_one [IsTotallyReal F] (w : InfinitePlace F) : adr (F := F) w 1 = 1 := by
  refine Prod.ext (funext fun u => ?_) rfl
  show (adr w 1).1 u = 1
  rw [adr_fst, ite_self, map_one]

theorem ext_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) :
    InfinitePlace.Completion.extensionEmbedding u ((adr w r).1 u) = ((if u = w then r else 1 : ℝ) : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal u), adr_fst]
  congr 1
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal u)).apply_symm_apply _

theorem finOne_adr [IsTotallyReal F] (w : InfinitePlace F) (r : ℝ) : finOne F * adr w r = finOne F := by
  refine Prod.ext ?_ (mul_one _)
  show (finOne F).1 * (adr w r).1 = (finOne F).1
  have h0 : (finOne F).1 = 0 := rfl
  rw [h0, zero_mul]

end PositivityTheory.SiegelWeilFormula.AStep

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def adrU [IsTotallyReal F] (w : InfinitePlace F) (τ : ℝ) : (AF F)ˣ :=
  ⟨adr w (Real.exp τ), adr w (Real.exp (-τ)),
    by rw [adr_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, adr_one],
    by rw [adr_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, adr_one]⟩

theorem evInf_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) : evInf F u (adr w r) = (adr w r).1 u := rfl

theorem evFin_adr [IsTotallyReal F] (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (r : ℝ) :
    evFin F v (adr w r) = 1 := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (adr w r).2 = 1
  rw [adr_snd, map_one]

theorem norm_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) : ‖(adr w r).1 u‖ = |if u = w then r else 1| := by
  rw [← (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding u).norm_map_of_map_zero (map_zero _),
    ext_adr, Complex.norm_real, Real.norm_eq_abs]

theorem piInf_adr (h : IsCMExt F E σ) (τ' : ∀ w : InfinitePlace F, EmbOver E w) (w u : InfinitePlace F) (r : ℝ) :
    haveI := h.1
    piInf (τ' u) (algebraMap (AF F) (AE F E) (adr w r)) = ((if u = w then r else 1 : ℝ) : ℂ) := by
  haveI := h.1
  show GlobalTheory.AdelicU.infEmb (τ' u) (GlobalTheory.AdelicU.compInf F E u (algebraMap (AF F) (AE F E) (adr w r))) = _
  rw [Algebra.TensorProduct.algebraMap_apply]
  show GlobalTheory.AdelicU.infEmb (τ' u)
    (Algebra.TensorProduct.map (GlobalTheory.AdelicU.evInf F u) (AlgHom.id F E) (adr w r ⊗ₜ[F] (1 : E))) = _
  rw [Algebra.TensorProduct.map_tmul, evInf_adr, AlgHom.id_apply]
  simp only [GlobalTheory.AdelicU.infEmb, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  exact ext_adr w u r

theorem finOne_smul_adr (h : IsCMExt F E σ) (w : InfinitePlace F) (r : ℝ) :
    haveI := h.1
    finOne F • algebraMap (AF F) (AE F E) (adr w r) = finOne F • (1 : AE F E) := by
  haveI := h.1
  rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, finOne_adr, mul_one]

theorem absE_adrU (h : IsCMExt F E σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := h.1
    ((absE F E (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℝ≥0) : ℝ) = Real.exp (2 * τ) := by
  haveI := h.1
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) = 1 := by
    intro v
    have h1 : GlobalTheory.Doubling.unitFin F E v
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) = 1 := by
      apply Units.ext
      show GlobalTheory.AdelicU.compFin F E v (algebraMap (AF F) (AE F E) (adr w (Real.exp τ))) = 1
      rw [Algebra.TensorProduct.algebraMap_apply]
      show Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin F v) (AlgHom.id F E)
        (adr w (Real.exp τ) ⊗ₜ[F] (1 : E)) = 1
      rw [Algebra.TensorProduct.map_tmul, evFin_adr, AlgHom.id_apply, ← Algebra.TensorProduct.one_def]
    rw [h1, map_one]
  have hinf : ∀ u, (GlobalTheory.Doubling.absEw F E u (GlobalTheory.Doubling.unitInf F E u
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) : ℝ) =
      |if u = w then Real.exp τ else 1| ^ 2 := by
    intro u
    have hval : ((GlobalTheory.Doubling.unitInf F E u
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : (TensorProduct F u.Completion E)ˣ) :
          TensorProduct F u.Completion E) =
        algebraMap u.Completion (TensorProduct F u.Completion E) ((adr w (Real.exp τ)).1 u) := by
      show GlobalTheory.AdelicU.compInf F E u (algebraMap (AF F) (AE F E) (adr w (Real.exp τ))) = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
      show Algebra.TensorProduct.map (GlobalTheory.AdelicU.evInf F u) (AlgHom.id F E)
        (adr w (Real.exp τ) ⊗ₜ[F] (1 : E)) = _
      rw [Algebra.TensorProduct.map_tmul, evInf_adr, AlgHom.id_apply]
      rfl
    have hmult : u.mult = 1 := by
      rw [NumberField.InfinitePlace.mult, if_pos (NumberField.IsTotallyReal.isReal u)]
    show ((‖Algebra.norm u.Completion ((GlobalTheory.Doubling.unitInf F E u
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : (TensorProduct F u.Completion E)ˣ) :
          TensorProduct F u.Completion E)‖₊ ^ u.mult : ℝ≥0) : ℝ) = _
    rw [hval, hmult, pow_one, Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1, coe_nnnorm,
      norm_pow, norm_adr]
  show (((∏ u, GlobalTheory.Doubling.absEw F E u (GlobalTheory.Doubling.unitInf F E u
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)))) *
      ∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) : ℝ≥0) : ℝ) = _
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one, NNReal.coe_prod, Finset.prod_eq_single w]
  · rw [hinf, if_pos rfl, Real.abs_exp, sq, ← Real.exp_add, two_mul]
  · intro b _ hb
    rw [hinf, if_neg hb, abs_one, one_pow]
  · intro hw
    exact absurd (Finset.mem_univ w) hw

theorem chi_adrU (d : SD σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := d.cm.1
    (d.χ (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℂ) = 1 := by
  haveI := d.cm.1
  have hmem : adrU w τ ∈ (Units.map (Algebra.norm (AF F) (S := AE F E))).range := by
    refine ⟨Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w (τ / 2)), ?_⟩
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (TensorProduct F (AF F) E) (adr w (Real.exp (τ / 2)))) =
      adr w (Real.exp τ)
    rw [Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) d.bs), Fintype.card_fin, pow_two,
      adr_mul, ← Real.exp_add, add_halves]
  have h2 := d.ok.res (adrU w τ)
  split_ifs at h2 with hc
  · exact h2
  · exact absurd (Subgroup.mem_sup_right hmem) hc

end PositivityTheory.SiegelWeilFormula.AStep

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionEqThetaZero
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace COne

theorem om_sch (d : SD σ) (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h

theorem T_zero (d : SD σ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  have := d.ok.dbl.kill 0 Φ h
  have e2 : (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * (diagCols (Fin d.n) : Matrix _ _ (AE F E))ᵀ = 0 := Matrix.zero_mul _
  have e3 : (0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ = 0 := Matrix.zero_mul _
  erw [e2] at this
  show d.l (d.dd.rho d.B.ψ ((0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ) Φ) = _
  rw [e3]
  exact this

theorem section_eq_theta_zero (d : SD σ) {Φ : d.Fn} (h : Φ ∈ d.sch) (x : d.G) : d.sec0 Φ x = d.T (d.om x Φ) 0 :=
  (T_zero d (om_sch d x h)).symm

theorem T_smul (d : SD σ) (c : ℂ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • Φ) X = c * d.T Φ X := by
  unfold SD.T Darboux.rho
  have : schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) (c • Φ) = c • schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) Φ := by
    funext y; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, map_smul, smul_eq_mul]

theorem orb_smul (d : SD σ) (T : nF σ d.Y d.b) (c : ℂ) (Φ : d.Fn) : d.orb T (c • Φ) = c * d.orb T Φ := by
  unfold SD.orb
  simp only [T_smul, tsum_mul_left]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _

theorem Ln {d : SD σ} (L : LD d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    (Equiv.ofInjective L.em L.inj).trans (Equiv.subtypeEquivRight fun i => (L.rng i).symm)
  have h1 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h1
  have := L.i₀.isLt
  omega

theorem cosetSum_factor {G : Type} [Group G] (Pp Γ : Subgroup G) (Fn h : G → ℂ) (K : ℂ) (g₀ : G)
    (hF : ∀ g, Fn g = K * h (g * g₀)) (g : G) :
    GlobalTheory.Eis.cosetSum Pp Γ Fn g = K * GlobalTheory.Eis.cosetSum Pp Γ h (g * g₀) := by
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, hF, mul_assoc]
  exact tsum_mul_left

theorem ht_cpow (r a : ℝ) (hr : 0 < r) (w : ℂ) :
    (((r * a).toNNReal : ℝ) : ℂ) ^ w = (r : ℂ) ^ w * (((a.toNNReal : ℝ) : ℂ)) ^ w := by
  rw [Real.toNNReal_mul hr.le, NNReal.coe_mul, Real.coe_toNNReal _ hr.le, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (NNReal.coe_nonneg _)]

theorem hv_shift (W : ℂ → ℂ) (s₀ a v c : ℂ) (r : ℝ) (hr : 0 < r) (hW : HolValueAt W (s₀ + a) v) :
    HolValueAt (fun z => (c * (r : ℂ) ^ (z - s₀)) * W (z + a)) s₀ (c * v) := by
  obtain ⟨H, hext, han, hval⟩ := hW
  have h1 := hext.comp_add
  have hK : AnalyticOnNhd ℂ (fun z => c * (r : ℂ) ^ (z - s₀)) Set.univ := fun z _ =>
    analyticAt_const.mul (analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) (Complex.ofReal_mem_slitPlane.2 hr))
  have h2 : IsExtAt (fun z => c * (r : ℂ) ^ (z - s₀)) s₀ (fun z => c * (r : ℂ) ^ (z - s₀)) :=
    (isMerExt_self isRightDomain_univ hK.meromorphicOn).isExtAt (Set.mem_univ _)
  refine ⟨_, h2.mul h1, ?_, ?_⟩
  · exact (hK s₀ (Set.mem_univ _)).mul (han.comp_of_eq (analyticAt_id.add analyticAt_const) rfl)
  · simp [hval]

theorem fcVal (H : Hyps) {d' : SD σ} (R'' : RD d') (hMV : MainV 2 R'') {Ψ : d'.Fn} (hΨ : Ψ ∈ d'.sch)
    (hv : d'.T Ψ ∈ R''.vac) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d'.Y) d'.b nb lam 𝓖) (T : nF σ d'.Y d'.b)
    (g : d'.G) :
    HolValueAt (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z) T g) (s0 d'.m d'.n)
      (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
  have hK := H.polyKFin F E σ d' R'' Ψ hΨ ((H.vacK F E σ d' R'').2.1 hv)
  have hsec := H.secK F E σ d' Ψ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d' _ _ hsec (s0 d'.m d'.n)
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hadd, hbd⟩ := fcAll d' hc T g
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d'.Y) (fun f => fc d'.B.ψ d'.b nb lam 𝓖 f T g) hadd hbd U Ê hUo hd hcont hinv
  have hpt : ∀ g', ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (Ê · g') (s0 d'.m d'.n) =
      iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * d'.I Ψ g') := fun g' =>
    ordVal U p (Ê · g') (fun z => d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g') t _ (2 * d'.I Ψ g') hUo hR hs hp (hd g')
      (fun z hz => (hfar z hz).2 g') (hMV Ψ hΨ hv g')
  have hsm : ∀ (c : ℂ) (φ : d'.G → ℂ), fc d'.B.ψ d'.b nb lam 𝓖 (fun g' => c * φ g') T g =
      c * fc d'.B.ψ d'.b nb lam 𝓖 φ T g := by
    intro c φ; simp only [fc, mul_assoc]; exact integral_const_mul _ _
  have hder : ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n),
      iteratedDeriv i (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (Ê z) T g) (s0 d'.m d'.n) =
        iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
    intro i hi
    rw [hComm _ hs i]
    have : (fun g' => iteratedDeriv i (Ê · g') (s0 d'.m d'.n)) =
        fun g' => (iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * 2) * d'.I Ψ g' :=
      funext fun g' => by rw [hpt g' i hi]; ring
    rw [this, hsm]; ring
  refine wrap U p _ _ t _ _ hUo hR hs hp hDiff (fun z hz => ?_) (fun i hi => ?_) (hder _ le_rfl)
  · have e1 : Ê z = fun g' => p.eval z * d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g' := funext (hfar z hz).2
    rw [e1, hsm]
  · rw [hder i hi.le, pderiv_lt p _ i hi, zero_mul]

end COne

section Deg

variable (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (R' : RD L.sd) (hmn : d.m < d.n) (hIH : MainV 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)


include H hIH hΦ hv in
theorem cOneVal_pf {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (x : d.G) :
    HolValueAt (fun z => cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) (s0 d.m d.n)
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) := by
  obtain ⟨q, g₀, k, r, c, hk, hx, hr, ha, hTq⟩ := H.iwaQ F E σ d L x
  have hΦk : d.om k Φ ∈ d.sch := COne.om_sch d k hΦ
  have hvk : d.T (d.om k Φ) ∈ R.vac := (H.vacK F E σ d R).1 Φ hΦ hv k hk
  obtain ⟨Φ', hres, hv'⟩ := (H.vacK F E σ d R).2.2 L R' _ hΦk hvk
  have hΦ' : Φ' ∈ L.sd.sch := hres.1
  have hres0 : ∀ g : L.sd.G, L.sd.T (L.sd.om g Φ') 0 = d.T (d.om (L.j g) (d.om k Φ)) 0 := by
    intro g
    have := L.res _ hΦk Φ' hΦ' hres.2 g 0 (fun a => rfl)
    rwa [Matrix.submatrix_zero] at this
  have hf : ∀ g' : L.sd.G, d.sec0 Φ (L.j g' * x) = c * L.sd.sec0 Φ' (g' * g₀) := by
    intro g'
    have hΨ : d.om (L.j g₀) (d.om k Φ) ∈ d.sch := COne.om_sch d _ hΦk
    rw [COne.section_eq_theta_zero d hΦ, COne.section_eq_theta_zero L.sd hΦ', hx]
    have e : d.om (L.j g' * (q * L.j g₀ * k)) Φ = d.om (L.j g' * q) (d.om (L.j g₀) (d.om k Φ)) := by
      simp only [map_mul, mul_assoc]; rfl
    rw [e, hTq _ hΨ g' 0 (fun a => rfl), hres0 (g' * g₀)]
    congr 2
    simp only [map_mul]; rfl
  have hs' : s0 d.m L.n = s0 d.m d.n + 1 / 2 := by
    unfold s0; rw [← COne.Ln L]; push_cast; ring
  have hid : ∀ z, cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x = (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2)) T' g₀ := by
    intro z
    have ex : z + 1 / 2 - s0 d.m L.n = z - s0 d.m d.n := by rw [hs']; ring
    have hF : ∀ g' : L.sd.G, ((d.Ht (L.j g' * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g' * x) =
        (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (((L.sd.Ht (g' * g₀) : ℝ) : ℂ) ^ (z + 1 / 2 - s0 d.m L.n) *
          L.sd.sec0 Φ' (g' * g₀)) := by
      intro g'
      rw [hf g', ex]
      have e1 : ((d.Ht (L.j g' * x) : ℝ) : ℂ) = ((((r * L.a (g' * g₀)).toNNReal : ℝ)) : ℂ) := by
        simp only [SD.Ht, ha g']
      rw [e1, COne.ht_cpow r _ hr]
      simp only [SD.Ht]
      ring
    have hcs : GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) *
        d.sec0 Φ (L.j g * x)) = fun g => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
          L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2) (g * g₀) :=
      funext fun g => COne.cosetSum_factor _ _ _ _ _ g₀ hF g
    unfold cOne
    rw [hcs]
    simp only [fc, mul_one, mul_assoc, integral_const_mul]
  have hW := COne.fcVal H R' hIH hΦ' hv' hc' T' g₀
  rw [hs'] at hW
  have hsh := COne.hv_shift _ (s0 d.m d.n) (1 / 2) _ c r hr hW
  have hv1 : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = c * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.I Φ') T' g₀ := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x, H.thetaCoef F E σ L.sd Φ' hΦ' nb' lam' 𝓖' hc' T' g₀]
    rw [(H.orbRes F E σ d).2 L T T' hT (d.om x Φ) (c • L.sd.om g₀ Φ') ⟨?_, ?_⟩, COne.orb_smul]
    · exact Submodule.smul_mem _ _ (COne.om_sch L.sd g₀ hΦ')
    · intro X hX
      rw [COne.T_smul]
      have h1 := L.res _ hΦk Φ' hΦ' hres.2 g₀ X hX
      have hΨ := COne.om_sch d (L.j g₀) hΦk
      have h2 := hTq _ hΨ 1 X hX
      simp only [map_one, one_mul, Module.End.one_apply] at h2
      have h1' : L.sd.T (L.sd.om g₀ Φ') (X.submatrix id L.em) = d.T (d.om (L.j g₀) (d.om k Φ)) X := h1
      rw [h1', hx]
      have e : d.om (q * L.j g₀ * k) Φ = d.om q (d.om (L.j g₀) (d.om k Φ)) := by simp only [map_mul]; rfl
      rw [e, h2]
  have hfun : (fun z => cOne d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) = fun z => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      (fun z => fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m d.n + 1 / 2) z) T' g₀) (z + 1 / 2) := by
    funext z; rw [hid z, hs']
  rw [hfun, hv1]
  convert hsh using 1
  ring

end Deg

end PositivityTheory.SiegelWeilFormula.AStep

end
end
