module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNegatedSpaceDiscreteSeriesModelTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutCuspOfMemCusp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}


open Classical in
def givenFn (B : Frames G) (t : T) (Φ : G.Datum) (e : AE D) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) : ℂ :=
  if IsHalf e x then ∏ w ∈ locPl G t, givenDatum t w B Φ (edgeOf a) (locArg B t w a x) else 0

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem tensor_given (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (y : ∀ j : Fin D.R.m, WO (G.pS (Arrow.down t 0 j).pair) (G.pT (Arrow.down t 0 j).pair))
    (x : ∀ i : Fin D.R.m, WO (G.pS (Arrow.right (T := T) i 0).pair) (G.pT (Arrow.right (T := T) i 0).pair)) :
    (givenStage t w B Φ).tensor (pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x))) =
      (∏ j : Fin D.R.m, givenDatum t w B Φ (edgeOf (.down t 0 j)) (locArg B t w (.down t 0 j) (y j))) *
        ∏ i : Fin D.R.m, givenDatum t w B Φ (edgeOf (.right i 0)) (locArg B t w (.right i 0) (x i)) := by
  have pathArgs_down (i : ℕ) : ∀ (n : ℕ) (y : ∀ j : Fin n, WO (G.pS (Arrow.down t i j).pair) (G.pT (Arrow.down t i j).pair))
      (j : ℕ) (h : j < n), pathArgs B t w (downPath t i n) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n y) (.theta i j) =
        locArg B t w (.down t i j) (y ⟨j, h⟩) := by
    intro n
    induction n with
    | zero => intro y j h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro y j h
      have hc := GlobalTheory.OppConv.pathArgs_comp B t w (Path.one (.down t i n)) ((), y (Fin.last n)) (.theta i j) (downPath t i n)
        (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t i n fun j => y j.castSucc)
      by_cases hj : j < n
      · exact (hc.1 ((GlobalTheory.OppConv.mem_edges_down t i n _).2 ⟨j, hj, rfl⟩)).trans (ih _ j hj)
      · have hj' : j = n := by omega
        subst hj'
        refine (hc.2 fun h' => ?_).trans ?_
        · obtain ⟨k, hk, hk'⟩ := (GlobalTheory.OppConv.mem_edges_down t i j _).1 h'
          simp only [GlobalTheory.SplitFlip.Edge.theta.injEq] at hk'
          omega
        · exact dif_pos rfl
  have hθ : ∀ j : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.theta 0 j) = locArg B t w (.down t 0 j) (y j) := by
    intro j
    refine ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.theta 0 j) (rowPath T 0 D.R.m) _).2 ?_).trans
      (pathArgs_down 0 D.R.m y j j.2)
    rw [GlobalTheory.OppConv.mem_edges_row]
    rintro ⟨i, -, h⟩
    cases h
  have hex : ∀ i : Fin D.R.m, pathArgs B t w (givenPath t D.R.m)
      (Path.Fam.append (q := rowPath T 0 D.R.m) (downFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) t 0 D.R.m y)
        (rowFam (S := fun a => WO (G.pS a.pair) (G.pT a.pair)) 0 D.R.m x)) (.ex i 0) = locArg B t w (.right i 0) (x i) :=
    fun i => ((GlobalTheory.OppConv.pathArgs_comp B t w (downPath t 0 D.R.m) _ (.ex i 0) (rowPath T 0 D.R.m) _).1
      ((GlobalTheory.OppConv.mem_edges_row 0 D.R.m _).2 ⟨i, i.2, rfl⟩)).trans (GlobalTheory.OppConv.pathArgs_row B t w 0 D.R.m x i i.2)
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b _).prod = _
  simp only [GlobalTheory.SplitFlip.givenPath, List.map_append, List.prod_append, List.map_map, List.map_reverse, List.prod_reverse]
  have hl : ∀ f : ℕ → ℂ, ((List.range D.R.m).map f).prod = ∏ i : Fin D.R.m, f i := fun f => by
    rw [← Finset.prod_range, Finset.prod_eq_multiset_prod]; rfl
  rw [hl, hl]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp_apply]
    rw [hθ j]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_apply]
    rw [hex i]
    rfl

end GlobalTheory.FlipStart

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem repFin_of (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (Φ : G.Datum) (e : AE D) (he : IsIdemSum e (locPl G t)) (c : Fin D.R.m → ℂ) (z : ℂ) (hz : z * ∏ j, c j = 1)
    (hcol : ∀ j : Fin D.R.m, IsLocVec W (.mu t 0 j) e (ρ.vT 0 j) (c j • givenFn B t Φ e (.down t 0 j)) (f j))
    (hrow : ∀ i : Fin D.R.m, IsLocVec W (.chi i 0) e (ρ.vX i 0) (givenFn B t Φ e (.right i 0)) (W.cosVec i (Φ i))) :
    RepFin B ρ t (givenPath t D.R.m) (Finsupp.single (givenFin W t f Φ) z) (fun w => (givenStage t w B Φ).tensor) := by
  have append_surj {S : Arrow T → Type} {X Y : Node} (p : Path T X Y) :
      ∀ {Z : Node} (q : Path T Y Z) (f : (p.comp q).Fam S), ∃ d e, Path.Fam.append (q := q) d e = f := by
    intro Z q
    induction q with
    | nil => intro f; exact ⟨f, (), rfl⟩
    | snoc a q ih =>
      intro f
      obtain ⟨d, e, h⟩ := ih f.1
      refine ⟨d, (e, f.2), ?_⟩
      show (Path.Fam.append (q := q) d e, f.2) = f
      rw [h]
      rfl
  have rowFam_surj {S : Arrow T → Type} (j : ℕ) : ∀ n (d : (rowPath T j n).Fam S), ∃ f, rowFam j n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun i => i.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨f, hf⟩ := ih d.1
      refine ⟨Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f, ?_⟩
      show (rowFam j n (fun i => Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f i.castSucc),
        Fin.lastCases (motive := fun i : Fin (n + 1) => S (.right i j)) d.2 f (Fin.last n)) = d
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  have downFam_surj {S : Arrow T → Type} (i : ℕ) : ∀ n (d : (downPath t i n).Fam S), ∃ f, downFam t i n f = d := by
    intro n
    induction n with
    | zero => intro d; exact ⟨fun j => j.elim0, rfl⟩
    | succ n ih =>
      intro d
      obtain ⟨d0, e, he⟩ := append_surj (Path.one (.down t i n)) (downPath t i n) d
      obtain ⟨f, hf⟩ := ih e
      refine ⟨Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f, ?_⟩
      rw [← he]
      show Path.Fam.append (p := Path.one (.down t i n)) ((), Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f (Fin.last n))
        (downFam t i n fun j => Fin.lastCases (motive := fun j : Fin (n + 1) => S (.down t i j)) d0.2 f j.castSucc) = _
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, hf]
      rfl
  refine ⟨e, he, fun _ => Path.Fam.append (q := rowPath T 0 D.R.m)
    (downFam t 0 D.R.m fun j => c j • givenFn B t Φ e (.down t 0 j)) (rowFam 0 D.R.m fun i => givenFn B t Φ e (.right i 0)),
    fun d hd => ?_, fun x hx => ?_⟩
  · rw [Finsupp.support_single_ne_zero _ (by rintro rfl; simp at hz), Finset.mem_singleton] at hd
    subst hd
    exact (GlobalTheory.OppConv.vecAll_append ρ e _ _ _ _ _ _).2
      ⟨(GlobalTheory.OppConv.vecAll_down ρ e t 0 _ _ _).2 hcol, (GlobalTheory.OppConv.vecAll_row ρ e 0 _ _ _).2 hrow⟩
  · rw [Finsupp.sum_single_index (by rw [zero_mul])]
    obtain ⟨x₁, x₂, rfl⟩ := append_surj (downPath t 0 D.R.m) (rowPath T 0 D.R.m) x
    obtain ⟨y, rfl⟩ := downFam_surj 0 D.R.m x₁
    obtain ⟨y', rfl⟩ := rowFam_surj 0 D.R.m x₂
    obtain ⟨h1, h2⟩ := (GlobalTheory.OppConv.halfAll_append e _ _ _ _).1 hx
    have hy := (GlobalTheory.OppConv.halfAll_down e t 0 _ _).1 h1
    have hy' := (GlobalTheory.OppConv.halfAll_row e 0 _ _).1 h2
    dsimp only
    rw [Finset.prod_congr rfl fun w _ => tensor_given B t Φ w y y']
    erw [GlobalTheory.OppConv.famProd_append (downPath t 0 D.R.m), GlobalTheory.OppConv.famProd_down, GlobalTheory.OppConv.famProd_row]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, givenFn, if_pos (hy _), if_pos (hy' _)]
    rw [Finset.prod_comm (s := Finset.univ) (t := locPl G t), Finset.prod_comm (s := Finset.univ) (t := locPl G t),
      ← mul_assoc, ← mul_assoc, hz, one_mul]

end GlobalTheory.FlipStart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Grid GlobalTheory.ChainFr
open scoped ENNReal

variable {D : D7}

theorem jm_not {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm (fun j => !(ε j)) = -Formalism.REAL.Jm ε := by
  ext a b
  by_cases h : a = b
  · subst h
    cases hε : ε a <;> simp [Formalism.REAL.Jm, hε]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_apply_ne _ h]

theorem gramAt_neg (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j
  simp [gramAt, neg_gram]

def negFr (N : Node D) : Fr (neg N.V) where
  ε τ j := !(N.M.ε τ j)
  fr := N.M.fr
  fr_unit := N.M.fr_unit
  fr_gram τ := by
    rw [jm_not, Matrix.mul_neg, Matrix.neg_mul, N.M.fr_gram τ, gramAt_neg]

theorem negFr_cart (N : Node D) : (negFr N).cart = cartS true N := by
  funext τ
  show (N.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun j => !(N.M.ε τ j)) * N.M.fr τ = -((N.M.fr τ)⁻¹ * Formalism.REAL.Jm (N.M.ε τ) * N.M.fr τ)
  rw [jm_not, Matrix.mul_neg, Matrix.neg_mul]

theorem thetaKernel_le_sobolev_mul_height_source {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeil ψ true S T χS χT ω) (μ : Measure (WO (neg S) T))
    (𝓓 : Set (WO (neg S) T)) (hμ : IsCovolOne (ratL T (neg S)) μ 𝓓) (U : AddSubgroup (WO (neg S) T))
    (hU : IsOpen (U : Set (WO (neg S) T))) :
    ∃ (d A : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ (neg S) T U, ∀ (g : GA D S) (h : GA D T),
      ‖thetaKO ω g h f‖ ≤ K * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight S g ^ A * GlobalTheory.Grow.height T h ^ A := by
  have hω' : IsWeilDatumO ψ (neg S) T χS χT (ω.toSgn true) := hω
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg S).rank T.rank
  obtain ⟨C, hC0, hC⟩ := (H (neg S) T rfl rfl).real ψ hθ hU
  refine ⟨d, A, C * 2 ^ A, by positivity, fun f hf g h => ?_⟩
  have hb := (hC χS χT (ω.toSgn true) hω' μ 𝓓 hμ f hf).2
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
    have e1 : (((ofSgn true S).symm (γ * g), h) : GA D (neg S) × GA D T) =
        ((ofSgn true S).symm γ, 1) * ((ofSgn true S).symm g, h) := by simp
    show (ω.toSgn true) ((ofSgn true S).symm (γ * g), h) f 0 = (ω.toSgn true) ((ofSgn true S).symm g, h) f 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hf.1)
  have hs : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
  have hgr : ∀ g, ‖thetaKO ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height T h ^ A) *
      GlobalTheory.Grow.height S g ^ A := fun g => by
    have := hb ((ofSgn true S).symm g) h
    refine this.trans_eq ?_
    show C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * (GlobalTheory.Grow.height S g * GlobalTheory.Grow.height T h) ^ A = _
    ring
  refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ω g h f) hinv hgr g).trans_eq ?_
  ring

theorem exists_sum_of_mem_fockSpan {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A : Fr V} {B : Fr W}
    {U : AddSubgroup (WO V W)} {g : WO V W → ℂ} (hg : g ∈ fockSpan ψ θ A B U) :
    ∃ (n : ℕ) (f : Fin n → (WO V W → ℂ)) (p : Fin n → PolF D W.rank V.rank),
      (∀ l, IsVacF ψ θ A B (f l)) ∧ g = ∑ l, ptF ψ θ A B (f l) (p l) := by
  obtain ⟨n, c, u, hu⟩ := Submodule.mem_span_set'.1 hg
  have hm : ∀ l, ∃ f₀ P, IsVacF ψ θ A B f₀ ∧ f₀ ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ (u l : WO V W → ℂ) = ptF ψ θ A B f₀ P :=
    fun l => (u l).2
  choose f₀ P hv _ he using hm
  refine ⟨n, f₀, fun l => c l • P l, hv, ?_⟩
  rw [← hu]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [he l]
  exact (map_smul (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb (f₀ l)) (c l) (P l)).symm

theorem isVacF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (negFr S) (Fr.ofModel T.M) f ↔ IsFinVec ψ θ true S T f := by
  unfold IsVacF IsFinVec
  rw [negFr_cart]
  rfl

theorem ptF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) (P : Pol S T) :
    ptF ψ θ (negFr S) (Fr.ofModel T.M) f P = fock ψ θ true S T f P := by
  unfold ptF fock
  rw [negFr_cart]
  rfl


end GlobalTheory.DownApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelInductionFromPairs
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowArrow

variable {D : D7}

theorem unit_of_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    IsUnit b.det := by
  have hJ : IsUnit (Formalism.REAL.Jm ε).det := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by split_ifs <;> norm_num
  rw [← h, det_mul] at hJ
  exact isUnit_of_mul_isUnit_right hJ

theorem inv_gram {n : ℕ} {G b : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : bᴴ * G * b = Formalism.REAL.Jm ε) :
    (b⁻¹)ᴴ * Formalism.REAL.Jm ε * b⁻¹ = G := by
  have hb := unit_of_gram h
  have h1 : (bᴴ)⁻¹ * bᴴ = 1 := nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hb.star)
  have h2 : b * b⁻¹ = 1 := mul_nonsing_inv _ hb
  rw [← h, conjTranspose_nonsing_inv]
  calc (bᴴ)⁻¹ * (bᴴ * G * b) * b⁻¹ = ((bᴴ)⁻¹ * bᴴ) * G * (b * b⁻¹) := by simp only [Matrix.mul_assoc]
    _ = G := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_frame (V : HSp D) (c b : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (b τ)ᴴ * gramAt D V τ * b τ = Formalism.REAL.Jm ε ∧ c τ * b τ = b τ * Formalism.REAL.Jm ε) :
    ∃ A : Fr V, A.cart = c ∧ A.onb = b := by
  choose ε hε using h
  refine ⟨⟨ε, fun τ => (b τ)⁻¹, fun τ => isUnit_nonsing_inv_iff.2 ((isUnit_iff_isUnit_det _).2 (unit_of_gram (hε τ).1)),
    fun τ => inv_gram (hε τ).1⟩, ?_, ?_⟩
  · funext τ
    simp only [Fr.cart]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1), ← (hε τ).2, Matrix.mul_assoc,
      mul_nonsing_inv _ (unit_of_gram (hε τ).1), Matrix.mul_one]
  · funext τ
    simp only [Fr.onb]
    rw [nonsing_inv_nonsing_inv _ (unit_of_gram (hε τ).1)]

theorem lifts_neg {X : ProvA} (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X) (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X)
    (hP : PairLifts D X) (hE : PairEx) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {A B : HSp D} {S S' : D.what₂.Tau → SPar} (MA : DSModel A S) (MB : DSModel B S') {aS aT : D.what₂.Tau → ℚ}
    (hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ) (aS τ) (aT τ)) (FA : Fr A) (FB : Fr B)
    (hA : cart MA = FA.cart) (hB : cart MB = FB.cart) {ω : GlobalTheory.Grid.WRep (GlobalTheory.Grid.sgn true B) A}
    (hω : IsWeilExp ψ (GlobalTheory.Grid.sgn true B) A aS aT ω) {f₀ : WO (GlobalTheory.Grid.sgn true B) A → ℂ}
    (hf₀ : IsVacF ψ θ (frSgn true FB) FA f₀) (h0 : f₀ ≠ 0) {ν : Measure (GA D A)} {𝓕 : Set (GA D A)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 ν) :
    ∃ It : PolF D A.rank B.rank → SmT MA → SmT MB, ∀ f, IsVacF ψ θ (frSgn true FB) FA f →
      LiftsM θ MA MB ν 𝓕 (fun P h g => thetaKO ω ((GlobalTheory.Grid.ofSgn true B).symm h) g (ptF ψ θ (frSgn true FB) FA f P)) It := by
  obtain ⟨N, κ, hN⟩ := GlobalTheory.negModel_tr D θ hθ B S' MB
  have cS : ∀ τ, (Fr.ofModel N).cart τ = (frSgn true FB).cart τ := fun τ =>
    (hN.cart τ).trans ((congrArg _ (congrFun hB τ)).trans (cart_frSgn true FB τ).symm)
  have cT : ∀ τ, (Fr.ofModel MA).cart τ = FA.cart τ := fun τ => congrFun hA τ
  have vac : ∀ f, IsVacF ψ θ (frSgn true FB) FA f → IsVacF ψ θ (Fr.ofModel N) (Fr.ofModel MA) f :=
    fun f h => ⟨h.1, fun τ => by rw [cS, cT]; exact h.2 τ⟩
  obtain ⟨j, hj⟩ := GlobalTheory.FrameChange.ptF_frame_change D ψ θ hψ hθ (GlobalTheory.Grid.sgn true B) A _ _ _ _ cS cT
  obtain ⟨It, hIt⟩ := hE D _ S aS aT hR _ A N MA θ ψ hθ
  have hv : IsVacVec ψ θ N MA f₀ := ⟨hf₀.1, h0, (vac f₀ hf₀).2⟩
  refine ⟨fun P v => κ (It (j P) v), fun f hf F hF => ?_⟩
  obtain ⟨F₁, hF₁, e₁⟩ := hP _ _ aS aT (fun τ => GlobalTheory.StepRule.rulePar_of_pairPar h3 h4 h5 (hR τ)) _ A N MA θ ψ hθ ω hω f₀ It hv
    (hIt ω hω f₀ hv) ν 𝓕 hν h𝓕 f (vac f hf) F hF
  obtain ⟨F', hF', e'⟩ := hN.mult' F₁ hF₁
  refine ⟨F', hF', fun P v h => ?_⟩
  have := e₁ (j P) v ((GlobalTheory.Grid.ofSgn true B).symm h)
  rw [← ptF_ofModel, e'] at this
  simp only [hj f hf.1 P, MulEquiv.apply_symm_apply, RingHom.id_apply] at this
  exact this

theorem cen_eq (τ : D.what₂.Tau) : GlobalTheory.Grid.cen D τ = GlobalTheory.ChiGrid.cen D 1 τ := by
  funext i
  unfold GlobalTheory.Grid.cen GlobalTheory.ChiGrid.cen GlobalTheory.Grid.gridOf
  rw [GlobalTheory.GridJoin.gap_eq_chiGap D]
  rfl

theorem parRow_eq (i : ℕ) (τ : D.what₂.Tau) : parRow D 1 i τ = GlobalTheory.Grid.parV D i 0 τ := by
  have hg : GlobalTheory.Grid.grid D τ = GlobalTheory.ChiGrid.num D 1 τ := by
    unfold GlobalTheory.Grid.grid GlobalTheory.Grid.gridOf GlobalTheory.ChiGrid.num
    rw [cen_eq, GlobalTheory.GridJoin.gap_eq_chiGap D]
    rfl
  rw [GlobalTheory.Grid.parV, hg]
  rfl

theorem exp_att {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {c : ℚ} (h : HasInfExp D χ τ c)
    (hη : HasInfExp D η τ (1 / 2)) (n : ℕ) : HasInfExp D (Lift.attChr χ η n) τ (att c n) := by
  unfold Lift.attChr att
  split_ifs
  · rw [sub_eq_add_neg]
    exact StepVac.hasInfExp_mul h (StepVac.hasInfExp_inv hη)
  · exact h

end GlobalTheory.RowArrow


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNsmulActO
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLinear

open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove

variable {D : D7} {S T : HSp D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_nsmul_actO (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT)
    (g : GA D S) (h : GA D T) : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      N • actO S T g h u ∈ latO S T ΛS ΛT fun _ => True := by
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.toIsLattice.fg hT.toIsLattice.fg
  obtain ⟨K, hK, hKt⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_mul (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun z => GlobalTheory.PlaceDatum.exists_den_adele z) ((Formalism.L2.Theta.mt T h).map (toEAf D))
    ((Formalism.L2.Theta.mt S g⁻¹).map (toEAf D))
  refine ⟨K * (N * M), Nat.mul_pos hK (Nat.mul_pos hN hM), fun u hu => ?_⟩
  rw [← smul_smul]
  apply hKt
  · have h0 := GlobalTheory.SplitScalar.latO_fin hu
    have hz : (actO S T g h u).map (infPart D) = 0 := by
      simp only [actO, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]
    ext i j
    have hij := congrFun (congrFun hz i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul, Matrix.zero_apply] at hij ⊢
    rw [hij, smul_zero]
  · intro i j
    have hX := hNm M (u.map (toEAf D)) (fun i j => hMu u hu i j) i j
    have e1 : toEAf D (((N * M) • actO S T g h u) i j) = ((N * M : ℕ) : EAf D) *
        ((Formalism.L2.Theta.mt T h).map (toEAf D) * u.map (toEAf D) * (Formalism.L2.Theta.mt S g⁻¹).map (toEAf D)) i j := by
      simp only [actO]
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    rw [e1]
    exact hX

theorem isSBHalf_actO (hS : Submodule.IsFullLattice D.host.E ΛS) (hT : Submodule.IsFullLattice D.host.E ΛT) {a : AE D}
    (g : GA D S) (h : GA D T) {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) :
    IsSBHalf a (latO S T ΛS ΛT fun _ => True) fun t => Φ (actO S T g h t) := by
  simp only [IsSBHalf] at hΦ ⊢
  obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
  obtain ⟨N, hN, hNu⟩ := exists_nsmul_actO hS hT g h
  obtain ⟨M, hM, hMu⟩ := exists_nsmul_actO hS hT g⁻¹ h⁻¹
  refine ⟨fun t ht => isHalf_of_act g h (h1 _ ht), k * (N * M), Nat.mul_pos hk (Nat.mul_pos hN hM), ?_, ?_⟩
  · intro u hu hua t
    rw [act_add, act_nsmul]
    have hw := hNu u hu
    have hwa : IsHalf a (N • actO S T g h u) :=
      GlobalTheory.SplitScalar.isHalf_nsmul (GlobalTheory.SplitHecke.isHalf_actO g h hua) N
    have e : (k * (N * M)) • actO S T g h u = k • (M • (N • actO S T g h u)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact h2 _ (AddSubgroup.nsmul_mem _ hw M) (GlobalTheory.SplitScalar.isHalf_nsmul hwa M) _
  · intro t ht
    have hm := hMu _ (h3 _ ht)
    rw [act_nsmul, GlobalTheory.SplitHecke.actO_inv_actO] at hm
    have e : (k * (N * M)) • t = N • (M • (k • t)) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [e]
    exact AddSubgroup.nsmul_mem _ hm N

theorem absV_mul {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : (Fv F v)ˣ) :
    absV F v (x * y) = absV F v x * absV F v y := by
  unfold absV
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
    ((Valuation.ne_zero_iff _).mpr y.ne_zero), zpow_add₀ hq]

theorem absFin_mul (x y : (AE D)ˣ) : absFin D (x * y) = absFin D x * absFin D y := by
  unfold absFin
  simp_rw [map_mul, absV_mul]
  exact finprod_mul_distrib (absFin_finite D x) (absFin_finite D y)

theorem absFin_one : absFin D 1 = 1 := by
  have h := absFin_mul (D := D) 1 1
  rw [mul_one] at h
  have hp := absFin_pos D 1
  have h2 : absFin D 1 * (absFin D 1 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hp.ne'
  · linarith

theorem modFac_mul (x x' y y' : (AE D)ˣ) : modFac S T (x * x') (y * y') = modFac S T x y * modFac S T x' y' := by
  unfold modFac
  rw [absFin_mul, absFin_mul, Real.mul_rpow (absFin_pos D x).le (absFin_pos D x').le,
    Real.mul_rpow (absFin_pos D y).le (absFin_pos D y').le]
  ring

theorem modFac_one : modFac S T 1 1 = 1 := by
  unfold modFac
  rw [absFin_one, Real.one_rpow, Real.one_rpow, one_mul]

end GlobalTheory.SplitLinear

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

section Transfer

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem actO_eq_of_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {x : WO S T}
    (hx : x.map (infPart D) = 0) : actO S T g h x = x := by
  have e1 : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = 1 := congrArg Units.val (show finHom S g⁻¹ = 1 from inv_mem hg)
  have e2 : (Formalism.L2.Theta.mt T h).map (finPart D) = 1 := congrArg Units.val (show finHom T h = 1 from hh)
  have e3 : (actO S T g h x).map (infPart D) = x.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]
  have e4 : (actO S T g h x).map (finPart D) = x.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.mul_one, Matrix.one_mul]
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun e3 i) j) (congrFun (congrFun e4 i) j)

theorem isItW_of_mem_span {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeilDatumO ψ S T χS χT ω) (hθ : IsInfFam θ)
    {P P' : D.what₂.Tau → SPar} {M : DSModel S P} {M' : DSModel T P'}
    {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    {It : PolF D T.rank S.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (h : IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f) It) :
    IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f₀) It := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  let L : Module.End ℂ (WO S T → ℂ) := ∑ a ∈ c.support, c a • GlobalTheory.SplitScalar.heisL ψ S T a.1
  have hL : ∀ F, L F = ∑ a ∈ c.support, c a • heisO ψ S T a.1 F := fun F => by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, GlobalTheory.SplitScalar.heisL_apply]
  have hd : ∀ τ z F, IsThetaFunO ψ S T F → L (dRho (heisO ψ S T) θ τ z F) = dRho (heisO ψ S T) θ τ z (L F) :=
    fun τ z F hF => by
      rw [hL, hL, GlobalTheory.FockTranslate.dRho_sum hω.std.1.1 hθ hF τ z c.support (fun a => a.1) c fun a _ => a.2]
  have hpt : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ Q) ∧
      L (pureTensorO ψ θ S T sS sT BS BT f₀ Q) = pureTensorO ψ θ S T sS sT BS BT (L f₀) Q := fun Q => by
    refine GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
      (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _ _ L (fun k F hF => ?_) f₀ h₀ Q
    obtain ⟨τ, i, j⟩ := k
    refine ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF))), ?_⟩
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul, hd _ _ _ hF, hd _ _ _ hF]
  have hom : ∀ g ∈ GinfC S, ∀ k ∈ GinfC T, ∀ Q, ω (g, k) (pureTensorO ψ θ S T sS sT BS BT (L f₀) Q) =
      L (ω (g, k) (pureTensorO ψ θ S T sS sT BS BT f₀ Q)) := fun g hg k hk Q => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (hpt Q).2, hL, hL, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hω.om_heis _ _ _ _ (hpt Q).1, actO_eq_of_real hg hk a.2]
  have hder : ∀ (F : ℝ → WO S T → ℂ) (F' : WO S T → ℂ), (∀ z, HasDerivAt (fun t => F t z) (F' z) 0) →
      ∀ z, HasDerivAt (fun t => L (F t) z) (L F' z) 0 := fun F F' hF z => by
    simp only [hL, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]
    exact HasDerivAt.fun_sum fun a _ => ((hF _).const_mul _).const_mul _
  have e : (c.sum fun i a => a • heisO ψ S T i.1 f₀) = L f₀ := (hL f₀).symm
  rw [e] at h
  refine ⟨h.ne, h.bdd, fun τ g hg φ φ' H => h.eqK τ g hg φ φ' ?_, fun τ X hX φ φ' H => h.eqg τ X hX φ φ' fun z => ?_,
    fun τ g hg φ φ' v v' H => h.invK τ g hg φ φ' v v' ?_, fun τ X hX φ φ' v v' H => h.invg τ X hX φ φ' v v' fun z => ?_⟩
  · rw [hom _ (GlobalTheory.FinTranslate.atTau_mem θ S τ g) _ (one_mem _), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (GlobalTheory.FinTranslate.oneP_mem θ S τ X t) _ (one_mem _) φ, ← (hpt φ').2]
    exact hder _ _ H z
  · rw [hom _ (one_mem _) _ (GlobalTheory.FinTranslate.atTau_mem θ T τ g), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (one_mem _) _ (GlobalTheory.FinTranslate.oneP_mem θ T τ X t) φ, ← (hpt φ').2]
    exact hder _ _ H z

theorem stepVec_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ dS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ dT) βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  rw [hall Tm hTm]
  exact (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB).1

theorem finVec_of_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T sS sT ΛS ΛT f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)) :
    IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2⟩

end Transfer

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chrStep_eq_muAt (R : RealDat D A Ks) (t : T) (j : ℕ) : Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
    (GridPre.muAt R t (j + 1) (rkV D 0 j), GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

end GlobalTheory.Grid

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftIdeal

def conjO (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv

theorem coe_conjO (D : D7) (x : 𝓞 D.host.E) :
    ((conjO D x : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) := rfl

theorem conjO_conjO (D : D7) (x : 𝓞 D.host.E) : conjO D (conjO D x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO]
  simp

theorem star_eq (D : D7) (x : D.host.E) : star x = IsCMField.complexConj D.host.E x := rfl

theorem conjI_eq_map (D : D7) (I : Ideal (𝓞 D.host.E)) :
    conjI I = I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, RingOfIntegers.ext ?_⟩
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem map_map_conjO (D : D7) (I : Ideal (𝓞 D.host.E)) :
    (I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = I := by
  rw [Ideal.map_map]
  have : ((conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).comp (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = RingHom.id _ :=
    RingHom.ext fun x => conjO_conjO D x
  rw [this, Ideal.map_id]

end GlobalTheory.LiftIdeal

end

noncomputable section

namespace GlobalTheory.LiftIdeal

open GlobalTheory.LiftLevel

theorem isMaximal_map (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) :
    (PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := by
  haveI := PP.isMaximal
  exact Ideal.map_isMaximal_of_equiv (conjO D)

theorem liftI_eq (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    liftI Pg Q = ∏ PP ∈ Pg ∪ Q, PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold liftI
  exact Finset.prod_congr rfl fun PP _ => conjI_eq_map D _

theorem conjI_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    conjI (liftI Pg Q) = ∏ PP ∈ Pg ∪ Q, PP.asIdeal := by
  rw [conjI_eq_map, liftI_eq]
  have := map_prod (Ideal.mapHom (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
    (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (Pg ∪ Q)
  simp only [Ideal.mapHom_apply] at this
  rw [this]
  exact Finset.prod_congr rfl fun PP _ => map_map_conjO D _

theorem map_ne {D : D7} {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {PP PP' : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ S) (hP' : PP' ∈ S) :
    PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ PP'.asIdeal := by
  intro h
  refine GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP' fun c hc => ?_
  refine ⟨conjO D c, h ▸ Ideal.mem_map_of_mem _ hc, ?_⟩
  rw [coe_conjO, star_eq]

theorem liftI_props : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) →
    GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  intro D Pg Q e hne h2 he
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P0, hP0⟩ := hne
    intro htop
    have hle : liftI Pg Q ≤ P0.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [liftI_eq]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hP0))
    rw [htop] at hle
    exact (isMaximal_map D P0).ne_top (top_le_iff.1 hle)
  · rw [liftI_eq, ← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
    rw [Ne, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective (f := (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (conjO D).injective]
    exact PP.ne_bot
  · rw [conjI_liftI, liftI_eq]
    refine IsCoprime.prod_left fun PP hP => IsCoprime.prod_right fun PP' hP' => ?_
    exact Ideal.isCoprime_iff_sup_eq.2
      ((isMaximal_map D PP).coprime_of_ne PP'.isMaximal (map_ne he hP hP'))
  · rw [liftI_eq]
    refine IsCoprime.prod_left fun PP hP => Ideal.isCoprime_iff_sup_eq.2 ?_
    have h2' : (2 : 𝓞 D.host.E) ∉ PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, map_ofNat]
      exact h2 PP (Finset.mem_union.1 hP)
    exact (isMaximal_map D PP).out.2 _ (left_lt_sup.2 fun hle => h2' (hle (Ideal.mem_span_singleton_self 2)))

end GlobalTheory.LiftIdeal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatePlacesProductIdeal_proper_odd_coprime : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧ IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  first | exact @GlobalTheory.LiftIdeal.liftI_props | exact GlobalTheory.LiftIdeal.liftI_props | (intros; apply GlobalTheory.LiftIdeal.liftI_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameAtOfUnrAt
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

variable {D : D7}

theorem isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} (h : χ.UnrAt PP) : IsRes χ PP 1 := by
  intro a k u hk hu
  have ha : a ∉ PP.asIdeal := by
    intro hmem
    have h0 : (u : kP PP) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact u.ne_zero h0
  have hv : Formalism.L2.Host.IsUnitAt PP (Formalism.L2.Host.atFin PP k) := by
    show Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) (k : D.host.E)) = 1
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
      | erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [hk, Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).mpr ha
  have := h _ hv
  rw [MonoidHom.one_apply]
  exact this.symm

theorem tameAt_of_unrAt {χ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} (h : χ.UnrAt PP) : χ.TameAt PP := by
  intro x hx _
  exact h x hx

theorem UnrOff.mul {b : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : UnrOff b χ) (h' : UnrOff b χ') : UnrOff b (χ * χ') := by
  intro x h1 h2 h3 h4
  rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem UnrOff.inv {b : AE D} {χ : (AE D)ˣ →* Circle} (h : UnrOff b χ) : UnrOff b χ⁻¹ := by
  intro x h1 h2 h3 h4
  rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

variable {T0 : Type} {L : LevCh D T0} {μ0 : T0}

theorem unrOff_mu (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {P : Finset (Pl D.host.E)} {e : AE D}
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) :
    UnrOff (e + cA D e) (L.mu t ((j : ℕ) + 1)) ∧ UnrOff (e + cA D e) L.eta := by
  obtain ⟨-, hQ, -, hoff⟩ := GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL t j
  have hsub : ∀ PP', PP' ∉ P → (∀ PP ∈ P, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') →
      PP' ∉ L.Pg ∧ PP' ∉ L.Q t ∧ (∀ PP ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') ∧
        ∀ PP ∈ L.Q t, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
    intro PP' hn hc
    exact ⟨fun hm => hn ((hP PP').mpr (Or.inl hm)), fun hm => hn ((hP PP').mpr (Or.inr hm)),
      fun PP hm => hc PP ((hP PP).mpr (Or.inl hm)), fun PP hm => hc PP ((hP PP).mpr (Or.inr hm))⟩
  have h0 : UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ (L.C.mu0 j) P e (hL.mu0 j) he
      (fun PP' hn hc => hoff PP' (hsub PP' hn hc).1 (hsub PP' hn hc).2.2.1)
  have h1 : UnrOff (e + cA D e) (L.xi t) := by
    refine GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ (L.xiH t) P e (hL.xi t) he (fun PP' hn hc => ?_)
    by_contra hr
    rcases (hL.Q_ram t PP').mp hr with hm | ⟨PP, hm, hcj⟩
    · exact (hsub PP' hn hc).2.1 hm
    · exact (hsub PP' hn hc).2.2.2 PP hm hcj
  refine ⟨?_, GlobalTheory.T.heckeChar_trivial_on_idempotentIntegralUnits D _ L.C.eta P e hL.eta he
    (fun PP' _ _ => L.C.isEta.unr PP')⟩
  show UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1) * L.xi t)
  exact h0.mul h1

theorem mu_val (hL : L.Is μ0) (t : T0) (j : Fin D.R.m) {P : Finset (Pl D.host.E)} {e : AE D}
    (hP : ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ L.Q t) (he : IsIdemSum e P) (x : (AE D)ˣ) (a : AE D)
    (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ) (hx : (x : AE D) = e * a + (1 - e))
    (ha : (a' : Lev.EAf D) = toEAf D a) (hu : ∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') :
    ((L.mu t ((j : ℕ) + 1) x : Circle) : ℂ) =
        (((∏ PP ∈ L.Pg, (L.chi ((j : ℕ) + 1) PP (u PP))⁻¹) * ∏ PP ∈ L.Q t, L.xiR t PP (u PP) : ℂˣ) : ℂ) ∧
      L.eta x = 1 := by
  classical
  obtain ⟨hdisj, hQ, hPg, -⟩ := GlobalTheory.T.levelCharacters_ramification_levelPlaces D T0 L μ0 hL t j
  have hPu : P = L.Pg ∪ L.Q t := by
    ext PP
    rw [hP PP, Finset.mem_union]
  have hA := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D (L.mu0 ((j : ℕ) + 1)) (L.C.mu0 j) P e
    (fun PP => if PP ∈ L.Pg then (L.chi ((j : ℕ) + 1) PP)⁻¹ else 1) (hL.mu0 j) he
    (fun PP hm => by
      by_cases hg : PP ∈ L.Pg
      · simp only [if_pos hg]
        exact ⟨(L.C.isMu0 j).tame PP, hL.chi j PP hg⟩
      · simp only [if_neg hg]
        have hq : PP ∈ L.Q t := ((hP PP).mp hm).resolve_left hg
        exact ⟨tameAt_of_unrAt (hQ PP hq), isRes_one (hQ PP hq)⟩) x a a' u hx ha hu
  have hB := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D (L.xi t) (L.xiH t) P e
    (fun PP => if PP ∈ L.Q t then L.xiR t PP else 1) (hL.xi t) he
    (fun PP hm => by
      by_cases hq : PP ∈ L.Q t
      · simp only [if_pos hq]
        exact ⟨hL.xi_tame t PP, hL.xiR t PP hq⟩
      · simp only [if_neg hq]
        have hg : PP ∈ L.Pg := ((hP PP).mp hm).resolve_right hq
        exact ⟨tameAt_of_unrAt (hPg PP hg), isRes_one (hPg PP hg)⟩) x a a' u hx ha hu
  have hC := GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue D L.eta L.C.eta P e (fun _ => 1) hL.eta he
    (fun PP _ => ⟨tameAt_of_unrAt (L.C.isEta.unr PP),
      isRes_one (L.C.isEta.unr PP)⟩) x a a' u hx ha hu
  rw [hPu, Finset.prod_union hdisj] at hA hB
  have hA' : ((L.mu0 ((j : ℕ) + 1) x : Circle) : ℂ) =
      ∏ PP ∈ L.Pg, (((L.chi ((j : ℕ) + 1) PP (u PP))⁻¹ : ℂˣ) : ℂ) := by
    rw [hA, Finset.prod_eq_one (s := L.Q t) (fun PP hm => ?_), mul_one]
    · exact Finset.prod_congr rfl (fun PP hm => by simp only [if_pos hm, MonoidHom.inv_apply])
    · simp only [if_neg (Finset.disjoint_right.mp hdisj hm), MonoidHom.one_apply, Units.val_one]
  have hB' : ((L.xi t x : Circle) : ℂ) = ∏ PP ∈ L.Q t, ((L.xiR t PP (u PP) : ℂˣ) : ℂ) := by
    rw [hB, Finset.prod_eq_one (s := L.Pg) (fun PP hm => ?_), one_mul]
    · exact Finset.prod_congr rfl (fun PP hm => by simp only [if_pos hm])
    · simp only [if_neg (Finset.disjoint_left.mp hdisj hm), MonoidHom.one_apply, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.coe_prod, Units.coe_prod]
    show ((L.mu0 ((j : ℕ) + 1) x * L.xi t x : Circle) : ℂ) = _
    rw [Circle.coe_mul, hA', hB']
  · have hC' : ((L.eta x : Circle) : ℂ) = 1 := by
      rw [hC]
      exact Finset.prod_eq_one (fun PP _ => by simp only [MonoidHom.one_apply, Units.val_one])
    exact Circle.ext (by rw [hC', Circle.coe_one])

end GlobalTheory.VecInv
end
