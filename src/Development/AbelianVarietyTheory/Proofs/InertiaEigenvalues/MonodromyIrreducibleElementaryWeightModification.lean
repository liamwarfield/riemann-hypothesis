module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChange
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameChange


open Topology Filter in
theorem cont_apply_Om {l : ℕ} [Fact l.Prime] (d : Om l) : Continuous fun g : GQ l => g d := by
  refine continuous_iff_continuousAt.2 fun g₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer (GQ l) d
  have hS : (S : Set (GQ l)) ∈ 𝓝 (g₀⁻¹ * g₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral d).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS] with g hg
  have h : (g₀⁻¹ * g) • d = d := hg
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h


open Topology Filter in
theorem cont_σC {l : ℕ} [Fact l.Prime] (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨d, hd⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt y
    (show (0 : ℝ) < ε / 3 by positivity)
  have h1 := Metric.tendsto_nhds.1 ((cont_apply_Om d).tendsto g₀) (ε / 3) (by positivity)
  filter_upwards [h1] with g hg
  have e : ∀ g' : GQ l, dist (Formalism.Per.σC g' y) (Formalism.Per.σC g' (d : ℂ_[l])) = dist y (d : ℂ_[l]) := fun g' => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, GlobalTheory.RingBasics.norm_σC]
  have e2 : dist (Formalism.Per.σC g (d : ℂ_[l])) (Formalism.Per.σC g₀ (d : ℂ_[l])) = dist (g d) (g₀ d) := by
    rw [GlobalTheory.RingBasics.σC_coe, GlobalTheory.RingBasics.σC_coe, UniformSpace.Completion.dist_eq]
  calc dist (Formalism.Per.σC g y) (Formalism.Per.σC g₀ y)
      ≤ dist (Formalism.Per.σC g y) (Formalism.Per.σC g (d : ℂ_[l])) + dist (Formalism.Per.σC g (d : ℂ_[l])) (Formalism.Per.σC g₀ (d : ℂ_[l])) +
        dist (Formalism.Per.σC g₀ (d : ℂ_[l])) (Formalism.Per.σC g₀ y) := dist_triangle4 _ _ _ _
    _ < ε := by rw [e, e2, dist_comm (Formalism.Per.σC g₀ _), e]; linarith

theorem cont_of_frame : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (N : ↥(GK K) → Matrix n n ↥(MaximalUnramifiedExtension l)) (W : GL n P.R.BdR) (k : n → ℤ), UnitM P W → (∀ g : ↥(GK K), (N g).map (kd P) = ((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k j : ℚ_[l]ˣ) : ℚ_[l])) * (W : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l))) → ∀ i j, Continuous fun g : ↥(GK K) => ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  intro l _ P AI T n _ _ K N W k hW hN i j
  obtain ⟨S, θ, hS, -, -, hθom, hθg⟩ := GlobalTheory.T.exists_theta_deRhamFilZero_surjective l P AI T
  have hemb : Topology.IsEmbedding (fun x : Om l => (x : ℂ_[l])) :=
    (UniformSpace.Completion.isUniformEmbedding_coe (Om l)).isEmbedding
  let a : n → ℂ_[l] := fun k' => θ ⟨((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i k', (hS _).2 (hW.2 i k')⟩
  let b : n → ℂ_[l] := fun k' => θ ⟨(W : Matrix n n P.R.BdR) k' j, (hS _).2 (hW.1 k' j)⟩
  have key : ∀ g : ↥(GK K), (((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) : ℂ_[l]) =
      ∑ k', a k' * (((algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])) : Om l) : ℂ_[l]) *
        Formalism.Per.σC (g : GQ l) (b k') := by
    intro g
    have e := congrFun (congrFun (hN g) i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at e
    obtain ⟨h0, hθ0⟩ := hθom ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l)
    rw [← hθ0]
    let xa : n → ↥S := fun k' => ⟨((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i k', (hS _).2 (hW.2 i k')⟩
    let xq : n → ↥S := fun k' => ⟨algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])),
      (hS _).2 (om_mem_Fil P _)⟩
    let xb : n → ↥S := fun k' => ⟨P.actQdR (g : GQ l) ((W : Matrix n n P.R.BdR) k' j), (hS _).2 (Fil_act _ (hW.1 k' j))⟩
    have hsum : (⟨algebraMap (Om l) P.R.BdR ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l), h0⟩ : ↥S) = ∑ k', xa k' * xq k' * xb k' := by
      apply Subtype.ext
      push_cast
      rw [show algebraMap (Om l) P.R.BdR ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) = kd P (N g i j) from rfl, e]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [Matrix.mul_diagonal, Matrix.map_apply]
      change _ = ((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i k' *
        algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])) *
        P.actQdR (g : GQ l) ((W : Matrix n n P.R.BdR) k' j)
      rw [← IsScalarTower.algebraMap_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul, map_mul]
    obtain ⟨h1, h2⟩ := hθom (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l]))
    obtain ⟨h3, h4⟩ := hθg (g : GQ l) ⟨(W : Matrix n n P.R.BdR) k' j, (hS _).2 (hW.1 k' j)⟩
    have e1 : θ (xq k') = (((algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])) : Om l) : ℂ_[l]) := h2
    have e2 : θ (xb k') = Formalism.Per.σC (g : GQ l) (b k') := h4
    rw [e1, e2]
  refine hemb.continuous_iff.2 ((continuous_congr fun g => (key g).symm).1 ?_)
  refine continuous_finsetSum _ fun k' _ => ?_
  have hχ : Continuous fun g : GQ l => (P.χQ g : ℚ_[l]) := GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc
  have hχk : Continuous fun g : ↥(GK K) => ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l]) := by
    simp only [Units.val_zpow_eq_zpow_val]
    exact (hχ.comp continuous_subtype_val).zpow₀ _ fun g => Or.inl (Units.ne_zero _)
  refine (continuous_const.mul ?_).mul ?_
  · exact (UniformSpace.Completion.continuous_coe _).comp ((continuous_algebraMap ℚ_[l] (Om l)).comp hχk)
  · exact (cont_σC (b k')).comp continuous_subtype_val

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem act_tz (g : GQ l) (a : ℤ) :
    P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  rw [tz, ← iota_act, Inhab.act_zpow, map_mul, AlgHom.commutes]

theorem phi_iter_act (m : ℕ) (g : GQ l) (b : P.R.B) : P.φB^[m] (P.actQ g b) = P.actQ g (P.φB^[m] b) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]

end GlobalTheory.PMon.FrameChange

namespace GlobalTheory.PMon


open FrameChange in
theorem exists_rep_of_fixed_frame_change : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w e : Fin r → n → ℤ) (U : Fin r → GL n P.R.BdR) (A : GL n P.R.B), IsRat r ρ → (∀ (m : Fin r) (g : ↥(GK K)), matD P ρ m g * (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])) → (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) → (∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (e m j)) * (W : Matrix n n P.R.BdR)) → ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + e m j) ∧ (AdmSt P ρ' → AdmSt P ρ) := by
  intro l _ P AI T n _ _ K r ρ w e U A hρ hU hA hfr
  choose W hWu hAW using hfr
  haveI := nontrivial_B P
  have alg_inj : Function.Injective (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective
  let φr : P.R.B →+* P.R.B := ((P.φB ^ r : P.R.B →ₐ[ℚ_[l]] P.R.B) : P.R.B →+* P.R.B)
  have hφr : ∀ b, φr b = P.φB^[r] b := fun b => by simp [φr, AlgHom.coe_pow]
  let X : ↥(GK K) → Matrix n n P.R.B := fun g =>
    ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B) * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *
      (A : Matrix n n P.R.B).map (P.actQ (g : GQ l))
  have hXA : ∀ g, (A : Matrix n n P.R.B) * X g =
      (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) * (A : Matrix n n P.R.B).map (P.actQ (g : GQ l)) := by
    intro g
    simp only [X, ← mul_assoc, Units.mul_inv, one_mul]

  have h1 : (A : Matrix n n P.R.B).map φr = A := by
    ext i j; rw [Matrix.map_apply, hφr, hA]
  have h2 : ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B).map φr = ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B) := by
    have h3 : ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B).map φr * (A : Matrix n n P.R.B) = 1 := by
      conv_lhs => rw [← h1]
      rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B).map φr *
          ((A : Matrix n n P.R.B) * ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B)) := by rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, h3, one_mul]
  have hXfix : ∀ g i j, P.φB^[r] (X g i j) = X g i j := by
    intro g i j
    have eR : ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map φr =
        (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
      ext a b; rw [Matrix.map_apply, Matrix.map_apply, hφr, phi_iter_kur, hρ.rat]
    have eA : ((A : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map φr = (A : Matrix n n P.R.B).map (P.actQ (g : GQ l)) := by
      ext a b; rw [Matrix.map_apply, Matrix.map_apply, hφr, phi_iter_act, hA]
    have e : (X g).map φr = X g := by
      simp only [X, Matrix.map_mul, h2, eR, eA]
    rw [← hφr]; exact congrFun (congrFun e i) j

  have hev : ∀ (m : Fin r) g, (X g).map (ev P m) = (((W m)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) *
      Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (w m j + e m j) : ℚ_[l]ˣ) : ℚ_[l])) *
      (W m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) := by
    intro m g
    have hE : ∀ M : Matrix n n P.R.B, M.map (ev P m) = M.map (evHom P m) := fun M => by
      ext; simp [evHom_apply]
    have key := congrArg (fun M => M.map (evHom P m)) (hXA g)
    simp only [Matrix.map_mul] at key
    have k2 : ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (evHom P m) = matD P ρ m g := by
      ext i j; simp [matD, evHom_apply, ev_kur]
    have k3 : ((A : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (evHom P m) =
        ((A : Matrix n n P.R.B).map (evHom P m)).map (P.actQdR (g : GQ l)) := by
      ext i j; simp [evHom_apply, ev_act]
    rw [k2, k3, ← hE, hAW m, ← hE] at key
    set D := Matrix.diagonal (fun j => tz P (e m j))
    set Q' := Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (w m j + e m j) : ℚ_[l]ˣ) : ℚ_[l]))
    have hD : Matrix.diagonal (fun j => tz P (-e m j)) * D = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext j; rw [← tz_add, neg_add_cancel, tz_zero]
    have hDg : D.map (P.actQdR (g : GQ l)) = Matrix.diagonal (fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (e m j) : ℚ_[l]ˣ) : ℚ_[l])) * D := by
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
      congr 1; funext j; exact FrameChange.act_tz P _ _
    have hcomm : Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])) *
        (Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (e m j) : ℚ_[l]ˣ) : ℚ_[l])) * D) =
        D * Q' := by
      simp only [D, Q', Matrix.diagonal_mul_diagonal]
      congr 1; funext j
      rw [zpow_add, Units.val_mul, map_mul]; ring
    rw [Matrix.map_mul, Matrix.map_mul, ← mul_assoc, ← mul_assoc, hU m g, hDg, mul_assoc _ _ (Matrix.diagonal _ * D),
      hcomm] at key

    have key2 : (W m : Matrix n n P.R.BdR) * (X g).map (ev P m) = Q' * (W m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) := by
      have k4 : (U m : Matrix n n P.R.BdR) * (D * ((W m : Matrix n n P.R.BdR) * (X g).map (ev P m))) =
          (U m : Matrix n n P.R.BdR) * (D * (Q' * (W m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)))) := by
        simpa only [mul_assoc] using key
      have k5 := (Units.mul_right_inj (U m)).mp k4
      have k6 := congrArg (fun M => Matrix.diagonal (fun j => tz P (-e m j)) * M) k5
      simpa only [← mul_assoc, hD, one_mul] using k6
    calc _ = (((W m)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * ((W m : Matrix n n P.R.BdR) * (X g).map (ev P m)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [key2, mul_assoc]
  have hFil : ∀ (m : Fin r) g i j, ev P m (X g i j) ∈ Fil P 0 := by
    intro m g i j
    have := congrFun (congrFun (hev m g) i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.mul_apply]
    refine Fil_sum fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.map_apply]
    exact Fil_mul_left (Fil_mul_left ((hWu m).2 i k) (q_mem_Fil P _)) (Fil_act _ ((hWu m).1 k j))
  have hpz := fun g i j => GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T r hρ.pos (X g i j) (hXfix g i j)
    (fun k hk => hFil ⟨k, hk⟩ g i j)
  choose N hNfr hNeq using hpz
  have hNmap : ∀ g, (Matrix.of (N g)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) = X g := fun g => by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, ← hNeq]
  have hNK : ∀ g i j, ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := fun g i j => hρ.le _ (hNfr g i j)
  have hρK : ∀ g i j, (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := fun g i j => hρ.le _ (hρ.rat g i j)
  have hXact : ∀ g h : ↥(GK K), (X h).map (P.actQ (g : GQ l)) = X h := by
    intro g h; ext i j; rw [Matrix.map_apply, hNeq, act_kur P g (hNK h i j)]
  have hRact : ∀ g h : ↥(GK K), ((ρ h : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (P.actQ (g : GQ l)) =
      (ρ h : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
    intro g h; ext i j; rw [Matrix.map_apply, Matrix.map_apply, act_kur P g (hρK h i j)]
  have hX1 : X 1 = 1 := by
    have hm1 : (A : Matrix n n P.R.B).map (P.actQ ((1 : ↥(GK K)) : GQ l)) = A := by
      ext i j; simp
    simp only [X, hm1, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one, Units.inv_mul]
  have hXmul : ∀ g h, X (g * h) = X g * X h := by
    intro g h
    apply (Units.mul_right_inj A).mp
    have hAgh : (A : Matrix n n P.R.B).map (P.actQ ((g * h : ↥(GK K)) : GQ l)) =
        ((A : Matrix n n P.R.B).map (P.actQ (h : GQ l))).map (P.actQ (g : GQ l)) := by
      ext i j; simp [AlgEquiv.mul_apply]
    rw [hXA, ← mul_assoc, hXA, mul_assoc, ← hXact g h, ← Matrix.map_mul, hXA, Matrix.map_mul, hRact, ← mul_assoc,
      map_mul ρ, Units.val_mul, Matrix.map_mul, hAgh]
  let ρ'' : ↥(GK K) →* Matrix n n ↥(MaximalUnramifiedExtension l) :=
    { toFun := fun g => Matrix.of (N g)
      map_one' := by
        have h : (Matrix.of (N 1)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) = (1 : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
          rw [hNmap, hX1, Matrix.map_one _ (map_zero _) (map_one _)]
        exact Matrix.map_injective alg_inj h
      map_mul' := fun g h => by
        have h' : (Matrix.of (N (g * h))).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) =
            (Matrix.of (N g) * Matrix.of (N h)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
          rw [Matrix.map_mul, hNmap, hNmap, hNmap, hXmul]
        exact Matrix.map_injective alg_inj h' }
  have hρ' : ∀ g, ((ρ''.toHomUnits g : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = Matrix.of (N g) := fun g => rfl
  have hmatD : ∀ (m : Fin r) g, matD P ρ''.toHomUnits m g = (X g).map (ev P m) := by
    intro m g; ext i j
    rw [matD, hρ', Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, hNeq, ev_kur]
  refine ⟨ρ''.toHomUnits, ?_, ?_, ?_⟩
  · refine { pos := hρ.pos, le := hρ.le, rat := fun g i j => hNfr g i j, cont := fun i j => ?_ }
    let m0 : Fin r := ⟨0, hρ.pos⟩
    refine FrameChange.cont_of_frame l P AI T n K (fun g => Matrix.of (N g)) (W m0) (fun j => w m0 j + e m0 j) (hWu m0)
      (fun g => ?_) i j
    rw [← hev m0 g]
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, hNeq, ev_kur]
    rfl
  · intro m
    refine ⟨(W m)⁻¹, ⟨fun i j => (hWu m).2 i j, fun i j => ?_⟩, fun g => ?_⟩
    · rw [inv_inv]; exact (hWu m).1 i j
    · rw [hmatD, hev, mul_assoc _ _ (Matrix.map _ _), ← Matrix.map_mul, Units.mul_inv,
        Matrix.map_one _ (map_zero _) (map_one _), mul_one]
  · rintro ⟨K', hK, Q', hQ'⟩
    refine ⟨K', hK, Matrix.GeneralLinearGroup.map (Polynomial.C : P.R.B →+* Bst P) A * Q', fun g => ?_⟩
    have hQg := hQ' g
    have e1 : ((Matrix.GeneralLinearGroup.map (Polynomial.C : P.R.B →+* Bst P) A : GL n (Bst P)) : Matrix n n (Bst P)) =
        (A : Matrix n n P.R.B).map (Polynomial.C : P.R.B →+* Bst P) := rfl
    have e2 : ((A : Matrix n n P.R.B).map (Polynomial.C : P.R.B →+* Bst P)).map (actSt P (g : GQ l)) =
        ((A : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (Polynomial.C : P.R.B →+* Bst P) := by
      ext i j; simp [actSt_C]
    have e3 : ∀ M : Matrix n n ↥(MaximalUnramifiedExtension l), M.map (ks P) = (M.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map
        (Polynomial.C : P.R.B →+* Bst P) := fun M => by ext; rfl
    rw [Units.val_mul, Matrix.map_mul, e1, e2, e3, ← mul_assoc, ← Matrix.map_mul, ← hXA, Matrix.map_mul, mul_assoc,
      ← hNmap, ← e3]
    exact congrArg _ hQg

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepOfFrobeniusFixedFrameChangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_of_frobeniusFixed_frame_change : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w e : Fin r → n → ℤ) (U : Fin r → GL n P.R.BdR) (A : GL n P.R.B), IsRat r ρ → (∀ (m : Fin r) (g : ↥(GK K)), matD P ρ m g * (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])) → (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) → (∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (e m j)) * (W : Matrix n n P.R.BdR)) → ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + e m j) ∧ (AdmSt P ρ' → AdmSt P ρ) := by
  first | exact @GlobalTheory.PMon.exists_rep_of_fixed_frame_change | exact GlobalTheory.PMon.exists_rep_of_fixed_frame_change | (intros; apply GlobalTheory.PMon.exists_rep_of_fixed_frame_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspace
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem vecMul_repr_rows {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul v (Matrix.of fun k j => b.repr (Pi.single k 1) j) = b.repr v := by
  ext j
  conv_rhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (v k) : n → E) = v k • Pi.single k 1 by
    ext i; by_cases h : i = k <;> simp [h]]
  simp

theorem vecMul_rows_repr {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul (b.repr v) (Matrix.of fun i j => b i j) = v := by
  ext j
  conv_rhs => rw [← b.sum_repr v]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem splits_of_stable_rat_subspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  classical
  intro l _ n _ _ K r ρ hρ W hWE hWsm hWst hW0 hWtop
  let E : Subfield ↥(MaximalUnramifiedExtension l) := RingHom.eqLocusField (fr l r) (RingHom.id _)
  let ι : E →+* ↥(MaximalUnramifiedExtension l) := E.subtype
  have hE : ∀ x : E, fr l r (x : ↥(MaximalUnramifiedExtension l)) = x := fun x => x.2
  let cv : (n → E) → (n → ↥(MaximalUnramifiedExtension l)) := fun c i => (c i : ↥(MaximalUnramifiedExtension l))
  let W' : Submodule E (n → E) :=
    { carrier := {c | cv c ∈ W}
      add_mem' := fun {c d} hc hd => by
        show cv (c + d) ∈ W
        rw [show cv (c + d) = cv c + cv d from funext fun i => by simp [cv]]
        exact W.add_mem hc hd
      zero_mem' := by
        show cv 0 ∈ W
        rw [show cv 0 = 0 from funext fun i => by simp [cv]]
        exact W.zero_mem
      smul_mem' := fun e c hc => by
        show cv (e • c) ∈ W
        rw [show cv (e • c) = (e : ↥(MaximalUnramifiedExtension l)) • cv c from funext fun i => by simp [cv, smul_eq_mul]]
        exact hWsm (e : ↥(MaximalUnramifiedExtension l)) (hE e) _ hc }
  have memW' : ∀ c, c ∈ W' ↔ cv c ∈ W := fun c => Iff.rfl
  have lift : ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∃ c' : n → E, cv c' = c :=
    fun c hc => ⟨fun i => ⟨c i, hc i⟩, rfl⟩
  have hW'0 : W' ≠ ⊥ := by
    obtain ⟨c, hcW, hc0⟩ : ∃ c ∈ W, c ≠ 0 := by
      by_contra h
      push_neg at h
      exact hW0 ((AddSubgroup.eq_bot_iff_forall W).2 h)
    obtain ⟨c', rfl⟩ := lift c (hWE c hcW)
    intro h
    have : c' ∈ W' := hcW
    rw [h, Submodule.mem_bot] at this
    exact hc0 (by subst this; rfl)
  have hW'top : W' ≠ ⊤ := by
    obtain ⟨c, hcE, hcW⟩ := hWtop
    obtain ⟨c', rfl⟩ := lift c hcE
    intro h
    exact hcW ((memW' c').1 (h ▸ Submodule.mem_top))
  obtain ⟨S, hSW, hSspan, hSli⟩ := exists_linearIndependent E (W' : Set (n → E))
  have hSli' : LinearIndepOn E id S := hSli
  let B := Module.Basis.extend hSli'
  let e := B.indexEquiv (Pi.basisFun E n)
  let b : Module.Basis n E (n → E) := B.reindex e
  have hb : ∀ i, b i = ((e.symm i : _) : n → E) := fun i => by
    rw [Module.Basis.reindex_apply]; exact Module.Basis.extend_apply_self hSli' _
  have hbS : ∀ x ∈ S, ∃ i, b i = x := fun x hx =>
    ⟨e ⟨x, Module.Basis.subset_extend hSli' hx⟩, by simp [hb]⟩
  let s : Finset n := Finset.univ.filter fun i => b i ∉ S
  have hs : ∀ i, i ∉ s ↔ b i ∈ S := fun i => by simp [s]
  have hWspan : W' ≤ Submodule.span E (b '' ((s : Set n)ᶜ)) := by
    conv_lhs => rw [← Submodule.span_eq W', ← hSspan]
    apply Submodule.span_mono
    intro x hx
    obtain ⟨i, rfl⟩ := hbS x hx
    exact ⟨i, by simpa [hs] using hx, rfl⟩
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hW'top
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hSW ((hs i).1 (by simp [h]))
  have hsuniv : s ≠ Finset.univ := by
    intro h
    apply hW'0
    have hS0 : S = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨i, rfl⟩ := hbS x hx
      exact (hs i).2 hx (by simp [h])
    rw [← Submodule.span_eq W', ← hSspan, hS0, Submodule.span_empty]
  let M : Matrix n n E := Matrix.of fun i j => b i j
  let N : Matrix n n E := Matrix.of fun k j => b.repr (Pi.single k 1) j
  have hNM : N * M = 1 := by
    refine Matrix.ext fun k j => ?_
    show Matrix.vecMul (b.repr (Pi.single k 1)) M j = _
    rw [vecMul_rows_repr]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hMN : M * N = 1 := mul_eq_one_comm.2 hNM
  let qE : GL n E := ⟨M, N, hMN, hNM⟩
  let p : GL n ↥(MaximalUnramifiedExtension l) := (Matrix.GeneralLinearGroup.map ι qE)⁻¹
  have hp : (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = N.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [← map_inv]
    rfl
  have hpinv : ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = M.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [inv_inv]
    rfl
  let R : ↥(GK K) → Matrix n n E := fun g => Matrix.of fun i j => (⟨(ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j, hρ.rat g i j⟩ : E)
  have hR : ∀ g, ((ρ g : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = (R g).map ι := fun g => by
    ext i j; rfl
  refine ⟨s, p, hsne, hsuniv, fun i j => ?_, fun g i j hi hj => ?_⟩
  · rw [hp]
    exact hE (N i j)
  · rw [Units.val_mul, Units.val_mul, hpinv, hR, hp, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    suffices h : (M * R g * N) i j = 0 by rw [h, map_zero]
    show Matrix.vecMul (Matrix.vecMul (b i) (R g)) N j = 0
    rw [vecMul_repr_rows]
    have hw : Matrix.vecMul (b i) (R g) ∈ W' := by
      rw [memW']
      have h1 : cv (b i) ∈ W := hSW ((hs i).1 hi)
      have h2 := hWst g _ h1
      convert h2 using 1
      funext k
      show ι (Matrix.vecMul (b i) (R g) k) = Matrix.vecMul (cv (b i)) (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, map_sum, map_mul]
      rfl
    have := (Module.Basis.mem_span_image b).1 (hWspan hw)
    by_contra hne
    exact this ((Finsupp.mem_support_iff).2 hne) (by simpa using hj)

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducible_of_stable_rational_rowSubspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  first | exact @GlobalTheory.PMon.splits_of_stable_rat_subspace | exact GlobalTheory.PMon.splits_of_stable_rat_subspace | (intros; apply GlobalTheory.PMon.splits_of_stable_rat_subspace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramified
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResIndep

variable {l : ℕ} [Fact l.Prime]

theorem fr_bijective (l : ℕ) [Fact l.Prime] (m : ℕ) : Function.Bijective (fr l m) := by
  have e : (fr l m : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l)) = (frobUr l)^[m] := by
    funext c
    simp [fr, AlgHom.coe_pow]
  rw [e]
  exact frobUr_bijective.iterate m

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def resS (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : P.R.BdR := ∑ i, kd P (fr l m (d i)) * u i

theorem resS_zero (m : ℕ) (u : n → P.R.BdR) : resS P m u 0 = 0 := by simp [resS]

theorem resS_add (m : ℕ) (u : n → P.R.BdR) (d e : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (d + e) = resS P m u d + resS P m u e := by
  simp [resS, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem resS_neg (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : resS P m u (-d) = -resS P m u d := by
  simp [resS, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem resS_smul (m : ℕ) (u : n → P.R.BdR) (e : ↥(MaximalUnramifiedExtension l)) (d : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (e • d) = kd P (fr l m e) * resS P m u d := by
  simp [resS, Finset.mul_sum, mul_assoc]

def resW (r m : ℕ) (u : n → P.R.BdR) : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)) where
  carrier := {d | (∀ i, fr l r (d i) = d i) ∧ resS P m u d ∈ Fil P 1}
  zero_mem' := ⟨fun i => by simp, by rw [resS_zero]; exact Fil_zero_mem 1⟩
  add_mem' := fun {x y} hx hy => ⟨fun i => by simp [hx.1 i, hy.1 i], by rw [resS_add]; exact Fil_add hx.2 hy.2⟩
  neg_mem' := fun {x} hx => ⟨fun i => by simp [hx.1 i], by rw [resS_neg]; exact Fil_neg hx.2⟩

theorem rat_vecMul {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (d : n → ↥(MaximalUnramifiedExtension l))
    (hd : ∀ i, fr l r (d i) = d i) (g : ↥(GK K)) (j : n) :
    fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j := by
  change fr l r (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = ∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hd, hR.rat]

theorem key {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (m : ℕ) (u : n → P.R.BdR) (a : ℤ)
    (g : ↥(GK K))
    (hrel : (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u)
    (d : n → ↥(MaximalUnramifiedExtension l)) (hd : ∀ i, fr l r (d i) = d i)
    (h : resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) ∈ Fil P 1) : resS P m u d ∈ Fil P 1 := by
  set q : ℚ_[l]ˣ := P.χQ (g : GQ l) ^ a with hq
  have hi : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * u i =
      ∑ j, kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j) := by
    intro i
    have := congrFun hrel i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, matD, Matrix.map_apply] at this
    exact this.symm
  have hfix : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j))) =
      kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) := fun j =>
    act_kd P g (hR.le _ (fr_comm (rat_vecMul hR d hd g j) m))
  have e1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d =
      P.actQdR (g : GQ l) (resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)))) := by
    have hR' : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) * u j) =
        ∑ i, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro j
      rw [map_mul, hfix j]
      change kd P (fr l m (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, mul_assoc]
    have hL : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * (kd P (fr l m (d i)) * u i) =
        ∑ j, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro i
      rw [mul_left_comm, hi i, Finset.mul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [resS, resS, map_sum, Finset.mul_sum]
    simp_rw [hR', hL]
    exact Finset.sum_comm
  have h1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d ∈ Fil P 1 := e1 ▸ Fil_act (g : GQ l) h
  have h2 := Fil_mul_left (q_mem_Fil P ((q⁻¹ : ℚ_[l]ˣ) : ℚ_[l])) h1
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h2

end GlobalTheory.PMon.ResIndep

namespace GlobalTheory.PMon


open GlobalTheory.PMon.ResIndep in
theorem residue_indep_of_not_splits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  intro l _ P AI T n _ _ K r ρ m u a hR hNS _ hu1 hrel c hc hS
  by_contra hc0
  apply hNS
  have hbij := fr_bijective l m
  refine GlobalTheory.T.reducible_of_stable_rational_rowSubspace l n K r ρ hR (resW P r m u) (fun d hd => hd.1) ?_ ?_ ?_ ?_
  · intro e he d hd
    refine ⟨fun i => ?_, ?_⟩
    · simp [Pi.smul_apply, smul_eq_mul, map_mul, he, hd.1 i]
    · rw [resS_smul]
      exact Fil_mul_left (kd_mem_Fil P _) hd.2
  · intro g d hd
    have hd1 : ∀ i, fr l r (d i) = d i := hd.1
    have hd' : ∀ j, fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j :=
      rat_vecMul hR d hd1 g
    refine ⟨hd', key P hR m u a g⁻¹ (hrel g⁻¹) _ hd' ?_⟩
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]
    exact hd.2
  · choose d hd using fun i => hbij.2 (c i)
    have hdr : ∀ i, fr l r (d i) = d i := fun i => hbij.1 (by
      rw [← fr_add, add_comm, fr_add, hd i, hc i])
    intro hbot
    have hmem : d ∈ resW P r m u := ⟨hdr, by
      change ∑ i, kd P (fr l m (d i)) * u i ∈ Fil P 1
      simpa only [hd] using hS⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    apply hc0
    funext i
    rw [← hd i, hmem]
    simp
  · obtain ⟨i0, hi0⟩ := hu1
    refine ⟨Pi.single i0 1, fun i => ?_, fun hmem => hi0 ?_⟩
    · by_cases h : i = i0
      · subst h; simp
      · simp [h]
    · have e : resS P m u (Pi.single i0 1) = u i0 := by
        simp [resS, Pi.single_apply]
      rw [← e]
      exact hmem.2

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_indep_of_not_reducibleOverUnramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  first | exact @GlobalTheory.PMon.residue_indep_of_not_splits | exact GlobalTheory.PMon.residue_indep_of_not_splits | (intros; apply GlobalTheory.PMon.residue_indep_of_not_splits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModification
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem modStep_holds : ModStep := by
  intro l _ P AI T n _ _ K r ρ w x y hxy hR hF hS
  choose U hU hUe using hF
  obtain ⟨hfield, -, -, -, hval, hmul, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  haveI : Nontrivial P.R.BdR := ⟨hfield.exists_pair_ne⟩
  have hsum : ∀ (s : Finset n) (f : n → P.R.BdR), (∀ k ∈ s, f k ∈ Fil P 1) → ∑ k ∈ s, f k ∈ Fil P 1 := by
    intro s f hf
    unfold Fil at *
    exact sum_mem hf
  have h1 : (1 : P.R.BdR) ∉ Fil P 1 := by
    intro h
    obtain ⟨a, ha, ha'⟩ := hval 1 one_ne_zero
    exact ha' (by simpa using hmul a 1 1 1 ha h)
  have hcol : ∃ i, (U x.1 : Matrix n n P.R.BdR) i x.2 ∉ Fil P 1 := by
    by_contra hc
    push_neg at hc
    have hinv : (((U x.1)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * (U x.1 : Matrix n n P.R.BdR) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have he := congrFun (congrFun hinv x.2) x.2
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at he
    apply h1
    rw [← he]
    apply hsum
    intro k _
    simpa using hmul 0 1 _ _ ((hU x.1).2 x.2 k) (hc k)
  have heig : ∀ g : ↥(GK K), (matD P ρ (x.1 : ℕ) g).mulVec
      (fun i => P.actQdR (g : GQ l) ((U x.1 : Matrix n n P.R.BdR) i x.2)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w x.1 x.2 : ℚ_[l]ˣ) : ℚ_[l]) •
        (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) := by
    intro g
    funext i
    have h := congrFun (congrFun (hUe x.1 g) i) x.2
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
    simp only [Matrix.map_apply] at h
    rw [Matrix.mulVec, dotProduct, h, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hind := GlobalTheory.T.residue_indep_of_not_reducibleOverUnramified l P AI T n K r ρ (x.1 : ℕ) (fun i => (U x.1 : Matrix n n P.R.BdR) i x.2) (w x.1 x.2)
    hR hS (fun i => (hU x.1).1 i x.2) hcol heig
  obtain ⟨A, hA, hW⟩ := GlobalTheory.T.fundamentalLemmaLatticeFrobFixed_forall_degree r l P AI T n U x y hxy (fun m => hU m) hind
  exact GlobalTheory.T.exists_rep_of_frobeniusFixed_frame_change l P AI T n K r ρ w (fun m j => eps x y (m, j)) U A hR hUe hA hW

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModificationStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_irreducible_elementary_weightModification : ModStep := by
  first | exact @GlobalTheory.PMon.modStep_holds | exact GlobalTheory.PMon.modStep_holds | (intros; apply GlobalTheory.PMon.modStep_holds <;> assumption)
end
