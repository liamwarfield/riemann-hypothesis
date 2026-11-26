module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PEmbAll
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.embAll_of :
    UpperTheory.Gal.W2.EmbAll := by
  intro p _ G τ
  rcases HTGroupOver.liesOver_or_conj p G τ with h | h
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ h
    refine ⟨i, σ, Or.inl fun x => ?_⟩
    rw [hσ]
    rfl
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ h
    refine ⟨i, σ, Or.inr fun x => ?_⟩
    have hx := congrArg (fun f : G.F →+* PadicAlgCl p => f (IsCMField.complexConj G.F x)) hσ
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      conjQ_apply] at hx
    have hc : (conjQ G.F).toRingHom ((IsCMField.complexConj G.F) x) = x := by
      simp [conjQ_apply]
    rw [hc] at hx
    exact hx
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PKpMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mem_intK_iff {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    a ∈ GlobalTheory.LKLoc.intK p K ↔ ‖(a : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff

theorem UpperTheory.Gal.W2.kpMem_of :
    UpperTheory.Gal.W2.KpMem := by
  intro p _ G g
  rw [GlobalTheory.HeckeP.inclG_mem_KHT_iff]
  unfold UpperTheory.Gal.W2.IntPt
  have hunit : (‖(g.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ↔ ‖(g.1 : ℚ_[p])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ‖(g.1 : ℚ_[p])‖ := norm_pos_iff.2 g.1.ne_zero
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 (by simpa using (inv_le_one₀ hpos).1 h2)
    · intro h
      rw [h]
      simp
  rw [hunit]
  apply and_congr_right'
  apply forall_congr'
  intro w
  unfold GlobalTheory.LKLoc.KintK
  rw [GlobalTheory.HeckeP.mem_range_map_subtype]
  simp only [mem_intK_iff]
  rw [← forall_and]
  apply forall_congr'
  intro i
  rw [← forall_and]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PMemDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.memDual_of :
    UpperTheory.Gal.W2.TrDual → UpperTheory.Gal.W2.MemDual := by
  intro h p _ G
  choose d hd0 hd using fun w : Fin G.m => h p G w
  refine ⟨d, hd0, fun a => ?_⟩
  constructor
  · intro ha w i
    have key := (hd w (a w i)).1 (fun z0 hz0 => by
      have hz : IntL (Pi.single w (Pi.single i z0) : Loc G) := by
        intro w' j
        by_cases hw : w' = w
        · subst hw
          by_cases hj : j = i
          · subst hj
            simpa using hz0
          · simp [Pi.single_apply, hj]
        · simp [Pi.single_apply, hw]
      have hp := ha _ hz
      have he : pairL a (Pi.single w (Pi.single i z0) : Loc G) =
          Algebra.trace ℚ_[p] (G.Fw w) (a w i * z0) := by
        unfold pairL
        rw [Finset.sum_eq_single w]
        · simp
        · intro w' _ hw'
          simp [Pi.single_apply, hw']
        · simp
      rwa [he] at hp)
    simpa [mul_comm] using key
  · intro ha z hz
    unfold pairL
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro w _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro i _
    have hai : ‖((a w i * d w : G.Fw w) : PadicAlgCl p)‖ ≤ 1 := by
      simpa [mul_comm] using ha w i
    exact (hd w (a w i)).2 hai (z w i) (hz w i)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.pkTop_of :
    UpperTheory.Gal.W2.PFrameEx → UpperTheory.Gal.W2.PkLat → UpperTheory.Gal.W2.PkEquiv → UpperTheory.Gal.W2.PkPerf → UpperTheory.Gal.W2.PkInj → UpperTheory.Gal.W2.PkOnto → UpperTheory.Gal.W2.KpMem → UpperTheory.Gal.W2.PDicEx := by
  intro hF hLat hEq hPerf hInj hOnto hKp p _ D G L _ hm B
  obtain ⟨A⟩ := hF p D G L hm B.β B.sym
  let i : Gp G ≃* Gr G 1 := MulEquiv.ofBijective (inclG G 1) (GlobalTheory.TorCls.AtP.inclG_one_bijective G)
  have hi : ∀ g, i g = inclG G 1 g := fun _ => rfl
  choose M hM hMl using hLat p D G L B.β A hm
  refine ⟨{ lat := fun hp => M (i.symm hp), isLat := fun hp => hMl _, perf := ?_, equiv := ?_, inj := ?_, onto := ?_ }⟩
  · intro hp
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hp1 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    set g := i.symm hp with hg
    set v : ℤ := (g.1 : ℚ_[p]).valuation with hv
    refine ⟨(p : ℚ) ^ (-v), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, ?_⟩
    refine hPerf p D G L B.β A g _ ?_ _ (hM g)
    have hne : (g.1 : ℚ_[p]) ≠ 0 := g.1.ne_zero
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hne, ← hv]
    push_cast
    rw [norm_zpow, Padic.norm_p, inv_zpow', neg_neg, ← zpow_add₀ hp1.ne']
    simp
  · intro y hp w
    have e : i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp) = locC G (y : G.Cˣ × ℚˣ) * i.symm hp := by
      rw [map_mul]
      congr 1
      exact i.symm_apply_apply (locC G (y : G.Cˣ × ℚˣ))
    change actY L y w ∈ M (i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp)) ↔ w ∈ M (i.symm hp)
    rw [e, hM, hM]
    exact hEq p D G L B.β A y _ w
  · intro hp hp'
    have e : hp⁻¹ * hp' = inclG G 1 ((i.symm hp)⁻¹ * i.symm hp') := by
      rw [← hi, map_mul, map_inv, i.apply_symm_apply, i.apply_symm_apply]
    change M (i.symm hp) = M (i.symm hp') ↔ _
    rw [e, hKp p G, ← hInj p D G L B.β A]
    constructor
    · intro h x
      rw [← hM, ← hM, h]
    · intro h
      ext x
      rw [hM, hM]
      exact h x
  · rintro N hN ⟨s, hs, hP⟩
    obtain ⟨g, hg⟩ := hOnto p D G L B.β A hm N s hN hs hP
    refine ⟨i g, ?_⟩
    change M (i.symm (i g)) = N
    rw [i.symm_apply_apply]
    ext x
    rw [hM, hg]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPkEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_ratCast {p : ℕ} [Fact p.Prime] (G : HTGroup p) (w : Fin G.m) (s : ℚ) :
    G.rho w (algebraMap ℚ G.C s) = Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) (algebraMap ℚ ℚ_[p] s)) := by
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C s, G.rho_F w]
  congr 1
  rw [eq_ratCast (algebraMap ℚ G.F) s, eq_ratCast (algebraMap ℚ ℚ_[p]) s, map_ratCast, map_ratCast]

private theorem pairL_move {p : ℕ} [Fact p.Prime] (G : HTGroup p) (M N : ∀ w : Fin G.m, Matrix (Fin G.n) (Fin G.n) (G.Fw w))
    (s : ℚ_[p]) (h : ∀ w, M w * N w = Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) s)) (a b : Loc G) :
    pairL (fun w => (M w)ᵀ *ᵥ a w) (fun w => N w *ᵥ b w) = s * pairL a b := by
  unfold pairL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ((M w)ᵀ *ᵥ a w) ⬝ᵥ (N w *ᵥ b w) = s • (a w ⬝ᵥ b w) := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h w,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, Algebra.smul_def]
  rw [e, map_smul, smul_eq_mul]

private theorem mem_move {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ} (A : PFrame L β)
    (u : G.Cˣ) (s : ℚˣ) (hy : (u : G.C) * β * sh G u = algebraMap ℚ G.C s * β) (g g' : Gp G) (x : VQ D)
    (h1 : g'.1 = Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s * g.1)
    (h2 : ∀ w, g'.2 w = Units.map (G.rho w).toMonoidHom u * g.2 w) :
    A.Mem g' (L.rep (u : G.C) x) ↔ A.Mem g x := by
  have hk : (β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C) = ((u⁻¹ : G.Cˣ) : G.C) * algebraMap ℚ G.C s := by
    calc (β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)
        = ((u⁻¹ : G.Cˣ) : G.C) * ((u : G.C) * β * sh G u) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [_root_.mul_assoc, Units.inv_mul_cancel_left]
      _ = _ := by
          rw [hy]
          simp only [_root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have hM : ∀ w, G.rho w ((β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)) * G.rho w (u : G.C) =
      Matrix.scalar (Fin G.n) (algebraMap ℚ_[p] (G.Fw w) (algebraMap ℚ ℚ_[p] s)) := by
    intro w
    rw [hk, ← map_mul, ← Algebra.commutes, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, rho_ratCast]
  have t1 : ∀ w, (((g'.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T (L.rep (u : G.C) x) w =
      (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w := by
    intro w
    have hu : (((Units.map (G.rho w).toMonoidHom u)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *
        G.rho w (u : G.C) = 1 := Units.inv_mul (Units.map (G.rho w).toMonoidHom u)
    rw [h2 w, _root_.mul_inv_rev, Units.val_mul, A.act, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ _ (G.rho w (u : G.C)), hu,
      Matrix.one_mulVec]
  have e1 : ((g'.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℚ ℚ_[p] s = ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) := by
    have hs : (((Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * algebraMap ℚ ℚ_[p] s = 1 :=
      Units.inv_mul (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom s)
    rw [h1, _root_.mul_inv_rev, Units.val_mul, _root_.mul_assoc, hs, _root_.mul_one]
  have t2 : ∀ z : Loc G, ((g'.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' (L.rep (u : G.C) x))
        (fun w => (g'.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) =
      ((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) := by
    intro z
    have a1 : A.T' (L.rep (u : G.C) x) = fun w =>
        (G.rho w ((β : G.C) * sh G u * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ A.T' x w := funext fun w => A.act' _ x w
    have a2 : (fun w => (g'.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) = fun w =>
        G.rho w (u : G.C) *ᵥ ((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w) := by
      funext w
      rw [h2 w, Units.val_mul, ← Matrix.mulVec_mulVec]
      rfl
    rw [a1, a2, pairL_move G _ _ _ hM, ← _root_.mul_assoc, e1]
  refine and_congr (iff_of_eq (congrArg IntL (funext t1))) (forall_congr' fun z => imp_congr_right fun _ => ?_)
  rw [t2 z]

theorem UpperTheory.Gal.W2.pkEquiv_of :
    UpperTheory.Gal.W2.PkEquiv := by
  intro p _ D G L β A y g x
  exact mem_move A y.1.1 y.1.2 y.2.1 g _ x rfl (fun _ => rfl)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPLatOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem plat_core {V : Type} [AddCommGroup V] [Module ℚ V] (p : ℕ) (hp : p ≠ 0) (M : AddSubgroup V)
    (s : Finset V) (k : ℕ) (hs : Submodule.span ℚ (s : Set V) = ⊤)
    (hsat : ∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M)
    (h1 : ∀ x ∈ s, p ^ k • x ∈ M)
    (h2 : ∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set V)) :
    ∃ t : Finset V, Submodule.span ℚ (t : Set V) = ⊤ ∧
      ∀ w, w ∈ M ↔ ∃ m : ℕ, m.Coprime p ∧ m • w ∈ AddSubgroup.closure (t : Set V) := by
  have hpk : ((p : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp)
  set q : ℚ := ((p : ℚ) ^ k)⁻¹ with hq
  let f : V →ₗ[ℤ] V := (LinearMap.lsmul ℚ V q).toAddMonoidHom.toIntLinearMap
  have hf : ∀ x, f x = q • x := fun x => rfl
  set W : Submodule ℤ V := Submodule.span ℤ (f '' (s : Set V)) with hW
  have hWfg : W.FG := Submodule.fg_span ((s.finite_toSet).image f)
  haveI : IsNoetherian ℤ W := isNoetherian_of_fg_of_noetherian W hWfg
  have hNfg : (AddSubgroup.toIntSubmodule M ⊓ W).FG :=
    Submodule.FG.of_le_of_isNoetherian inf_le_right
  obtain ⟨t, ht⟩ := hNfg
  have hcl : ∀ y, y ∈ AddSubgroup.closure (t : Set V) ↔ y ∈ M ∧ y ∈ W := by
    intro y
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, ht,
      Submodule.mem_inf]
    rfl
  have hsW : ∀ y ∈ AddSubgroup.closure (s : Set V), q • y ∈ W := by
    intro y hy
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup] at hy
    have hy' : f y ∈ (Submodule.span ℤ (s : Set V)).map f := Submodule.mem_map_of_mem hy
    rw [Submodule.map_span] at hy'
    rw [← hf]
    exact hy'
  refine ⟨t, ?_, fun w => ⟨fun hw => ?_, fun ⟨m, hm, hmw⟩ => hsat m w hm ((hcl _).1 hmw).1⟩⟩
  · rw [eq_top_iff, ← hs, Submodule.span_le]
    intro x hx
    have hx1 : p ^ k • x ∈ M := h1 x hx
    have e : p ^ k • x = q • ((p ^ k * p ^ k) • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    have hx2 : p ^ k • x ∈ W := by
      rw [e]
      exact hsW _ (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure hx) _)
    have hmem : p ^ k • x ∈ Submodule.span ℚ (t : Set V) :=
      (AddSubgroup.closure_le (K := (Submodule.span ℚ (t : Set V)).toAddSubgroup)).2
        Submodule.subset_span ((hcl _).2 ⟨hx1, hx2⟩)
    have e2 : x = q • (p ^ k • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      push_cast
      rw [hq, inv_mul_cancel₀ hpk, one_smul]
    show x ∈ Submodule.span ℚ (t : Set V)
    rw [e2]
    exact Submodule.smul_mem _ q hmem
  · obtain ⟨m, hm, hmem⟩ := h2 w hw
    refine ⟨m, hm, (hcl _).2 ⟨M.nsmul_mem hw m, ?_⟩⟩
    have e : m • w = q • ((m * p ^ k) • w) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [hq, _root_.mul_comm (m : ℚ), ← _root_.mul_assoc, inv_mul_cancel₀ hpk, _root_.one_mul]
    rw [e]
    exact hsW _ hmem

theorem UpperTheory.Gal.W2.pLatOf_of :
    UpperTheory.Gal.W2.PLatOf := by
  intro p _ D M s k hs hO hsat h1 h2
  exact ⟨hO, plat_core p (Fact.out : p.Prime).ne_zero M s k hs hsat h1 h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.POOnto
noncomputable section

open NumberField
open scoped TensorProduct Matrix Classical
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.W2

private theorem tens_inj (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] :
    Function.Injective (fun x : O => x ⊗ₜ[ℤ] (1 : ℤ_[p])) := by
  have hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p]) := by
    intro a b h
    exact RingHom.injective_int (algebraMap ℤ ℤ_[p]) h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj
  intro x y hxy
  have h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ) := h1 (by simpa using hxy)
  have h3 := congrArg (TensorProduct.rid ℤ O) h2
  simpa using h3

private theorem comm_of_split (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] {R : Type} [CommRing R]
    {m : ℕ} (hm : m = 1) (f : (O ⊗[ℤ] ℤ_[p]) ≃+* Matrix (Fin m) (Fin m) R) (x y : O) : x * y = y * x := by
  subst hm
  apply tens_inj p
  have hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A := by
    intro A B
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  have := hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))
  rw [← map_mul, ← map_mul] at this
  have h2 := f.injective this
  simpa using h2

private theorem a_inj {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] : Function.Injective (algebraMap (𝓞 F) O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥ := fun h => h0 (by
    have h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O) := hc
    rw [h] at h1
    simpa using h1)
  have hN := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))
  have hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  rw [RingHom.mem_ker, map_natCast] at hN
  have h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0 := by
    rw [zsmul_one]
    exact_mod_cast hN
  rcases smul_eq_zero.mp h1 with h | h
  · exact hN0 (by exact_mod_cast h)
  · exact one_ne_zero h

private theorem a_onto {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hcomm : ∀ x y : O, x * y = y * x)
    (hc : ∀ x : O, ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  intro x
  obtain ⟨c, e, he, hx⟩ := hc x
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  obtain ⟨P, hP, hPx⟩ : IsIntegral ℤ x := IsIntegral.of_finite ℤ x
  have hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 := by
    rw [Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hx]; simp [zsmul_eq_mul]
  have hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0 := by
    apply a_inj (O := O)
    rw [map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]
    congr 1
    exact RingHom.ext_int _ _
  have hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) hQ2
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [← this]
    congr 1
  have heF : (algebraMap ℤ F e) ≠ 0 := by simpa using he
  have hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e) := by field_simp
  rw [hcF, Polynomial.scaleRoots_eval₂_mul] at hQ3
  have hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e) :=
    ⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩
  obtain ⟨c', hc'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨c', ?_⟩
  have hcc : c = e • c' := by
    apply RingOfIntegers.ext
    rw [hcF, ← hc']
    simp [zsmul_eq_mul]
  have h3 : e • (algebraMap (𝓞 F) O c' - x) = 0 := by
    rw [smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h he
  · exact sub_eq_zero.mp h

theorem oOnto_of : OOnto := by
  intro p _ D hm
  haveI := D.freeO
  haveI := D.finO
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]
    simpa using hd
  obtain ⟨f⟩ := D.splitP
  have hcomm : ∀ x y : D.O, x * y = y * x := comm_of_split p hm f.toRingEquiv
  exact a_onto hcomm fun x => D.central x (hcomm x)

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFTrace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.FrobeniusTrace

variable {p : ℕ} [Fact p.Prime]

private theorem not_both (G : HTGroup p) (τ : G.F →+* PadicAlgCl p) (h1 : LiesOver G.Kq G.u τ)
    (h2 : LiesOver G.Kq G.u (τ.comp (IsCMField.complexConj G.F : G.F →+* G.F))) : False := by
  obtain ⟨x, hx, hne⟩ := CentAtP.exists_conj_ne G
  apply hne
  apply τ.injective
  have a := h1 ⟨x, hx⟩
  have b := h2 ⟨x, hx⟩
  exact b.trans a.symm

private theorem exists_ext (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (s : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ y : E, σ (y : PadicAlgCl p) = s y := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun z => ⟨Algebra.IsIntegral.isIntegral z, IsAlgClosed.splits _⟩) s
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact congrArg (fun f => f y) hφ

private theorem hom_ext {F : Type} [Field F] (τ : F →+* PadicAlgCl p)
    (s s' : FwOf τ →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (embOf τ x) = s' (embOf τ x)) : s = s' := by
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[p]
    (rfl : FwOf τ = IntermediateField.adjoin ℚ_[p] (Set.range τ)) ?_
  rintro _ ⟨x, rfl⟩
  exact h x

private theorem sigma_eq (G : HTGroup p) {w w' : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)
    (s' : G.Fw w' →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (G.embW w x) = s' (G.embW w' x)) :
    (⟨w, s⟩ : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) = ⟨w', s'⟩ := by
  obtain ⟨σ, hσ⟩ := exists_ext _ s
  obtain ⟨σ', hσ'⟩ := exists_ext _ s'
  have hw : w = w' := by
    refine G.emb_inj w w' (σ.trans σ'.symm) (RingHom.ext fun x => ?_)
    have e1 : σ (G.emb w x) = s (G.embW w x) := hσ (G.embW w x)
    have e2 : σ' (G.emb w' x) = s' (G.embW w' x) := hσ' (G.embW w' x)
    change σ'.symm (σ (G.emb w x)) = G.emb w' x
    rw [e1, h, ← e2, AlgEquiv.symm_apply_apply]
  subst hw
  rw [hom_ext (G.emb w) s s' h]

private theorem liesOver_comp (G : HTGroup p) {w : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    LiesOver G.Kq G.u ((s : G.Fw w →+* PadicAlgCl p).comp (G.embW w)) := by
  intro x
  have e : G.embW w (x : G.F) = algebraMap ℚ_[p] (G.Fw w) (G.u x) := Subtype.ext (G.emb_over w x)
  change s (G.embW w (x : G.F)) = _
  rw [e, s.commutes]

private noncomputable def phi (G : HTGroup p) :
    ((Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) ⊕ (Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) →
      (G.F →ₐ[ℚ] PadicAlgCl p)
  | .inl a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1)).toRatAlgHom
  | .inr a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp
      ((G.embW a.1).comp (IsCMField.complexConj G.F : G.F →+* G.F))).toRatAlgHom

private theorem phi_inl (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inl a) x = a.2 (G.embW a.1 x) := rfl

private theorem phi_inr (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inr a) x = a.2 (G.embW a.1 (IsCMField.complexConj G.F x)) := rfl

private theorem phi_ne (G : HTGroup p) (a b : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    phi G (.inl a) ≠ phi G (.inr b) := by
  intro h
  refine not_both G _ (liesOver_comp G a.2) fun k => ?_
  have e := DFunLike.congr_fun h (IsCMField.complexConj G.F (k : G.F))
  rw [phi_inl, phi_inr, IsCMField.complexConj_apply_apply] at e
  exact e.trans (liesOver_comp G b.2 k)

private theorem phi_injective (G : HTGroup p) : Function.Injective (phi G) := by
  rintro (⟨w, s⟩ | ⟨w, s⟩) (⟨w', s'⟩ | ⟨w', s'⟩) hab
  · rw [sigma_eq G s s' fun x => (phi_inl G ⟨w, s⟩ x).symm.trans
      ((DFunLike.congr_fun hab x).trans (phi_inl G ⟨w', s'⟩ x))]
  · exact absurd hab (phi_ne G _ _)
  · exact absurd hab.symm (phi_ne G _ _)
  · have key : ∀ y, s (G.embW w y) = s' (G.embW w' y) := by
      intro y
      have e := (phi_inr G ⟨w, s⟩ (IsCMField.complexConj G.F y)).symm.trans
        ((DFunLike.congr_fun hab _).trans (phi_inr G ⟨w', s'⟩ _))
      rwa [IsCMField.complexConj_apply_apply] at e
    rw [sigma_eq G s s' key]

private theorem phi_surjective (hE : EmbAll) (G : HTGroup p) : Function.Surjective (phi G) := by
  intro ψ
  obtain ⟨w, σ, h | h⟩ := hE p G ψ.toRingHom
  · refine ⟨.inl ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inl]
    exact (h x).symm
  · refine ⟨.inr ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inr]
    exact (h x).symm

end UpperTheory.Gal.W2.FrobeniusTrace

open UpperTheory.Gal.W2.FrobeniusTrace in
theorem UpperTheory.Gal.W2.fTrace_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FTrace := by
  intro hE p _ G x
  apply (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, map_sum]
  have hl : algebraMap ℚ_[p] (PadicAlgCl p) ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p])
      = algebraMap ℚ (PadicAlgCl p) (Algebra.trace ℚ G.F x) := by
    simp only [map_ratCast, eq_ratCast]
  rw [hl]
  simp_rw [trace_eq_sum_embeddings (E := PadicAlgCl p)]
  rw [← Fintype.sum_bijective (phi G) ⟨phi_injective G, phi_surjective hE G⟩
    (fun a => phi G a x) (fun σ => σ x) (fun _ => rfl)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [phi_inl, phi_inr]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTrDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_inverse_different (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ↔
        ‖((a * d : K) : PadicAlgCl p)‖ ≤ 1 := by
  classical
  have hpos : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hmin : ∀ z : K, minpoly ℚ_[p] (z : PadicAlgCl p) = minpoly ℚ_[p] z := fun z =>
    minpoly.algebraMap_eq (algebraMap K (PadicAlgCl p)).injective z
  have hsv : ∀ z : K, ‖(z : PadicAlgCl p)‖ = spectralValue (minpoly ℚ_[p] z) := by
    intro z
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, hmin]
  have hnat : ∀ m : ℕ, ‖(m : ℚ_[p])‖ ≤ 1 := fun m => by
    simpa using Padic.norm_int_le_one (p := p) (m : ℤ)
  have hTr : ∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K z‖ ≤ 1 := by
    intro z hz
    rw [hsv, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral z))] at hz
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, norm_mul, norm_neg]
    have h2 : ‖(minpoly ℚ_[p] z).nextCoeff‖ ≤ 1 := by
      unfold Polynomial.nextCoeff
      split_ifs
      · simp
      · exact hz _
    calc _ ≤ 1 * 1 := mul_le_mul (hnat _) h2 (norm_nonneg _) zero_le_one
      _ = 1 := _root_.one_mul 1
  have hdisc : ∀ x : K, x ≠ 0 → ∃ j : ℤ,
      ‖(x : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j := by
    intro x hx
    have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
    have hdpos : 0 < (minpoly ℚ_[p] x).natDegree := minpoly.natDegree_pos hint
    have hdle : (minpoly ℚ_[p] x).natDegree ≤ Module.finrank ℚ_[p] K := minpoly.natDegree_le x
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdle
    have hc0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
    have hx1 : ‖(x : PadicAlgCl p)‖ =
        ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / ((minpoly ℚ_[p] x).natDegree : ℝ)) := by
      rw [← PadicAlgCl.spectralNorm_eq,
        spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) (x : PadicAlgCl p),
        hmin]
    have hx2 : ‖(x : PadicAlgCl p)‖ ^ (minpoly ℚ_[p] x).natDegree = ‖(minpoly ℚ_[p] x).coeff 0‖ := by
      rw [hx1, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hdpos.ne']
    refine ⟨-((minpoly ℚ_[p] x).coeff 0).valuation * c, ?_⟩
    rw [hc, pow_mul, hx2, Padic.norm_eq_zpow_neg_valuation hc0, ← zpow_natCast, ← zpow_mul]
  have hn0 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  set c : ℚ_[p] := ((p : ℚ_[p]) * (Module.finrank ℚ_[p] K : ℕ))⁻¹ with hcdef
  have hbd : ∀ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) →
        ‖(a : PadicAlgCl p)‖ < ‖c‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have ha0 : (a : PadicAlgCl p) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlt
      exact absurd hlt (not_le.2 (norm_pos_iff.2 (inv_ne_zero (mul_ne_zero hp0 hn0))))
    have ha0' : a ≠ 0 := fun h => ha0 (by simp [h])
    have hz := ha (algebraMap ℚ_[p] K c * a⁻¹) (by
      rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv]
      have hcn : ‖((algebraMap ℚ_[p] K c : K) : PadicAlgCl p)‖ = ‖c‖ :=
        PadicAlgCl.norm_extends p c
      rw [hcn, ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 ha0)]
      exact hlt)
    have e2 : a * (algebraMap ℚ_[p] K c * a⁻¹) = algebraMap ℚ_[p] K c := by
      rw [_root_.mul_comm, _root_.mul_assoc, inv_mul_cancel₀ ha0', _root_.mul_one]
    rw [e2, Algebra.trace_algebraMap, nsmul_eq_mul] at hz
    have e3 : ((Module.finrank ℚ_[p] K : ℕ) : ℚ_[p]) * c = (p : ℚ_[p])⁻¹ := by
      rw [hcdef]
      field_simp
    rw [e3, norm_inv, Padic.norm_p, inv_inv] at hz
    linarith
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt (‖c‖ ^ (Module.finrank ℚ_[p] K).factorial) hpos
  have hex := Int.exists_greatest_of_bdd (P := fun j : ℤ => ∃ a : K,
      (∀ z : K, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] K (a * z)‖ ≤ 1) ∧ a ≠ 0 ∧
        ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial = (p : ℝ) ^ j)
    ⟨B, fun j ⟨a, ha, _, hj⟩ => by
      have h1 : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial <
          ‖c‖ ^ (Module.finrank ℚ_[p] K).factorial :=
        pow_lt_pow_left₀ (hbd a ha) (norm_nonneg _) (Nat.factorial_ne_zero _)
      rw [hj] at h1
      have h2 : (p : ℝ) ^ j < (p : ℝ) ^ (B : ℤ) := by
        rw [zpow_natCast]
        exact h1.trans hB
      exact ((zpow_lt_zpow_iff_right₀ hpos).1 h2).le⟩
    ⟨0, 1, fun z hz => by rw [_root_.one_mul]; exact hTr z hz, one_ne_zero, by simp⟩
  obtain ⟨jm, ⟨am, hamD, ham0, hamj⟩, hmax⟩ := hex
  have hamn : (am : PadicAlgCl p) ≠ 0 := fun h => ham0 (by exact_mod_cast h)
  refine ⟨am⁻¹, inv_ne_zero ham0, fun a => ?_⟩
  have key : ‖((a * am⁻¹ : K) : PadicAlgCl p)‖ ≤ 1 ↔
      ‖(a : PadicAlgCl p)‖ ≤ ‖(am : PadicAlgCl p)‖ := by
    rw [IntermediateField.coe_mul, IntermediateField.coe_inv, norm_mul, norm_inv,
      ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 hamn)]
  rw [key]
  constructor
  · intro ha
    by_cases ha0 : a = 0
    · simp [ha0]
    obtain ⟨j, hj⟩ := hdisc a ha0
    have hjle := hmax j ⟨a, ha, ha0, hj⟩
    have hle : ‖(a : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial ≤
        ‖(am : PadicAlgCl p)‖ ^ (Module.finrank ℚ_[p] K).factorial := by
      rw [hj, hamj]
      exact zpow_le_zpow_right₀ hpos.le hjle
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (Nat.factorial_ne_zero _)).1 hle
  · intro ha z hz
    have e : a * z = am * (am⁻¹ * a * z) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, mul_inv_cancel₀ ham0, _root_.one_mul]
    rw [e]
    apply hamD
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv,
      norm_mul, norm_mul, norm_inv]
    have h1 : ‖(am : PadicAlgCl p)‖⁻¹ * ‖(a : PadicAlgCl p)‖ ≤ 1 := by
      rw [inv_mul_le_iff₀ (norm_pos_iff.2 hamn), _root_.mul_one]
      exact ha
    exact mul_le_one₀ h1 (norm_nonneg _) hz

theorem UpperTheory.Gal.W2.trDual_of :
    UpperTheory.Gal.W2.TrDual := by
  intro p _ G w
  exact exists_inverse_different p (G.Fw w)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IntegralMultipleCoprime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def unitBall (p : ℕ) [Fact p.Prime] : Subring (PadicAlgCl p) where
  carrier := {y | ‖y‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (PadicAlgCl.isNonarchimedean p a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by simp

private theorem den_of_norm {p : ℕ} [hp : Fact p.Prime] (q : ℚ) (h : ‖(q : ℚ_[p])‖ ≤ 1) :
    ¬ p ∣ q.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [Nat.Coprime.gcd_eq_one q.reduced] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have hn1 : ‖(q.num : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one _)
      (not_lt.mp fun hlt => hnum (Padic.norm_intCast_lt_one_iff.mp hlt))
  have hd1 : ‖(q.den : ℚ_[p])‖ < 1 := Padic.norm_natCast_lt_one_iff.mpr hd
  have heq : (q : ℚ_[p]) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have hn := congrArg norm heq
  rw [norm_mul, hn1] at hn
  nlinarith [norm_nonneg (q.den : ℚ_[p]), norm_nonneg (q : ℚ_[p])]

private theorem coeff_den {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ τ : F →+* PadicAlgCl p, ‖τ x‖ ≤ 1) (i : ℕ) : ¬ p ∣ ((minpoly ℚ x).coeff i).den := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl p)) with hP
  have hPm : P.Monic := (minpoly.monic hx).map _
  have hroot : ∀ r ∈ P.roots, ‖r‖ ≤ 1 := by
    intro r hr
    have hr' : r ∈ (minpoly ℚ x).rootSet (PadicAlgCl p) := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hx, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.mem_roots hPm.ne_zero).mp hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hr'
    obtain ⟨ψ, rfl⟩ := hr'
    exact h ψ.toRingHom
  have hprod : (P.roots.map fun a => Polynomial.X - Polynomial.C a).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree
  have hlift : P ∈ Polynomial.lifts (unitBall p).subtype := by
    rw [← hprod]
    refine Subsemiring.multiset_prod_mem _ _ ?_
    intro f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hf
    exact ⟨Polynomial.X - Polynomial.C ⟨a, hroot a ha⟩, by simp⟩
  obtain ⟨y, hy⟩ := (Polynomial.lifts_iff_coeff_lifts P).mp hlift i
  have hn : ‖P.coeff i‖ ≤ 1 := by
    rw [← hy]
    exact y.2
  rw [hP, Polynomial.coeff_map] at hn
  apply den_of_norm
  have hc : algebraMap ℚ (PadicAlgCl p) ((minpoly ℚ x).coeff i)
      = algebraMap ℚ_[p] (PadicAlgCl p) (((minpoly ℚ x).coeff i : ℚ) : ℚ_[p]) := by
    simp only [eq_ratCast, map_ratCast]
  rw [hc] at hn
  exact (PadicAlgCl.norm_extends p _).symm.trans_le hn

private theorem integral_multiple_coprime {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (x : F)
    (h : ∀ i, ¬ p ∣ ((minpoly ℚ x).coeff i).den) :
    ∃ (m : ℕ) (c : 𝓞 F), m.Coprime p ∧ (c : F) = m * x := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  set P := minpoly ℚ x with hP
  set M : ℕ := ∏ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).den with hM
  have hMcop : M.Coprime p :=
    Nat.Coprime.prod_left fun i _ =>
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr (h i)).symm
  have hQ : P.scaleRoots (M : ℚ) ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    by_cases hi : i ≤ P.natDegree
    · rcases hi.lt_or_eq with hlt | heq
      · obtain ⟨k, hk⟩ : (P.coeff i).den ∣ M :=
          Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
        have hc : P.coeff i * M = (P.coeff i).num * k := by
          rw [hk]
          push_cast
          rw [← _root_.mul_assoc, Rat.mul_den_eq_num]
        have hpow : (M : ℚ) ^ (P.natDegree - i) = M * M ^ (P.natDegree - i - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        refine ⟨(P.coeff i).num * k * M ^ (P.natDegree - i - 1), ?_⟩
        rw [hpow, ← _root_.mul_assoc, hc]
        simp
      · subst heq
        refine ⟨1, ?_⟩
        rw [Nat.sub_self, pow_zero, _root_.mul_one, map_one]
        exact (minpoly.monic hx).leadingCoeff.symm
    · refine ⟨0, ?_⟩
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
  have hmon : (P.scaleRoots (M : ℚ)).Monic := (Polynomial.monic_scaleRoots_iff _).mpr (minpoly.monic hx)
  obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hQ hmon
  have hint : IsIntegral ℤ ((M : F) * x) := by
    refine ⟨Q, hQm, ?_⟩
    have h0 := Polynomial.scaleRoots_aeval_eq_zero (r := (M : ℚ)) (minpoly.aeval ℚ x)
    have hcast : Int.castRingHom ℚ = algebraMap ℤ ℚ := Subsingleton.elim _ _
    rw [← hP, ← hQmap, hcast, Polynomial.aeval_map_algebraMap, map_natCast] at h0
    rw [← Polynomial.aeval_def]
    exact h0
  exact ⟨M, ⟨(M : F) * x, hint⟩, hMcop, rfl⟩

theorem UpperTheory.Gal.W2.fInt_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FInt := by
  intro hE p _ G x hx
  apply integral_multiple_coprime
  apply coeff_den
  intro τ
  obtain ⟨w, σ, h | h⟩ := hE p G τ
  · rw [h x]
    calc ‖σ (G.emb w x)‖ = ‖G.emb w x‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).1
  · rw [h x]
    calc ‖σ (G.emb w ((IsCMField.complexConj G.F) x))‖
        = ‖G.emb w ((IsCMField.complexConj G.F) x)‖ := (spectralNorm_eq_of_equiv σ _).symm
      _ ≤ 1 := (hx w).2
end
