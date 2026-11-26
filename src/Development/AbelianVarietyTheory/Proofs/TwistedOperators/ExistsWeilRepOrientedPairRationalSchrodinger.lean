module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubledSchrodingerModelTransposedSiegelRul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRepOrientedPairRationalSchrodinger
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRepOrientedPairRationalSchrodinger
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem submatrix_mul_id {R : Type} [CommRing R] {m n p k : ℕ} (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin p) R)
    (e : Fin k → Fin m) : (M * N).submatrix e id = M.submatrix e id * N := by
  ext i j
  simp [Matrix.mul_apply]

theorem actE_eq_of_conj_related {R : Type} [CommRing R] {n m k : ℕ} (e : Fin k ≃ Fin m) (P : Matrix (Fin n) (Fin n) R)
    (x : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin m) (Fin m) R) (G H : Matrix (Fin n) (Fin n) R)
    (M₁ : Matrix (Fin k) (Fin k) R) (Lx : Matrix (Fin k) (Fin n) R) (M₂ : Matrix (Fin n) (Fin n) R)
    (hLx : Lx = xᵀ.submatrix e id * G) (h₁ : M₁ = Qᵀ.submatrix e e) (h₂ : M₂ = H) (hu : Pᵀ * G = G * H) :
    ((P * x * Q)ᵀ.submatrix e id) * G = M₁ * Lx * M₂ := by
  subst hLx h₁ h₂
  rw [Matrix.transpose_mul, Matrix.transpose_mul, submatrix_mul_id, ← Matrix.mul_assoc (Qᵀ.submatrix e e),
    Matrix.submatrix_mul_equiv, submatrix_mul_id]
  simp only [Matrix.mul_assoc]
  rw [hu]

theorem unit_aux {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (P P' K G : Matrix (Fin n) (Fin n) R)
    (hPP : P * P' = 1) (hK : Kᵀ = -G) (h : (P.map c)ᵀ * K * P = K) : Pᵀ * G = G * P'.map c := by
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, hK,
    Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h'
  have hc : P.map c * P'.map c = 1 := by
    rw [← Matrix.map_mul, hPP]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  calc Pᵀ * G = Pᵀ * G * (P.map c * P'.map c) := by rw [hc, Matrix.mul_one]
    _ = (Pᵀ * G * P.map c) * P'.map c := by simp only [Matrix.mul_assoc]
    _ = G * P'.map c := by rw [h']

theorem eq_submatrix_symm {α : Type} {a b : ℕ} (f : Fin a ≃ Fin b) (M : Matrix (Fin b) (Fin b) α)
    (N : Matrix (Fin a) (Fin a) α) (h : M.submatrix f f = N) : M = N.submatrix f.symm f.symm := by
  subst h
  ext i j
  simp

theorem incM_neg_refl {D : D7} {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (-(G.submatrix (Equiv.refl (Fin n)) (Equiv.refl (Fin n)))) = -(G.map (incA D)) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, Matrix.neg_apply, Matrix.submatrix_apply,
    Equiv.refl_apply, map_neg]

theorem neg_incM_eq {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : IsUnit J.det) {ξ : D.host.E} (hξ : ξ ≠ 0) :
    (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (ξ • (-ξ • J⁻¹)⁻¹) := by
  have e1 : (-ξ • J⁻¹)⁻¹ = (-ξ)⁻¹ • J := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ, inv_mul_cancel₀ (neg_ne_zero.2 hξ), one_smul]
  have e2 : ξ • (-ξ)⁻¹ • J = -J := by
    rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ, neg_one_smul]
  rw [e1, e2]
  funext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]

theorem eq_map_conj {D : D7} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) (AE D)) (h : Q = P.map (cA D)) : P = Q.map (cA D) := by
  subst h
  ext i j
  simp [Formalism.L2.Theta.cA_cA]

theorem eq_inv_transpose {R : Type} [CommRing R] {n : ℕ} (P P' B B' : Matrix (Fin n) (Fin n) R) (hP : P' * P = 1)
    (hB : B * B' = 1) (h : B = P'ᵀ) : P = B'ᵀ := by
  have h1 : Pᵀ * B = 1 := by rw [h, ← Matrix.transpose_mul, hP, Matrix.transpose_one]
  have h2 : B' = Pᵀ := by
    calc B' = (Pᵀ * B) * B' := by rw [h1, Matrix.one_mul]
      _ = Pᵀ := by rw [Matrix.mul_assoc, hB, Matrix.mul_one]
  rw [h2, Matrix.transpose_transpose]

theorem sgn_gram_eq {D : D7} (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε
  · show S.gram = _
    simp
  · show (neg S).gram = _
    rw [neg_gram]
    simp

theorem gram_neg_sgn {D : D7} (ε : Bool) (S : HSp D) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (hJ : J = (if ε then 1 else -1 : D.host.E) • S.gram) : J = -(sgn ε S).gram := by
  rw [sgn_gram_eq, hJ]
  cases ε <;> simp

theorem gram_hspOf_transpose {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E)
    (h1 : (GlobalTheory.WeilSchrodinger.sesq D Jᵀ).IsSymm) h2 L hL h3 (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (GlobalTheory.WeilSchrodinger.hspOf D Jᵀ h1 h2 L hL h3 sg).gramᵀ = J := by
  rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
  exact Matrix.transpose_transpose J


set_option maxHeartbeats 1600000 in
theorem exists_weil_of_oriented : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ (χ χ' : (AE D)ˣ →* Circle) (ω : WRep S X), IsWeil ψ ε S X χ χ' ω →
    ∃ om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vs Ws, M.IsWeil Bs.ψ χ χ' om ∧
      ∀ Φ f, IsDatum M ψ cS Φ f → ∀ g h,
        IsDatum M ψ cS (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g, kapX X e hJW h) Φ) (ω (g, h) f) := by
  intro D ψ θ _hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW _hcart M hM cS hcS χ χ' ω hω
  subst hψ
  have hω' : IsWeilDatumO Bs.ψ (sgn ε S) X χ χ' (ω.toSgn ε) := hω
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D Bs hBs S.rank Vs r s hV
  obtain ⟨hJd, L0, hL0, h4, h5, h6⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D Bs hBs d Ws r' s' hW
  let Th := GlobalTheory.WeilSchrodinger.hspOf D Vs.Jᵀ h1 h2 Vs.L hV.lat.toIsLattice h3 (fun _ => (r, s))
  let Sh := GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Ws.J⁻¹) h4 h5 L0 hL0 h6 (fun _ => (s', r'))
  have hTt : Th.gramᵀ = Vs.J := gram_hspOf_transpose _ _ _ _ _ _ _
  have hSg : Sh.gram = -D.host.xi0 • Ws.J⁻¹ := GlobalTheory.WeilSchrodinger.gram_hspOf _ _ _ _ _ _ _
  have hdX : X.rank = d := Fin.equiv_iff_eq.mp ⟨e⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

  have hT' : Th.gramᵀ = -((sgn ε S).gram.submatrix (Equiv.refl (Fin S.rank)) (Equiv.refl (Fin S.rank))) := by
    rw [hTt, Equiv.coe_refl, Matrix.submatrix_id_id]
    exact gram_neg_sgn ε S hJ
  have hS' : Sh.gram⁻¹ = -(X.gramᵀ.submatrix e.symm e.symm) := by
    refine Matrix.inv_eq_left_inv ?_
    have hK : D.host.xi0 • X.gramᵀ.submatrix e.symm e.symm = Ws.J := by rw [hJW]; rfl
    have key : (-(X.gramᵀ.submatrix e.symm e.symm)) * (-D.host.xi0 • Ws.J⁻¹) = 1 := by
      rw [neg_mul, Matrix.mul_smul, neg_smul, neg_neg, ← Matrix.smul_mul, hK]
      exact Matrix.mul_nonsing_inv _ hJd
    rw [hSg]
    exact key

  obtain ⟨φ', hφ'c, hφ'Q, hφ'm, hφ'S, hφ'd⟩ := GlobalTheory.T.exists_unitary_equiv_conj_of_gram_transpose_eq_neg D (sgn ε S) Th (Equiv.refl _) hT'
  obtain ⟨φ, hφc, hφQ, hφm, hφS, hφd⟩ := GlobalTheory.T.exists_unitary_equiv_inv_transpose_of_gram_inv D X Sh e.symm hS'
  obtain ⟨L, hL1, -, hLc, hLc', hLQ, hLi, hLf⟩ := GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic D (sgn ε S) X Sh Th (Equiv.refl _) e.symm
  have hsy := GlobalTheory.T.symplectic_hom_transpose_gram_darboux D (sgn ε S) X Sh Th (Equiv.refl _) e.symm hT' hS'
  have hLx : ∀ u : Matrix (Fin S.rank) (Fin d) (AE D), L u = (HMul.hMul (uᵀ.submatrix e id) ((sgn ε S).gram.map (incA D)) :
      Matrix (Fin X.rank) (Fin S.rank) (AE D)) := fun u => (hL1 u).trans rfl
  have hcL : ∀ u, cS u = L u := fun u => by
    rw [hcS, hLx, sgn_gram_eq]
    rfl

  have hact : ∀ (g : GA D Sh) (h : GA D Th) (x : WO Sh Th), L (actO Sh Th g h x) = actO (sgn ε S) X (φ' h) (φ g) (L x) := by
    intro g h x
    have hg : Formalism.L2.Theta.mt X (φ g) = ((Formalism.L2.Theta.mt Sh g⁻¹)ᵀ).submatrix e e :=
      eq_submatrix_symm e.symm _ _ (hφm g)
    have hh : Formalism.L2.Theta.mt (sgn ε S) (φ' h)⁻¹ = (Formalism.L2.Theta.mt Th h⁻¹).map (cA D) := by
      rw [← map_inv]
      exact hφ'm h⁻¹
    have hTinc : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gram)ᵀ = -((sgn ε S).gram.map (incA D)) := by
      have e0 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gram)ᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Th.gramᵀ := rfl
      rw [e0, hT']
      exact incM_neg_refl _
    have hPP : Formalism.L2.Theta.mt Th h * Formalism.L2.Theta.mt Th h⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]
    have hu := unit_aux (cA D) _ _ _ _ hPP hTinc (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram Th h)
    exact (hLx _).trans (actE_eq_of_conj_related e _ x _ _ _ _ _ _ (hLx x) hg hh hu)

  obtain ⟨ω', hω'', hrel⟩ := GlobalTheory.T.isWeilDatum_comp_group_swapping_symplectic_equiv D Bs.ψ (sgn ε S) X Sh Th hdX.symm rfl L φ.toMonoidHom φ'.toMonoidHom hLc hLc' hLQ
    (fun x y => by rw [hL1, hL1]; exact hsy x y) hLi hLf hφc hφ'c hφQ hφ'Q hact hφS hφ'S hφd hφ'd χ χ' (ω.toSgn ε) hω'
  have hA : Vs.J = Th.gramᵀ := hTt.symm
  have hB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • Sh.gram⁻¹) := by
    rw [hSg]
    exact neg_incM_eq Ws.J hJd hξ
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω''
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h6 := GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have h7 := GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D Bs.ψ hω'.std Sh Th χ' χ hω''.hecS hω''.hecT hω''.resS hω''.resT Vs.J Ws.J (-1) hA hB
    (Fin S.rank × Fin d) M.co hM.rat ω' hω'' om hom
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) Bs.ψ M.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hW : M.IsWeil Bs.ψ χ χ' om :=
    ⟨⟨GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp, h6⟩, ⟨GlobalTheory.WeilSchrodinger.transD _ M.co, GlobalTheory.WeilSchrodinger.transD_e M.co,
      GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp, h7⟩, h5⟩
  refine ⟨om, hW, ?_⟩

  intro Φ f hΦ g h
  have hm : Formalism.L2.Theta.mt (sgn ε S) ((ofSgn ε S).symm g) = Formalism.L2.Theta.mt S g := by
    rw [← mt_ofSgn, MulEquiv.apply_symm_apply]
  have h0 := hφ'm (φ'.symm ((ofSgn ε S).symm g))
  rw [MulEquiv.apply_symm_apply] at h0
  have ha : Formalism.L2.Theta.mt Th (φ'.symm ((ofSgn ε S).symm g)) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g).1.1 :=
    eq_map_conj _ _ (hm.symm.trans h0)
  have h1 := hφm (φ.symm h)
  rw [MulEquiv.apply_symm_apply] at h1
  have hP : Formalism.L2.Theta.mt Sh (φ.symm h)⁻¹ * Formalism.L2.Theta.mt Sh (φ.symm h) = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]
  have hb : Formalism.L2.Theta.mt Sh (φ.symm h) = ((kapX X e hJW h)⁻¹).1.1ᵀ :=
    eq_inv_transpose _ _ _ _ hP (Units.mul_inv (kapX X e hJW h).1) h1
  obtain ⟨hs, ht⟩ := hom (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g) (kapX X e hJW h) (φ.symm h) (φ'.symm ((ofSgn ε S).symm g))
    ha hb Φ hΦ.1
  refine ⟨hs, fun u => ?_⟩
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F M.co Bs.ψ Φ = fun u => f (L u) := funext fun u => by
    rw [← hcL]
    exact hΦ.2 u
  have k1 := congrFun ht u
  have k2 := congrArg (fun F => ω' (φ.symm h, φ'.symm ((ofSgn ε S).symm g)) F u) hΦf
  have k3 := congrFun (hrel (φ.symm h) (φ'.symm ((ofSgn ε S).symm g)) f) u
  rw [hcL]
  refine k1.trans (k2.trans (k3.trans ?_))
  simp [WRep.toSgn]

end GlobalTheory.SquareAgree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRepOrientedPairRationalSchrodingerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRep_orientedPair_rationalSchrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ (χ χ' : (AE D)ˣ →* Circle) (ω : WRep S X), IsWeil ψ ε S X χ χ' ω →
    ∃ om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Vs Ws, M.IsWeil Bs.ψ χ χ' om ∧
      ∀ Φ f, IsDatum M ψ cS Φ f → ∀ g h,
        IsDatum M ψ cS (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S _ hJ g, kapX X e hJW h) Φ) (ω (g, h) f) := by
  first | exact @GlobalTheory.SquareAgree.exists_weil_of_oriented | exact GlobalTheory.SquareAgree.exists_weil_of_oriented | (intros; apply GlobalTheory.SquareAgree.exists_weil_of_oriented <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdealMembershipCriterion
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdealMembershipCriterion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharComb

variable {D : D7}

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  exact Prod.ext (zero_mul _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem complId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : AE D} (hx : x ∈ complId 𝔞)
    (hy : y ∈ complId 𝔟) : x * y ∈ complId (𝔞 * 𝔟) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, b, hb, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]
      exact tmul_mem_complId (intAf_mul hα hβ) (FractionalIdeal.mul_mem_mul ha hb)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem infPart_of_mem {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    infPart D x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, a, -, rfl⟩ := hx
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] a = 0
    exact TensorProduct.zero_tmul _ _
  | zero => exact map_zero _
  | add x z _ _ hx hz => rw [RingHom.map_add (f := _), hx, hz, add_zero]
  | neg x _ hx => rw [RingHom.map_neg, hx, neg_zero]

def finId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (EAf D) :=
  (complId 𝔠).map (toEAf D).toAddMonoidHom

theorem finId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : EAf D} (hx : x ∈ finId 𝔞)
    (hy : y ∈ finId 𝔟) : x * y ∈ finId (𝔞 * 𝔟) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  exact ⟨x₀ * y₀, complId_mul hx₀ hy₀, map_mul (toEAf D) x₀ y₀⟩

theorem tmul_one_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {a : D.host.E} (ha : a ∈ 𝔠) :
    a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ finId 𝔠 :=
  ⟨_, tmul_mem_complId one_mem_intAf ha, rfl⟩

theorem int_mem_finId_one {z : EAf D} (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    z ∈ finId (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  induction hz using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨b, hb⟩ := b
      exact tmul_one_mem_finId ((FractionalIdeal.mem_one_iff _).2 hb)
    · exact ⟨_, tmul_mem_complId y.2 (FractionalIdeal.one_mem_one _), rfl⟩
  | zero => exact zero_mem _
  | one => exact tmul_one_mem_finId (FractionalIdeal.one_mem_one _)
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy => simpa using finId_mul hx hy

theorem idS_mem_finId (𝔪 : Ideal (𝓞 D.host.E)) {t : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) ∈ finId ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe]
    exact tmul_one_mem_finId ((FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => rw [Subring.coe_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul]
    simpa using finId_mul (int_mem_finId_one c.2) hx

theorem idem_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {e : AE D} {Q : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e Q) {a : D.host.E} (ha : a ∈ 𝔠)
    (hv : Valued.v (algebraMap D.host.E (Kw Q) a) = 1) : toEAf D e ∈ finId 𝔠 := by
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨h1, h2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt he
  have hu : toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (GlobalTheory.StdFrames.mem_OA_iff _).2 fun Q' => ?_
    rw [map_mul, GlobalTheory.FunObj.Comparison₂.cpt_tmul]
    by_cases hQ : Q' = Q
    · subst hQ
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q' hQ, zero_mul]
      exact zero_mem _
  have e1 : toEAf D e = (toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F))) *
      (a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ha0, one_mul,
      Algebra.TensorProduct.one_def.symm, mul_one]
  rw [e1]
  simpa using finId_mul (int_mem_finId_one hu) (tmul_one_mem_finId ha)

theorem toEAf_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    toEAf D x ∈ finId 𝔠 := ⟨x, hx, rfl⟩

theorem ring_key {R : Type*} [CommRing R] (e c : R) : c = e * (e * c) + ((1 + e) * (1 - e)) * c := by ring

theorem mem_complId_of_finId {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c : AE D} (hc : c ∈ complId 𝔞)
    (h : toEAf D c ∈ finId 𝔟) : c ∈ complId 𝔟 := by
  obtain ⟨z, hz, hze⟩ := h
  have hze' : toEAf D z = toEAf D c := hze
  have hzc : z = c := GlobalTheory.DepthFix.ext_cpt (by rw [infPart_of_mem hz, infPart_of_mem hc])
    fun Q => by rw [hze']
  exact hzc ▸ hz

theorem core {𝔞 𝔟 𝔪 𝔡 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hid : 𝔪 * 𝔡 = 𝔞 * 𝔟) {e c : EAf D}
    (he : e ∈ finId 𝔞) (hec : e * c ∈ finId 𝔟) (hm : (1 + e) * (1 - e) ∈ finId 𝔪) (hc : c ∈ finId 𝔡) :
    c ∈ finId (𝔞 * 𝔟) := by
  have h3 := finId_mul hm hc
  rw [hid] at h3
  have h4 := add_mem (finId_mul he hec) h3
  rwa [← ring_key e c] at h4

theorem ideal_key {M A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hM : M ≠ 0) :
    M * (A * (B * M⁻¹)) = A * B := by
  calc _ = A * B * (M * M⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hM, mul_one]

theorem mem_complId_AA_AAbar : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 →
    ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) →
    (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  classical
  intro D hq T L μ0 hL sc G c hc hec
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h1 := hec e he
  obtain ⟨-, heO, t, ht, hte⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0
    (fun Q => G.pl.depth sc (Q.under (𝓞 D.host.F))) he
  have hprod : (∏ Q ∈ G.pl.W0, Q.asIdeal ^ G.pl.depth sc (Q.under (𝓞 D.host.F))) = G.pl.modul sc := by
    unfold Places.W0 Places.modul
    rw [Finset.prod_image fun v hv v' hv' h =>
      (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
    exact Finset.prod_congr rfl fun v hv => by rw [G.pl.under_w hv]
  rw [hprod] at ht

  have heA : toEAf D e ∈ finId D.host.AA := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := id he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show toEAf D (∑ Q ∈ G.pl.W0, es Q) = ∑ Q ∈ G.pl.W0, toEAf D (es Q) from
      map_sum (toEAf D).toAddMonoidHom (fun Q => es Q) G.pl.W0]
    refine sum_mem fun Q hQ => ?_
    obtain ⟨a, ha, hv⟩ := GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hq hL G Q hQ
    exact idem_mem_finId (hes Q hQ) ha hv

  have ht2 : ((⟨1 + toEAf D e, add_mem (one_mem _) heO⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * t) ∈
      Formalism.L2.DIV.idS D.host.F (G.pl.modul sc) := Ideal.mul_mem_left _ _ ht
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hid : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
      (D.host.AA * G.pl.stAbar sc) = D.host.AA * D.host.AAbar := ideal_key hM
  have hm := idS_mem_finId _ ht2
  rw [Subring.coe_mul, hte] at hm
  have h1f := toEAf_mem_finId h1
  rw [RingHom.map_mul] at h1f
  exact mem_complId_of_finId hc (core hid heA h1f hm (toEAf_mem_finId hc))

end GlobalTheory.XCharComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryIdealMembershipCriterionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementary_ideal_membership_criterion : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) → (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.XCharComb.mem_complId_AA_AAbar | exact GlobalTheory.XCharComb.mem_complId_AA_AAbar | (intros; apply GlobalTheory.XCharComb.mem_complId_AA_AAbar <;> assumption)
end
end
