module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsUnitaryAutomorphicFormOfWeightVectorValued
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsSphericalHeckeRepSplitLabelOfOffLevelPlace
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.sum_eq_of_dual_sums {G ι κ : Type} {M : Type} [AddCommGroup M] [Module ℂ M] (R : Finset ι) (B : Finset κ)
    (u : ι → G) (v : κ → G) (Fm : G → M)
    (h : ∀ ℓ : Module.Dual ℂ M, ∑ a ∈ B, ℓ (Fm (v a)) = ∑ γ ∈ R, ℓ (Fm (u γ))) :
    ∑ γ ∈ R, Fm (u γ) = ∑ a ∈ B, Fm (v a) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, map_sum, sub_eq_zero]
  exact (h ℓ).symm

private theorem UpperTheory.dual_invariant_of_trivial_character {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℂ M] (J : Subgroup G) (χ : J →* ℂˣ)
    (Fm : G → M) (hF : ∀ (κ : J) g, Fm (g * κ) = ((χ κ : ℂˣ) : ℂ) • Fm g) (ℓ : Module.Dual ℂ M) (g : G) (k : J)
    (hk : χ k = 1) : ℓ (Fm (g * k)) = ℓ (Fm g) := by
  rw [hF, hk, Units.val_one, one_smul]

private theorem UpperTheory.hecke_single_eq_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (F : Bridge.Gf V → ℂ) (g : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) := by
  have e1 : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      (1 : ℂ) • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index
      (h := fun d (z : ℂ) => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans (one_smul ℂ _)

private theorem UpperTheory.level_character_trivial {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∀ y : (levEnv V β L).J, GlobalTheory.Hk3.IsLocElt V P y → (levEnv V β L).χ y = 1 := by
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 P e f' he h1 hoff
  rintro ⟨y, hy⟩ ⟨e, f', a, he, ha, hxa, hs⟩
  obtain rfl : y = (Formalism.L2.Theta.finHom V).rangeRestrict a := Subtype.ext hxa
  exact Units.ext ((hl e f' he).2.1 a ⟨ha, hy⟩ hs)

private theorem UpperTheory.hecke_offprime_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)) (hd : d.Pairwise (fun a b => b ≤ a))
    (hx : GlobalTheory.Hk3.IsLabElt V P d x) (hB : ∀ a ∈ B, GlobalTheory.Hk3.IsLocElt V P a) (hDC : Bridge.IsDC (levEnv V β L).J x B) :
    ∃ R : Finset (Formalism.L2.Theta.GA D V),
      GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl P) (Formalism.IndefR.Mult.dualLab d) R ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf V → M),
        (∀ (κ : (levEnv V β L).J) g, Fm (g * κ) = (((levEnv V β L).χ κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
        ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) = ∑ a ∈ B, Fm (g * a) := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hχ := UpperTheory.level_character_trivial V β Λ L hc' P h1 hoff
  have H := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' P h1 hoff d x B hd hx hB hDC
  have hs : GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P)) d (GlobalTheory.Hk3.rep V P d) := by
    rw [GlobalTheory.SphConj.conjPl_conjPl]
    exact GlobalTheory.SphLabelOps.sphOp_rep H.1
  refine ⟨GlobalTheory.Hk3.rep V P d, GlobalTheory.SphConj.sphOp_conj V _ d _ hs, fun M _ _ Fm hF g => ?_⟩
  refine UpperTheory.sum_eq_of_dual_sums _ _ (fun γ => g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) (fun a => g * a) Fm fun ℓ => ?_
  have h2 := H.2 ℂ (fun h => ℓ (Fm h)) (fun h k hk => UpperTheory.dual_invariant_of_trivial_character _ _ Fm hF ℓ h k (hχ k hk))
  exact (congrFun h2 g).trans (UpperTheory.hecke_single_eq_sum V P d (fun h => ℓ (Fm h)) g)

theorem UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) (k : ℕ), 1 ≤ k → k ≤ (Vc D j).rank →
        (∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a) ∧
        ∃ R : Finset (Formalism.L2.Theta.GA D (Vc D j)),
          GlobalTheory.Hk3.SphOp (Vc D j) (labOf p j t Q) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab (Vc D j).rank k)) R ∧
          ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf (Vc D j) → M),
            (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
            ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict γ) = ∑ a ∈ hkA p j t (Q, k), Fm (g * a) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t Q k hpos hk
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2
  have hs := fun x => GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones (Vc D j) p.R.pl _ ((Q, k) : _ × ℕ) x
  have hloc : ∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a :=
    fun a ha => (hs a).2.1 ((p.R.B.L j t).hecke.hA_loc (Q, k) ⟨hpos, hk⟩ a ha)
  exact ⟨hloc, UpperTheory.hecke_offprime_sum (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) (plOf p j t Q) hg
    _ ((p.R.B.L j t).hecke.hx (Q, k)) (hkA p j t (Q, k)) (hs 1).2.2
    ((hs _).1 hk ((p.R.B.L j t).hecke.hx_ok (Q, k) ⟨hpos, hk⟩)) hloc ((p.R.B.L j t).hecke.hDC (Q, k) ⟨hpos, hk⟩)⟩
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.VectorValuedAutFormEquivariantInfiniteComponent
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.infinite_matrix_rational {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (h : GA D V) (γ₀ : GL (Fin V.rank) D.host.E)
    (e : matHom V h = Matrix.GeneralLinearGroup.map (incA D) γ₀) (τ : D.what₂.Tau) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) h =
      (Matrix.GeneralLinearGroup.map (tauE D τ) γ₀ : GL (Fin V.rank) ℂ).val := by
  have e' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat _ D.sp.cm.sig V.gram h = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [e']
  ext a b
  change θ τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] γ₀.val a b)) = tauE D τ (γ₀.val a b)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ τ).1 _

private theorem UpperTheory.exists_conjugate_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (σ ε : E →+* ℂ)
    (hε : ε = σ ∨ ε = ComplexEmbedding.conjugate σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ B : GL (Fin n) ℂ, ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val = A * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * A⁻¹ →
      Matrix.GeneralLinearGroup.map ε γ₀ = B * cEmb ε x * B⁻¹ := by
  obtain ⟨B, rfl⟩ := hA
  have key : ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val =
        B.val * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * (B.val)⁻¹ →
      Matrix.GeneralLinearGroup.map σ γ₀ = B * cEmb σ x * B⁻¹ := fun x γ₀ h => by
    apply Units.ext
    rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  rcases hε with rfl | rfl
  · exact ⟨B, key⟩
  · refine ⟨Matrix.GeneralLinearGroup.map (starRingEnd ℂ) B, fun x γ₀ h => ?_⟩
    have h1 := congrArg (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) (key x γ₀ h)
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (cEmb σ x) = cEmb (ComplexEmbedding.conjugate σ) x := by
      ext a b
      exact (GlobalTheory.DefiniteBC.coord_conjugate σ _).symm
    rw [h2] at h1
    rw [← h1]
    ext a b
    rfl

private theorem UpperTheory.weight_operator_conjugate {n : ℕ} {ι : Type} [Fintype ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (B C G : ι → GL (Fin n) ℂ) (h : G = B * C * B⁻¹) (u : NablaT ℂ n mu) :
    wtOp ℂ n mu sh B⁻¹ (wtOp ℂ n mu sh G u) = wtOp ℂ n mu sh C (wtOp ℂ n mu sh B⁻¹ u) := by
  classical
  rw [h, ← Module.End.mul_apply, ← wtOp_mul, ← mul_assoc, inv_mul_cancel_left, wtOp_mul]
  rfl

private theorem UpperTheory.monoidHom_kernel_invariance {G H K : Type} [Monoid G] [Monoid H] [Monoid K] (j : G →* H) (φ : H →* K)
    (g x : G) (h : H) (hx : φ (j x) = 1) : φ (j (g * x) * h) = φ (j g * h) := by
  simp only [map_mul, hx, mul_one]

theorem UpperTheory.vectorValued_autForm_equivariant_infinite_component :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
        (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsInfFam θ → GlobalTheory.DefTransfer.IsTransfer V θ j h₀ →
        ∀ (emb : D.what₂.Tau → (D.host.E →+* ℂ)), (∀ τ, emb τ = tauE D τ ∨ emb τ = ComplexEmbedding.conjugate (tauE D τ)) →
        ∀ (mu : D.what₂.Tau → ℕ → ℕ) (sh : D.what₂.Tau → ℤ) (Fm : Bridge.Gf V → NablaT ℂ V.rank mu), Fm ≠ 0 →
        (∀ (γ : GQ V) (γ₀ : GL (Fin V.rank) D.host.E), matHom V γ = Matrix.GeneralLinearGroup.map (incA D) γ₀ → ∀ g,
          Fm (Bridge.ratF V γ * g) = wtOp ℂ V.rank mu sh (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) (Fm g)) →
        (∀ᶠ κ in nhds (1 : GA D V), ∀ g, Fm (g * (finHom V).rangeRestrict κ) = Fm g) →
        ∃ F1 : UA D.host.E V.rank → NablaT ℂ V.rank mu, F1 ≠ 0 ∧
          (∀ γ ∈ ratU D.host.E V.rank, ∀ g, F1 (γ * g) = wtOp ℂ V.rank mu sh (fun τ => cEmb (emb τ) γ) (F1 g)) ∧
          (∀ x ∈ infU D.host.E V.rank, ∀ g, F1 (g * x) = F1 g) ∧ (∀ᶠ y in nhds (1 : UA D.host.E V.rank), ∀ g, F1 (g * y) = F1 g) ∧
          ∃ A : Module.End ℂ (NablaT ℂ V.rank mu), ∀ x, F1 x = A (Fm ((finHom V).rangeRestrict (j x * h₀))) := by
  intro D _ V θ j h₀ hθ hT emb hemb mu sh Fm hF hrat hlev
  classical
  obtain ⟨-, hQ, -, hI, ⟨A, hA, hAe⟩, -⟩ := hT
  choose B hB using fun τ => UpperTheory.exists_conjugate_embedding (tauE D τ) (emb τ) (hemb τ) (A τ) (hA τ)
  refine ⟨fun x => wtOp ℂ V.rank mu sh B⁻¹ (Fm ((finHom V).rangeRestrict (j x * h₀))), ?_, ?_, ?_, ?_, _, fun _ => rfl⟩
  · intro h0
    apply hF
    funext g
    obtain ⟨k, rfl⟩ := (finHom V).rangeRestrict_surjective g
    have h1 := congrArg (wtOp ℂ V.rank mu sh B) (congrFun h0 (j.symm (k * h₀⁻¹)))
    simp only [ContinuousMulEquiv.apply_symm_apply, inv_mul_cancel_right, Pi.zero_apply, map_zero] at h1
    rw [← Module.End.mul_apply, ← wtOp_mul, mul_inv_cancel, wtOp_one] at h1
    exact h1
  · intro γ hγ g
    have hj : j γ ∈ GQ V := (hQ γ).1 hγ
    obtain ⟨γ₀, -, e⟩ := id hj
    have e' : matHom V (j γ) = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e.symm
    have h1 := hrat ⟨j γ, hj⟩ γ₀ e' ((finHom V).rangeRestrict (j g * h₀))
    have h2 : (finHom V).rangeRestrict (j (γ * g) * h₀) =
        Bridge.ratF V ⟨j γ, hj⟩ * (finHom V).rangeRestrict (j g * h₀) := by
      have h4 : j (γ * g) * h₀ = j γ * (j g * h₀) := by rw [map_mul, mul_assoc]
      exact (congrArg (finHom V).rangeRestrict h4).trans (map_mul (finHom V).rangeRestrict _ _)
    have h3 : (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) = B * (fun τ => cEmb (emb τ) γ) * B⁻¹ := by
      funext τ
      exact hB τ γ γ₀ ((UpperTheory.infinite_matrix_rational θ hθ _ γ₀ e' τ).symm.trans (hAe τ γ))
    exact (congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm h2).trans h1)).trans
      (UpperTheory.weight_operator_conjugate mu sh B _ _ h3 _)
  · intro x hx g
    have hj : finHom V (j x) = 1 := (hI x).1 hx
    have h1 : (finHom V).rangeRestrict (j x) = 1 := Subtype.ext hj
    exact congrArg (fun z => wtOp ℂ V.rank mu sh B⁻¹ (Fm z))
      (UpperTheory.monoidHom_kernel_invariance j.toMulEquiv.toMonoidHom (finHom V).rangeRestrict g x h₀ h1)
  · have hc : Continuous fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀ :=
      (continuous_const.mul j.continuous).mul continuous_const
    have ht : Filter.Tendsto (fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀) (nhds 1) (nhds 1) := by
      exact hc.tendsto' 1 1 (by simp only [map_one, mul_one, inv_mul_cancel])
    filter_upwards [ht.eventually hlev] with y hy g
    have h1 : j (g * y) * h₀ = j g * h₀ * (h₀⁻¹ * j y * h₀) := by
      rw [map_mul]
      group
    exact congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm ((congrArg (finHom V).rangeRestrict h1).trans
      (map_mul (finHom V).rangeRestrict _ _))).trans (hy _))
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.GoodPlaceOfTwistPlaceDividing
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.good_place_of_twist_place_dividing :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W →
        ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ v : HeightOneSpectrum (𝓞 D.host.E),
          ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → GlobalTheory.Hk3.Good p.R.toRealDat (p.R.mu w) v := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j P W hD w hw hW v hv
  have hL := p.charW.base.lev
  have hl := Formalism.EigenvalueLevelCeiling.plc_prime w
  have key : ∀ q : ℕ, q.Prime → q ≠ Formalism.EigenvalueLevelCeiling.plc w → ((q : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    intro q hq hne hqv
    have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hl).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hqv) (v.asIdeal.mul_mem_left b hv)))
  have hsp : Formalism.EigenvalueLevelCeiling.plc w ∉ Formalism.MainNotions.JumpSetsAlt.excSet D := hD.special ▸ hW.2.2.2
  have hunr : (p.R.xiH (p.R.mu w)).UnrAt v := by
    obtain ⟨ψ, Q, hψ, e⟩ := p.charW.tup.mu_on w hw
    have e' : p.R.xiH (p.R.mu w) = p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have hd : (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt v := by
      unfold Formalism.L2.Host.CharFrame.delAt
      split_ifs
      · refine p.R.C.isDel'.unr v (key _ D.host.pde'_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
      · refine p.R.C.isDel.unr v (key _ D.host.pde_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
    intro x hx
    have a1 := hd x hx
    have a2 := hψ.atl v hv x
    rw [e']
    change (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc v x * ψ.loc v x = 1
    rw [a1, a2, mul_one]
  intro PP hPP
  rcases hPP with hPP | hPP
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have h1 := p.R.C.P.pb_over k
      have hk' : PP.under (𝓞 D.host.K) = p.R.C.P.pb k := hk
      rw [← hk'] at h1
      have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
      rwa [map_natCast] at h2
    have hn : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
      refine key _ (D.host.g_prime k) fun h => ?_
      have h1 := hD.big k
      have h2 := hW.2.1
      rw [h] at h1
      exact absurd h1 (not_lt.2 h2)
    refine ⟨fun e => hn (e ▸ hg), fun hc => hn ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hg
    have : c' = ((D.host.g k : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      have e1 : (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) = ((D.host.g k : ℕ) : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _
      have h3 : (c' : D.host.E) = star (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) := h2
      rw [e1, star_natCast, ← e1] at h3
      exact h3
    exact this ▸ h1
  · exact ⟨fun e => (hL.Q_ram (p.R.mu w) v).2 (Or.inl (e ▸ hPP)) hunr,
      fun hc => (hL.Q_ram (p.R.mu w) v).2 (Or.inr ⟨PP, hPP, hc⟩) hunr⟩
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsNonzeroVectorValuedEigenformUnitary
section -- merged from Development.AutomorphicArithmetic.DivisorFrames.EvalLocalElementMatrixEqOneOfPrimeNotDvd
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem norm_int_le_one {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (j : E →+* PadicAlgCl l) (x : 𝓞 E) :
    ‖j (x : E)‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (j (x : E)) := x.isIntegral_coe.map j.toIntAlgHom
  have h2 : IsIntegral (PadicAlgCl.valued l).v.integer (j (x : E)) := h1.tower_top
  have h3 := (Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral h2
  rw [Valuation.mem_integer_iff, PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

private theorem norm_le_of_int {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (z) (hz : z ∈ intAE D) : ‖ev z‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    have e : a ⊗ₜ[D.host.F] (x : D.host.E) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (x : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, norm_mul]
    have h2 := norm_int_le_one (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) x
    exact mul_le_one₀ (h a ha) (norm_nonneg _) h2
  | zero => rw [RingHom.map_zero, norm_zero]; exact zero_le_one
  | add x y _ _ hx hy =>
    rw [RingHom.map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rw [RingHom.map_neg, norm_neg]; exact hx

private theorem ev_idem {D : D7} {l : ℕ} [Fact l.Prime]
    (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l)
    (h : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) →
      ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (e : AE D) (he : e * e = e)
    (hx : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) :
    ev (finPart D e) = 0 := by
  have hl : l.Prime := Fact.out
  have hcO : ((l : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have h1 := (hx _ hcO).not.1 hP
  rw [not_not] at h1
  have h2 := norm_le_of_int ev h _ h1
  by_contra hne
  have h3 : ev (finPart D e) * ev (finPart D e) = ev (finPart D e) := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, he]
  have h4 : ev (finPart D e) = 1 := mul_left_cancel₀ hne (h3.trans (mul_one _).symm)
  rw [RingHom.map_mul, RingHom.map_mul, h4, one_mul] at h2
  have h5 : ev (finPart D (incA D ((((l : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹))) = ((l : ℕ) : PadicAlgCl l)⁻¹ := by
    change (ev.comp ((finPart D).comp (incA D))) _ = _
    rw [map_inv₀]
    congr 1
    simp only [map_natCast]
  rw [h5, norm_inv] at h2
  have h6 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have h7 : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  exact absurd h2 (not_le.2 ((one_lt_inv₀ h7).2 h6))

private theorem finPart_cA {D : D7} (w : AE D) :
    finPart D (cA D w) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e => rfl

private theorem placeIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F}
    (h : IsPlaceIdem D v ε) : ε * ε = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have : α * α = α := by
    refine DFunLike.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (α * α) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w α
    rw [map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, mul_one]
    · rw [h0 w hw, mul_zero]
  exact Prod.ext (mul_zero _) this

private theorem finPart_sub_one {D : D7} (V : HSp D) (h : GA D V) (i j : Fin V.rank) :
    finPart D ((Formalism.L2.Theta.mt V h - 1) i j) = ((finHom V h).1 - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
  congr 1
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]

theorem UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd :
    ∀ (D : D7) (V : HSp D) (l : ℕ) [Fact l.Prime]
        (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l),
        (∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F, (∀ v, a v ∈ v.adicCompletionIntegers D.host.F) → ‖ev (a ⊗ₜ[D.host.F] 1)‖ ≤ 1) →
        ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ x : Bridge.Gf V, GlobalTheory.Hk3.IsLocElt V P x →
          Matrix.map x.1.val ev = 1 := by
  intro D V l _ ev h P hP x ⟨e, f, g, hef, _, hx, hs⟩
  have hf : ev (finPart D f) = 0 := by
    rcases hef with ⟨⟨⟨h1, -⟩, h2⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hε, h1⟩, h2⟩
    · have a1 := ev_idem ev h P hP e h1 h2
      have a2 := ev_idem (ev.comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig))
        (fun a ha => by
          change ‖ev (a ⊗ₜ[D.host.F] D.sp.cm.sig 1)‖ ≤ 1
          rw [map_one]; exact h a ha) P hP e h1 h2
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), a1, finPart_cA, zero_add]
      exact a2
    · refine ev_idem ev h P hP f ?_ h2
      rw [h1, ← RingHom.map_mul, placeIdem hε]
  ext i j
  have h1 := congrArg (fun z => ev (finPart D z)) (hs i j)
  simp only [RingHom.map_mul, hf, zero_mul] at h1
  rw [finPart_sub_one, ← hx, Matrix.sub_apply, RingHom.map_sub, eq_comm, sub_eq_zero] at h1
  rw [Matrix.map_apply, h1]
  by_cases e : i = j
  · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsInjectiveSemilinearNablaTWtOpEquivariant
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

noncomputable section

namespace UpperTheory.RingTransport

open MvPolynomial GlobalTheory.ExpFrame

private theorem map_mem {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    map σ f ∈ Formalism.GradedWeylDivisibility.dualWeyl S r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro l j hlj
    have e := h2 l j hlj
    simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at e ⊢
    have hc : ∀ g : MvPolynomial (Fin r × Fin n) R,
        map σ (Formalism.GradedWeylDivisibility.colAddGen R l j g) = Formalism.GradedWeylDivisibility.colAddGen S l j (map σ g) := by
      intro g
      unfold Formalism.GradedWeylDivisibility.colAddGen
      rw [aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
      congr 2
      funext v
      split_ifs <;> simp
    rw [← hc, e, map_rename]

private def onFactor {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl R r n ν →+ Formalism.GradedWeylDivisibility.dualWeyl S r n ν where
  toFun f := ⟨map σ (f : MvPolynomial (Fin r × Fin n) R), map_mem σ f.2⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp

private theorem onFactor_smul {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (r n : ℕ) (ν : Fin n → ℕ) (c : R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : onFactor σ r n ν (c • f) = σ c • onFactor σ r n ν f := by
  ext1
  simp [onFactor, smul_eq_C_mul]

private def Tw {R S : Type} [CommRing R] [CommRing S] (_σ : R →+* S) (M : Type) : Type := M

private instance instAdd {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (M : Type) [AddCommGroup M] :
    AddCommGroup (Tw σ M) :=
  inferInstanceAs (AddCommGroup M)

private instance instMod {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) (M : Type) [AddCommGroup M] [Module S M] :
    Module R (Tw σ M) :=
  Module.compHom M σ

variable {R S : Type} [CommRing R] [CommRing S] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

private def mlin (σ : R →+* S) :
    MultilinearMap (RingHom.id R) (fun τ : ι => Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ)))
      (Tw σ (NablaT S N mu)) where
  toFun x := (PiTensorProduct.tprod S (fun τ => onFactor σ N N _ (x τ)) : NablaT S N mu)
  map_update_add' := by
    intro _ x i a b
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, map_add (f := _)]
    exact (PiTensorProduct.tprod S).map_update_add _ i _ _
  map_update_smul' := by
    intro _ x i c a
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, onFactor_smul]
    exact (PiTensorProduct.tprod S).map_update_smul _ i _ _

private def semi (σ : R →+* S) : NablaT R N mu →+ NablaT S N mu :=
  (PiTensorProduct.lift (mlin N mu σ)).toAddMonoidHom

private theorem semi_tprod (σ : R →+* S) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    semi N mu σ (PiTensorProduct.tprod R x) = PiTensorProduct.tprod S (fun τ => onFactor σ N N _ (x τ)) := by
  show (PiTensorProduct.lift (mlin N mu σ)) (PiTensorProduct.tprod R x) = _
  rw [PiTensorProduct.lift.tprod]; rfl

private theorem semi_smul (σ : R →+* S) (c : R) (y : NablaT R N mu) :
    semi N mu σ (c • y) = σ c • semi N mu σ y :=
  (PiTensorProduct.lift (mlin N mu σ)).map_smul c y

private theorem semi_left_inv (g : R ≃+* S) (y : NablaT R N mu) :
    semi N mu g.symm.toRingHom (semi N mu g.toRingHom y) = y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [semi_smul, semi_smul, semi_tprod, semi_tprod]
    congr 1
    · simp
    · congr 1
      funext τ
      ext1
      simp [onFactor, map_map, MvPolynomial.map_id]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

private theorem onFactor_rep (σ : R →+* S) (u : GL (Fin N) R) (ν : Fin N → ℕ)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R N N ν) :
    onFactor σ N N ν (Formalism.UG.dualWeylRep R N N ν u f) =
      Formalism.UG.dualWeylRep S N N ν (Matrix.GeneralLinearGroup.map σ u) (onFactor σ N N ν f) := by
  ext1
  simp only [onFactor, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.dualWeylRep_apply]
  unfold Formalism.UG.dwAct Formalism.GradedWeylDivisibility.rowAct
  rw [aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
  congr 2
  funext v
  rw [← map_inv]
  simp only [map_sum, map_mul, map_C, map_X, Matrix.GeneralLinearGroup.map_apply]

private theorem semi_grp [DecidableEq ι] (σ : R →+* S) (h : ι → GL (Fin N) R) (y : NablaT R N mu) :
    semi N mu σ (grp R N mu h y) =
      grp S N mu (fun τ => Matrix.GeneralLinearGroup.map σ (h τ)) (semi N mu σ y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, semi_smul, semi_smul, map_smul, GlobalTheory.SemilinTransport.grp_tprod, semi_tprod, semi_tprod,
      GlobalTheory.SemilinTransport.grp_tprod]
    congr 2
    funext τ
    exact onFactor_rep N σ (h τ) _ (x τ)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

private theorem det_map (σ : R →+* S) (u : GL (Fin N) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map σ u) =
      Units.map (σ : R →* S) (Matrix.GeneralLinearGroup.det u) := by
  ext
  simp [RingHom.map_det]

private theorem semi_wtOp [Fintype ι] [DecidableEq ι] (sh : ι → ℤ) (σ : R →+* S) (h : ι → GL (Fin N) R) (y : NablaT R N mu) :
    semi N mu σ (wtOp R N mu sh h y) =
      wtOp S N mu sh (fun τ => Matrix.GeneralLinearGroup.map σ (h τ)) (semi N mu σ y) := by
  rw [wtOp_apply, wtOp_apply, semi_smul, semi_grp]
  congr 1
  simp only [det_map, ← map_zpow, ← map_prod]
  rfl

end UpperTheory.RingTransport

end

theorem UpperTheory.exists_injective_semilinear_nablaT_wtOp_equivariant :
    ∀ (K K' : Type) [CommRing K] [CommRing K'] (io : K ≃+* K') (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
        (mu : ι → ℕ → ℕ) (sh : ι → ℤ), ∃ Φ : NablaT K n mu →+ NablaT K' n mu, Function.Injective Φ ∧ (∀ (c : K) u, Φ (c • u) = io c • Φ u) ∧
          ∀ (g : ι → GL (Fin n) K) u,
            Φ (wtOp K n mu sh g u) = wtOp K' n mu sh (fun τ => Matrix.GeneralLinearGroup.map io.toRingHom (g τ)) (Φ u) := by
  intro K K' _ _ io n ι _ _ mu sh
  refine ⟨UpperTheory.RingTransport.semi n mu io.toRingHom, fun y y' e => ?_,
    fun c x => UpperTheory.RingTransport.semi_smul n mu _ c x,
    fun h x => UpperTheory.RingTransport.semi_wtOp n mu sh _ h x⟩
  rw [← UpperTheory.RingTransport.semi_left_inv n mu io y, ← UpperTheory.RingTransport.semi_left_inv n mu io y', e]
end

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem core {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] {n : ℕ} (F : Frame l ι n) {H : Type} [Group H]
    (e : F.G ≃* H) (io : PadicAlgCl l ≃+* ℂ) (A : H →* (ι → GL (Fin n) (PadicAlgCl l))) (bs : ι → GL (Fin n) (PadicAlgCl l))
    (sh : ι → ℤ) (mu : ι → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hf : F.IsEig mu θ) :
    ∃ Fm : H → NablaT ℂ n mu, Fm ≠ 0 ∧
      (∀ γ, e.symm γ ∈ F.Γ → ∀ g,
        Fm (γ * g) = wtOp ℂ n mu sh (fun τ => Matrix.GeneralLinearGroup.map io.toRingHom (A γ τ)) (Fm g)) ∧
      (∀ κ : F.K, (∀ τ, Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) = (bs τ)⁻¹ * A (e κ) τ * bs τ) → ∀ c : ℂ,
        io (F.emb (F.chi κ) * ∏ τ, F.emb (F.kap κ τ).val.det ^ sh τ) * c = 1 → ∀ g, Fm (g * e κ) = c • Fm g) ∧
      ∀ i (S : Finset H), (∀ g, g ∈ F.tr i ↔ e g ∈ S) → F.cst i = 1 → (∀ a ∈ S, A a = 1) → ∀ g,
        ∑ a ∈ S, Fm (g * a) = io (θ i) • Fm g := by
  classical
  obtain ⟨f, hf0, ⟨hf1, hf2⟩, hf3⟩ := hf
  obtain ⟨Φ, hΦ, hΦs, hΦw⟩ := UpperTheory.exists_injective_semilinear_nablaT_wtOp_equivariant _ _ io n ι mu sh
  refine ⟨fun g => Φ (wtOp _ n mu sh (A g * bs) (f (e.symm g))), fun h => hf0 ?_, fun γ hγ g => ?_, fun κ hκ c hc g => ?_,
    fun i S hS hc hA g => ?_⟩
  · funext x
    have h1 : Φ (wtOp _ n mu sh (A (e x) * bs) (f (e.symm (e x)))) = 0 := congrFun h (e x)
    rw [e.symm_apply_apply, ← Φ.map_zero] at h1
    have h2 := congrArg (wtOp _ n mu sh (A (e x) * bs)⁻¹) (hΦ h1)
    rw [← Module.End.mul_apply, ← wtOp_mul, inv_mul_cancel, wtOp_one, map_zero] at h2
    exact h2
  · show Φ _ = wtOp _ _ _ _ _ (Φ _)
    rw [← hΦw, map_mul, map_mul, hf1 _ hγ, mul_assoc, wtOp_mul, Module.End.mul_apply]
  · show Φ _ = c • Φ _
    have hk : A (g * e κ) * bs = (A g * bs) * fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) := by
      funext τ
      simp only [Pi.mul_apply, map_mul, hκ]
      group
    rw [hk, map_mul, e.symm_apply_apply, wtOp_mul, Module.End.mul_apply, ← hf2 κ (e.symm g),
      wtOp_apply _ _ _ _ (fun τ => Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)), LinearMap.map_smul, LinearMap.map_smul, hΦs, hΦs, smul_smul]
    congr 1
    have hd : ∀ τ, ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ)) : (PadicAlgCl l)ˣ) :
        PadicAlgCl l) = F.emb (F.kap κ τ).val.det := fun τ => by
      simp [RingHom.map_det]
    simp only [zpow_neg, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, hd]
    rw [map_mul] at hc
    rw [map_inv₀]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hc]
    ring
  · have h1 : ∑ a ∈ S, f (e.symm g * e.symm a) = ∑ s ∈ F.tr i, f (e.symm g * s) :=
      (Finset.sum_equiv e.toEquiv hS fun s _ => by simp).symm
    have h2 := hf3 i (e.symm g)
    rw [hc, map_one, one_smul, ← h1] at h2
    show ∑ a ∈ S, Φ _ = _ • Φ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hΦs, ← LinearMap.map_smul, ← h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, map_mul, hA a ha, mul_one]

set_option maxHeartbeats 800000 in
theorem UpperTheory.exists_nonzero_vectorValued_eigenform_unitary :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime]
        (F : Frame l D.what₂.Tau (Vc D j).rank) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
        (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
        (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l), F.IsEig mu θ →
        ∃ Fm : Bridge.Gf (Vc D j) → NablaT ℂ (Vc D j).rank mu, Fm ≠ 0 ∧
          (∀ (γ : Formalism.L2.Theta.GQ (Vc D j)) (γ₀ : GL (Fin (Vc D j).rank) D.host.E),
            Formalism.L2.Theta.matHom (Vc D j) γ = Matrix.GeneralLinearGroup.map (Formalism.L2.Theta.incA D) γ₀ → ∀ g,
            Fm (Bridge.ratF (Vc D j) γ * g) = wtOp ℂ (Vc D j).rank mu T.sh
              (fun τ => Matrix.GeneralLinearGroup.map (T.io.toRingHom.comp (inc τ)) γ₀) (Fm g)) ∧
          (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) ∧
          ∀ i, (∀ a ∈ hkA p j t (ix i), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t (ix i).1) a) → ∀ g,
            ∑ a ∈ hkA p j t (ix i), Fm (g * a) = T.io (θ i) • Fm g := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t l _ F e0 ix inc T mu θ hf
  obtain ⟨A, hA⟩ : ∃ A : Bridge.Gf (Vc D j) →* (D.what₂.Tau → GL (Fin (Vc D j).rank) (PadicAlgCl l)),
      ∀ g τ, (A g τ).val = (matOf j g).map (T.ev τ) :=
    ⟨MonoidHom.pi fun τ => (Matrix.GeneralLinearGroup.map (T.ev τ)).comp (Bridge.Gf (Vc D j)).subtype, fun _ _ => rfl⟩
  obtain ⟨Fm, h0, h1, h2, h3⟩ := core F T.e T.io A T.bs T.sh mu θ hf
  refine ⟨Fm, h0, fun γ γ₀ hγ g => ?_, fun κ g => ?_, fun i hi g => ?_⟩
  · rw [h1 _ ((T.rat _).2 ⟨γ, (T.e.apply_symm_apply _).symm⟩)]
    congr 2
    funext τ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h4 : (Formalism.L2.Theta.matHom (Vc D j) γ).val a b = Formalism.L2.Theta.incA D (γ₀.val a b) := by rw [hγ]; rfl
    have h5 : matOf j (Bridge.ratF (Vc D j) γ) a b = 1 ⊗ₜ[D.host.F] γ₀.val a b :=
      congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) h4
    show T.io ((A _ τ).val a b) = T.io (inc τ (γ₀.val a b))
    rw [hA, Matrix.map_apply, h5, T.ev_rat]
  · have hrk : (T.rk : Fin (Vc D j).rank → Fin (Vc D j).rank) = id := by
      rw [Subsingleton.elim T.rk (OrderIso.refl _)]; rfl
    have hk : ∀ (k : F.K) τ, Matrix.GeneralLinearGroup.map F.emb (F.kap k τ) = (T.bs τ)⁻¹ * A (T.e k) τ * T.bs τ := by
      intro k τ
      have h := T.kap k τ
      rw [hrk, Matrix.submatrix_id_id, ← hA, ← Units.val_mul, ← Units.val_mul] at h
      exact Units.ext h
    obtain ⟨κ, hκ⟩ := κ
    obtain ⟨k, rfl⟩ := T.e.surjective κ
    obtain ⟨k', rfl⟩ : ∃ k' : F.K, (k' : F.G) = k := ⟨⟨k, (T.lev k).2 hκ⟩, rfl⟩
    exact h2 k' (hk k') _ (T.chi k' hκ) g
  · refine h3 i _ (T.tr i) (T.cst i) (fun a ha => ?_) g
    funext τ
    exact Units.ext ((hA a τ).trans
      (UpperTheory.eval_localElement_matrix_eq_one_of_prime_not_dvd D (Vc D j) l (T.ev τ) (T.ev_int τ) _ ((T.ix_range _).1 ⟨i, rfl⟩).2.2 a (hi a ha)))
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsInvariantPosDefHermitianFormAutFormUnitary
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory in
theorem UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D), V.SigOK → V.IsPosDef → ∀ (j : UA D.host.E V.rank ≃ₜ* GA D V),
        (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) →
        ∃ B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ, (∀ φ, IsAutFormU φ → φ ≠ 0 → 0 < (B φ φ).re) ∧
          ∀ k ∈ finU (E := D.host.E) (n := V.rank), ∀ φ ψ, IsAutFormU φ → IsAutFormU ψ →
            B (RU D.host.E V.rank k φ) (RU D.host.E V.rank k ψ) = B φ ψ := by
  intro D _ V hs hp j hj
  classical
  obtain ⟨h1, h2, h3, h4, h5, _h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨hR, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact V (fun τ => GlobalTheory.RepsObj.gramAt_posDef hp hs τ)

  let N : Submodule ℂ (UA D.host.E V.rank → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ ratU D.host.E V.rank, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp [ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp [ha.2 γ hγ g]⟩ }
  have hAN : ∀ φ, IsAutFormU φ → φ ∈ N := fun φ h => ⟨h.cont, h.left⟩
  have hRN : ∀ k, ∀ φ ∈ N, RU D.host.E V.rank k φ ∈ N := by
    intro k φ h
    refine ⟨h.1.comp (continuous_mul_const k), fun γ hγ g => ?_⟩
    show φ (γ * g * k) = φ (g * k)
    rw [mul_assoc, h.2 γ hγ]
  have hLC : ∀ x ∈ N, Continuous (fun g => x (j.symm g)) ∧
      ∀ γ ∈ GQ V, ∀ g, x (j.symm (γ * g)) = x (j.symm g) := by
    intro x hx
    refine ⟨hx.1.comp j.symm.continuous, fun γ hγ g => ?_⟩
    rw [map_mul]
    exact hx.2 _ ((hj _).2 (by rwa [j.apply_symm_apply])) _
  have hI : ∀ x ∈ N, ∀ y ∈ N, IntegrableOn (fun g => star (x (j.symm g)) * y (j.symm g)) 𝓕 μ := by
    intro x hx y hy
    exact GlobalTheory.MultPetersson.integrableOn_star_mul μ 𝓕 C hμ h𝓕 hC hcov (hLC x hx).1 (hLC y hy).1 (hLC x hx).2
      (hLC y hy).2
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl N
  let P : (UA D.host.E V.rank → ℂ) →ₗ[ℂ] N := Submodule.projectionOnto N q hq
  have hPN : ∀ T, ((P T : N) : UA D.host.E V.rank → ℂ) ∈ N := fun T => (P T).2
  have hPid : ∀ T ∈ N, ((P T : N) : UA D.host.E V.rank → ℂ) = T := fun T hT =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨T, hT⟩)
  let F : (UA D.host.E V.rank → ℂ) → (UA D.host.E V.rank → ℂ) → ℂ := fun x y =>
    ∫ g in 𝓕, star ((P x).1 (j.symm g)) * (P y).1 (j.symm g) ∂μ
  let B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F, map_add (f := _), Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x') _ (hPN y))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, RingHom.id_apply, starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F, map_add (f := _), Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x) _ (hPN y'))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, RingHom.id_apply, starRingEnd_apply]
      ring)
  have hB : ∀ x ∈ N, ∀ y ∈ N, B x y = ∫ g in 𝓕, star (x (j.symm g)) * y (j.symm g) ∂μ := by
    intro x hx y hy
    show F x y = _
    simp only [F, hPid x hx, hPid y hy]
  refine ⟨B, ?_, ?_⟩
  · intro T hT' h0
    have hT := hAN T hT'
    rw [hB _ hT _ hT]
    have hre : ∫ g in 𝓕, star (T (j.symm g)) * T (j.symm g) ∂μ = ((∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    rw [hre, Complex.ofReal_re]
    have hnn : 0 ≤ ∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
    refine lt_of_le_of_ne hnn fun hz => h0 ?_
    have hi : IntegrableOn (fun g => ‖T (j.symm g)‖ ^ 2) 𝓕 μ := by
      have := (hI T hT T hT).norm
      have e2 : (fun g => ‖star (T (j.symm g)) * T (j.symm g)‖) = fun g => ‖T (j.symm g)‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 hz.symm
    have := GlobalTheory.SchurConst.eq_zero_of_ae μ 𝓕 hμ h𝓕 (fun g => T (j.symm g)) (hLC T hT).1 (hLC T hT).2 (by
      filter_upwards [hae] with g hg
      simpa using hg)
    funext x
    have h := congrFun this (j x)
    simpa using h
  · intro k _hk T T' hT0 hT0'
    have hT := hAN T hT0
    have hT' := hAN T' hT0'
    rw [hB _ (hRN k T hT) _ (hRN k T' hT'), hB _ hT _ hT']
    haveI := h5
    haveI := h4
    haveI := h2
    haveI := h7
    haveI := hR
    have hmap : Measure.map (fun g => g * j k) μ = μ := map_mul_right_eq_self μ (j k)
    have hh : ∀ x : UA D.host.E V.rank → ℂ, ∀ g, RU D.host.E V.rank k x (j.symm g) = x (j.symm (g * j k)) := by
      intro x g
      rw [map_mul, j.symm_apply_apply]
      rfl
    simp only [hh]
    have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => star (T (j.symm g)) * T' (j.symm g)) (γ * g) =
        (fun g => star (T (j.symm g)) * T' (j.symm g)) g := by
      intro γ hγ g
      simp only [(hLC T hT).2 γ hγ, (hLC T' hT').2 γ hγ]
    exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 (j k) hmap _ hinv (hI T hT T' hT')).2
end

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

