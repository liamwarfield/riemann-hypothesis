module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModels
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBound
public import Development.WeilBound.CoreStatements.HodgeTatePoints.LieMultComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginComponentSections

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemPtsOverOfMemMcPts
section -- merged from Development.WeilBound.CoreStatements.IntegralTransfer.PetTie
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Xgy

namespace PetTie

open scoped ENNReal

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

end FD

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r} {W : HSp D}
  {dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r}

end PetTie


end PositivityTheory.Xgy
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.OS

section Vals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hasVal_add {a : K → ℤ} {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y a s z w)
    (h' : Small.HasVal y a s' z w') : Small.HasVal y a (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  obtain ⟨dg', dh', g', f', hg', hf', hd', e', hz0', ez'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := funext fun k => by
    have h1 := hd k
    have h2 := hd' k
    simp only [Pi.add_apply]
    omega
  refine ⟨dg + dh', dh + dh', g * f' + g' * f, f * f',
    FinRd.ValSub.mh_add (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg hf') ?_,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hf hf', fun k => ?_, ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hg' hf
  · have h1 := hd k
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_add (f := _), map_mul, e, e']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · simp only [map_add (f := _), map_mul, ez, ez']
    ring

theorem hasVal_zsmul {a : K → ℤ} {s : Ω} {w : 𝕜} (n : ℤ) (h : Small.HasVal y a s z w) :
    Small.HasVal y a (n • s) z (n • w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  refine ⟨dg, dh, MvPolynomial.C n * g, f, ?_, hf, hd, ?_, hz0, ?_⟩
  · intro m hm k
    rw [MvPolynomial.C_mul'] at hm
    exact hg m (MvPolynomial.support_smul hm) k
  · rw [map_mul, e, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]
  · rw [map_mul, ez, MvPolynomial.aeval_C, ← mul_assoc]
    simp [zsmul_eq_mul]

theorem hasVal_zero_of {a : K → ℤ} {s : Ω} {w : 𝕜} (h : Small.HasVal y a s z w) :
    Small.HasVal y a (0 : Ω) z (0 : 𝕜) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  exact ⟨dg, dh, 0, f, FinRd.ValSub.mh_zero dg, hf, hd, by simp, hz0, by simp⟩

end Vals

section Coef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

end Coef

section Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Fin

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

end Arch

section ArchD

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

end ArchD

section Emb

end Emb

end GlobalTheory.CompanionTheory.Ar.Rec.OS

namespace GlobalTheory.CompanionTheory.Ar.Rec


end GlobalTheory.CompanionTheory.Ar.Rec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyOverLieBasisDegree
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.QacInt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Qac

section Pull

open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels GlobalTheory.KeyCancel IsLocalRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isFibreOf_pull_local {R R' R'' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] [CommRing R'']
    {f : R →+* R'} {f' : R' →+* R''} {t : SAB H (Sp R)} {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f))
    {θ : t.PP.L.Sec} {n : ℕ} {v : Fin n → (epsR R ⟶ t.G)}
    (hθ : ∀ b : Sp R, ∃ y : t.G.left, t.G.hom y = b ∧ y ∈ Out.nonzeroLocus θ) (hv : IsLieBasis v)
    {x : KeyIn R''} (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ v (f'.comp f)) :
    ∃ (θ' : t'.PP.L.Sec) (v' : Fin n → (epsR R' ⟶ t'.G)), NonzeroClosed (X := t'.G) θ' ∧ IsLieBasis v' ∧
      IsFibreOf x t'.G t'.PP.L t'.PP.rig θ' v' f' := by
  obtain ⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := hx
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨θ', hs⟩ := sec_pull_down g t.PP.isLB t'.PP.isLB θ
  obtain ⟨v', hv', hvv⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ f t.G t'.G m.φ m.cart t.semi.smooth n v hv
  have he : eSec t'.G ≫ m.φ = spMap f ≫ eSec t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec t.G) m.base)
  have hrig : m.cm.rigPull t.PP.L t.PP.rig = rigPullOf m.φ (spMap f) he t.PP.L t.PP.rig := by
    have key : ∀ (a b : Sp R' ⟶ Sp R) (_ : a = b) ha hb,
        rigPullOf (G' := t'.G) m.φ a ha t.PP.L t.PP.rig = rigPullOf m.φ b hb t.PP.L t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr
  refine ⟨θ', v', ?_, hv', ?_⟩
  · obtain ⟨z, hz, hz'⟩ := hθ (spMap f (closedPoint R'))
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z (closedPoint R') hz
    obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    have hk : m.φ y ∈ t.PP.L.U k := t.G.left.basicOpen_le _ hb
    obtain ⟨l, hl⟩ := exists_chart t'.PP.isLB y
    have u : IsUnit (gs (𝟙 _) (m.φ y) _ (θ.f k)) := by
      rw [gs_eq (𝟙 _) (m.φ y) _ hk]; exact (t.G.left.mem_basicOpen _ _ hk).1 hb
    have u₁ : IsUnit (gs m.φ y _ (θ.f k)) := by rw [gs_stalkMap m.φ y _ hk]; exact u.map _
    have e := hs _ (𝟙 _) y k l hk hl
    rw [Category.id_comp] at e
    have u₂ := isUnit_of_mul_isUnit_right (e ▸ u₁)
    rw [gs_eq (𝟙 _) y _ hl] at u₂
    exact ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (t'.G.left.mem_basicOpen _ _ hl).2 u₂⟩⟩
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp _ _
  have hc := m.cart
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x.P.A.left ⟶ t'.G.left, φ' ≫ m.φ = φ'' ∧ φ' ≫ t'.G.hom = x.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x.P.A ≫ φ' = spMap f' ≫ eSec t'.G := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      have a₂ : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  obtain ⟨w', T⟩ := exists_cancel t.PP.isLB w w'' g g'' t'.PP.isLB x.P.isLB
  have r := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig (spMap f) _ (rigPull_le m.φ (spMap f) he t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec t.G) _ x.rig t.PP.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ m.φ) (spMap (f'.comp f)) he'' t.PP.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp (Chart.dualMapR f) = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', he', w', hg'', Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec t'.G) _ x.rig t'.PP.rig (spMap f') _ (rigPull_le φ' (spMap f') he' t'.PP.L)
      (fun _ => rfl)).2 (T.pmaps_cancel t.PP.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' θ' x.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (φ' (q z)))
    have a := hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' θ x.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hvv, ← hFF, ← Category.assoc, spMap_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem key_mem_of_dvr {κ : KeyRule} (hκ : IsKeyRule κ) (hpow : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K) (j : ℕ),
      GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j)
    {A V K : Type} [CommRing A] [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] (f : A →+* V) (t : SAB H (Sp A)) (θ : t.PP.L.Sec) {n : ℕ} (w : Fin n → (epsR A ⟶ t.G))
    (x : KeyIn K) (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ w ((algebraMap V K).comp f)) (hw : IsLieBasis w)
    (hθ : ∀ b : Sp A, ∃ y : t.G.left, t.G.hom y = b ∧ y ∈ Out.nonzeroLocus θ) :
    ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := by
  obtain ⟨t', ⟨m⟩⟩ := Kftwo.exists_pull (spMap f) t
  obtain ⟨θ', w', h₁, h₂, h₃⟩ := exists_isFibreOf_pull_local m hθ hw hx
  exact Kftwo.key_isUnit hκ hpow t' θ' w' x h₃ h₂ h₁

end Pull

theorem isIntegral_of_forall_mem {L : Type} [Field L] [NumberField L] (a : L)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      a ∈ Localization.subalgebra.ofField L _ v.asIdeal.primeCompl_le_nonZeroDivisors) : IsIntegral ℤ a := by
  have hb : a ∈ (⊥ : Subalgebra (𝓞 L) L) := by
    rw [← IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot (𝓞 L) L, Algebra.mem_iInf]
    exact h
  obtain ⟨b, rfl⟩ := Algebra.mem_bot.1 hb
  exact b.isIntegral_coe

section Main

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights TensorProduct GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem key_isIntegral : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) := by
  intro κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H L _ _ t th x v ⟨φ, he, w, h1, h2, h3, h4, h5⟩ hv hθ
  have hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, _root_.mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, _root_.mul_one] using k₅
  have hx : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsFibreOf x t.G t.PP.L t.PP.rig th v (algebraMap (𝓞 L) L) :=
    ⟨φ, he, w, rfl, dualMap (algebraMap (𝓞 L) L), h1, h2, h3, h4,
      fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl], by ext <;> simp [dualMap], h5⟩
  refine isIntegral_of_forall_mem _ fun p => ?_
  obtain ⟨V, hV⟩ : ∃ V : Subalgebra (𝓞 L) L,
      V = Localization.subalgebra.ofField L _ p.asIdeal.primeCompl_le_nonZeroDivisors := ⟨_, rfl⟩
  have hl : IsLocalization.AtPrime V p.asIdeal := by
    rw [hV]; exact Localization.subalgebra.isLocalization_ofField L _ _
  have hd : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) p.ne_bot V
  rw [IsScalarTower.algebraMap_eq (𝓞 L) V L] at hx
  obtain ⟨u, hu⟩ := key_mem_of_dvr hκ (GlobalTheory.KeyCl.rule_pow κ k₁ k₂ k₄) (algebraMap (𝓞 L) V) t th v x hx hv hθ
  rw [← hV, hu]
  exact (u : V).2

theorem keydeg_integral : KeyBadSt → ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) :=
  fun _ => key_isIntegral

end Main

end PositivityTheory.HtPt.Qac
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyOverLieBasisDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.key_over_lie_basis_degree : KeyBadSt → ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) := by
  first | exact @PositivityTheory.HtPt.Qac.keydeg_integral | exact PositivityTheory.HtPt.Qac.keydeg_integral
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyOverLieBasisDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.key_over_lie_basis_degree : KeyBadSt → ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ → GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp (𝓞 L))) (th : t.PP.L.Sec) (x : KeyIn L) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ t.G)), KeyOver (algebraMap (𝓞 L) L) t th x v → IsLieBasis v → KeyDeg.NonVan t.G.hom th → IsIntegral ℤ (κ L x : L) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.key_over_lie_basis_degree | exact GlobalTheory.CompanionTheory.Relay.key_over_lie_basis_degree | (intros; apply GlobalTheory.CompanionTheory.Relay.key_over_lie_basis_degree <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginModelComponentBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginModelComponentBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinLink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem chart_value {h : GenFrEx Xo c} (C : GlobalTheory.Reg.FChart h) {L : Type} [Field L] [Algebra c.F L]
    (ψ : C.R →ₐ[c.F] L) (z w : FrPt Xo c L) (t : Ix Dw → Lˣ) (hz : FrMap ψ C.y z) (hb : FrBor t z w)
    {a : WZ E} {g : Rul Xo c} (hg : g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) :
    ∃ s : C.R, (s : Om C.Z) = ((∏ i, C.t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : (Om C.Z)ˣ) : Om C.Z) * evC h C.Z g ∧
      evR Xo c g w = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * ψ s := by
  obtain ⟨⟨-, hC, hB, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  have hWD := evalWD_fr hC
  have key : ∀ {T : Type} [CommRing T] [Algebra c.F T] (p : TRing c.F) (χ : p.R →ₐ[c.F] T) (u : FrPt Xo c p.R)
      (v : FrPt Xo c T), FrMap χ u v → evR Xo c g v = χ (g p u) := by
    intro T _ _ p χ u v hv
    have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) v := ⟨p, χ, u, hv⟩
    unfold evR evalAt
    rw [dite_eq_left hft]
    exact hWD g hg.1 T _ p _ χ _ u v hft.choose_spec.choose_spec.choose_spec hv
  have hbor : ∀ {T : Type} [CommRing T] [IsReduced T] [Algebra c.F T] (t : Ix Dw → Tˣ) (v v' : FrPt Xo c T), FrBor t v v' →
      evR Xo c g v' = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Tˣ) : T) * evR Xo c g v := by
    intro T _ _ _ t v v' hv
    exact FinRd.evalAt_bor_zpow hB (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) hg.1
      (fun p t y y' hb => by rw [hg.2 p t y y' hb, Units.coe_prod]) T t v v' (hA T v) (hA T v') hv
  obtain ⟨q, χ, u, hu⟩ := hA C.R C.y
  refine ⟨χ (g q u), ?_, ?_⟩
  · have h1 := hbor C.t _ _ C.bor
    rw [key q (C.R.val.comp χ) u C.yg (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ C.R.val hu C.gen)] at h1
    exact h1
  · rw [hbor t _ _ hb, key q (ψ.comp χ) u z (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ ψ hu hz), AlgHom.comp_apply]

theorem prod_exZ_zero {M : Type} [CommGroup M] (t : Ix Dw → M) : ∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (0 : WZ E) i = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rcases i with _ | x
  · simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]
  · simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]

private theorem mul_mem_secZ' {a b : WZ E} {f g : Rul Xo c} (hf : f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a)
    (hg : g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c b) : f * g ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (a + b) := by
  obtain ⟨hfn, hfb⟩ := hf
  obtain ⟨hgn, hgb⟩ := hg
  refine ⟨fun p q φ y z hyz => ?_, fun p t y y' hb => ?_⟩
  · show f q z * g q z = φ (f p y * g p y)
    rw [hfn p q φ y z hyz, hgn p q φ y z hyz, map_mul]
  · show f p y' * g p y' = _ * (f p y * g p y)
    rw [hfb p t y y' hb, hgb p t y y' hb]
    have hex : ∀ i, GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw (a + b) i =
        GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i + GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw b i := by
      intro i
      rcases i with _ | x <;> simp [GlobalTheory.CompanionTheory.Ar.Rec.exZ]
    simp only [hex, zpow_add, Units.val_mul, Finset.prod_mul_distrib]
    ring

private theorem one_mem_secZ_zero' : (1 : Rul Xo c) ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E) := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    exact (map_one φ).symm
  · show (1 : p.R) = _ * 1
    rw [mul_one, ← Units.coe_prod, prod_exZ_zero, Units.val_one]

private theorem evC_mul_geometry (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f * g) = evC h Z f * evC h Z g := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_mul _ _ f g _

private theorem evC_add' (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f + g) = evC h Z f + evC h Z g := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_add _ _ f g _

private theorem evC_zero' (h : GenFrEx Xo c) (Z : Comp Xo c) : evC h Z (0 : Rul Xo c) = 0 := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_zero _ _ _

private theorem evC_one_of_genFromTest {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) (Z : Comp Xo c) :
    evC h Z (1 : Rul Xo c) = 1 := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_one _ _ _ (hT Z)

private theorem evC_smul' (h : GenFrEx Xo c) (Z : Comp Xo c) (k : c.F) (f : Rul Xo c) :
    evC h Z (k • f) = algebraMap c.F (Om Z) k * evC h Z f := by
  unfold Formalism.L2.Pj.evC Formalism.L2.Pj.evR
  exact Formalism.L2.Pj.evalAt_smul _ _ k f _

theorem exists_ratio {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) {Z : Comp Xo c} {a : WZ E} {N : ℕ}
    {g : Fin (N + 1) → Rul Xo c} (hg : ∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) (hB : BirOn h Z g) (x : Om Z) :
    ∃ (u : WZ E) (f f' : Rul Xo c), f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c u ∧ f' ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c u ∧
      evC h Z f' ≠ 0 ∧ x * evC h Z f' = evC h Z f := by
  have hx : x ∈ (⊤ : IntermediateField c.F (Om Z)) := IntermediateField.mem_top
  rw [← hB.2] at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨a, g j, g 0, hg j, hg 0, hB.1, div_mul_cancel₀ _ hB.1⟩
  | algebraMap k =>
    refine ⟨0, k • 1, 1, Submodule.smul_mem _ k one_mem_secZ_zero', one_mem_secZ_zero', ?_, ?_⟩
    · rw [evC_one_of_genFromTest hT]; exact one_ne_zero
    · rw [evC_smul', evC_one_of_genFromTest hT]
  | add x y _ _ ihx ihy =>
    obtain ⟨u1, f1, f1', hf1, hf1', h1, e1⟩ := ihx
    obtain ⟨u2, f2, f2', hf2, hf2', h2, e2⟩ := ihy
    refine ⟨u1 + u2, f1 * f2' + f2 * f1', f1' * f2',
      add_mem (mul_mem_secZ' hf1 hf2') (by rw [add_comm u1 u2]; exact mul_mem_secZ' hf2 hf1'),
      mul_mem_secZ' hf1' hf2', ?_, ?_⟩
    · rw [evC_mul_geometry]; exact mul_ne_zero h1 h2
    · rw [evC_add', evC_mul_geometry, evC_mul_geometry, evC_mul_geometry, ← e1, ← e2]; ring
  | inv x _ ihx =>
    obtain ⟨u, f, f', hf, hf', h0, e⟩ := ihx
    by_cases hx0 : x = 0
    · exact ⟨u, 0, f', Submodule.zero_mem _, hf', h0, by rw [hx0, inv_zero, zero_mul, evC_zero']⟩
    · refine ⟨u, f', f, hf', hf, ?_, ?_⟩
      · rw [← e]; exact mul_ne_zero hx0 h0
      · rw [← e, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x y _ _ ihx ihy =>
    obtain ⟨u1, f1, f1', hf1, hf1', h1, e1⟩ := ihx
    obtain ⟨u2, f2, f2', hf2, hf2', h2, e2⟩ := ihy
    refine ⟨u1 + u2, f1 * f2, f1' * f2', mul_mem_secZ' hf1 hf2, mul_mem_secZ' hf1' hf2', ?_, ?_⟩
    · rw [evC_mul_geometry]; exact mul_ne_zero h1 h2
    · rw [evC_mul_geometry, evC_mul_geometry, ← e1, ← e2]; ring

attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem frame_of_birOn {h : GenFrEx Xo c} (hT : GenFromTest Xo c h) {Z : Comp Xo c} {L : Type} [Field L]
    [Algebra c.F L] (y : FrPt Xo c L) (φ : Om Z →ₐ[c.F] L) (t : Ix Dw → Lˣ)
    (hrd : ∀ (a : WZ E), ∀ f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a,
      evR Xo c f y = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * φ (evC h Z f))
    (hE : ∀ Z' : Comp Xo c, ∃ ε ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E), evC h Z' ε = 1 ∧
      ∀ Z'', Z'' ≠ Z' → evC h Z'' ε = 0)
    {a : WZ E} {N : ℕ} {g : Fin (N + 1) → Rul Xo c} (hg : ∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a)
    (hB : BirOn h Z g) :
    ∃ (w : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap φ (genFr h Z) w ∧ FrBor t' w y := by
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z, t', hz, hb⟩ := hA h L y
  have hZ : C.Z = Z := by
    by_contra hne
    obtain ⟨ε, hε, e1, e0⟩ := hE C.Z
    obtain ⟨s, hs, hv⟩ := chart_value C ψ z y t' hz hb hε
    rw [prod_exZ_zero, e1, Units.val_one, one_mul] at hs
    have hs1 : s = 1 := Subtype.ext hs
    rw [hrd 0 ε hε, e0 Z (Ne.symm hne), map_zero, mul_zero, prod_exZ_zero, hs1, map_one, Units.val_one, one_mul] at hv
    exact zero_ne_one hv
  subst hZ
  have hψ : φ.comp C.R.val = ψ := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨u, f, f', hf, hf', hn, e⟩ := exists_ratio hT hg hB (x : Om C.Z)
    obtain ⟨sf, hsf, hvf⟩ := chart_value C ψ z y t' hz hb hf
    obtain ⟨sg, hsg, hvg⟩ := chart_value C ψ z y t' hz hb hf'
    have hs : sf = x * sg := by
      apply Subtype.ext
      show (sf : Om C.Z) = (x : Om C.Z) * (sg : Om C.Z)
      rw [hsf, hsg, ← e]; ring
    have hne : evR Xo c f' y ≠ 0 := by
      rw [hrd u f' hf']
      exact mul_ne_zero (Units.ne_zero _) ((map_ne_zero φ).2 hn)
    apply mul_right_cancel₀ hne
    show φ (x : Om C.Z) * _ = _
    have h1 : φ (x : Om C.Z) * evR Xo c f' y = evR Xo c f y := by
      rw [hrd u f hf, hrd u f' hf', ← e, map_mul]; ring
    rw [h1, hvf, hvg, hs, map_mul]; ring
  have hz' : FrMap φ C.yg z := frMap_cancel _ _ _ C.R.val φ C.y C.yg z C.gen (by rw [hψ]; exact hz)
  obtain ⟨y', hy'⟩ := hL.bc _ _ φ (genFr h C.Z)
  obtain ⟨-, hmul, -, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  exact ⟨y', _, hy', hmul _ _ _ _ _ (frBorBC _ _ φ C.t _ _ y' z C.bor hy' hz') hb⟩

theorem indicators {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
    (hC : CompLaws U h e) (Z' : Comp Xo c) : ∃ ε ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c (0 : WZ E), evC h Z' ε = 1 ∧
      ∀ Z'', Z'' ≠ Z' → evC h Z'' ε = 0 := by
  obtain ⟨hnat, hw⟩ := hC.e_sec Z'
  refine ⟨e Z', ⟨hnat, fun p t y y' hb => ?_⟩, (hC.e_val Z').1, (hC.e_val Z').2⟩
  have hw0 : Formalism.L2.Pj.wchar (Formalism.L2.Pj.ex Dw 0 0) t = 1 := by
    unfold Formalism.L2.Pj.wchar
    refine Finset.prod_eq_one fun i _ => ?_
    rcases i with _ | x <;> simp [Formalism.L2.Pj.ex]
  rw [hw p t y y' hb, hw0, ← Units.coe_prod, prod_exZ_zero, Units.val_one]

section Read

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

theorem linked_of_birOn {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {e : Comp Xo c → Rul Xo c}
    (hC : CompLaws U h e) (Rd : Reading Fr h Z) {a : WZ E} {N : ℕ} {g : Fin (N + 1) → Rul Xo c}
    (hg : ∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) (hB : BirOn h Z g) : FinTr.Linked Rd := by
  letI := Small.cstAlg Or
  exact frame_of_birOn hC.genT Fr.y₀ (FinTr.phiAlg Rd) Rd.t (fun a f hf => Rd.rd_eq a f hf)
    (indicators hC) hg hB

end Read

theorem linked : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y₀ : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)), Top.GoodOrigin Y₀ T → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), FinTr.Linked Rd := by
  intro hG E _ _ _ H Dw l Xo c r U h e hC Y₀ _ T hO O _ β Y SS RM Sys Fx Or Fr Z Rd
  obtain ⟨a, N, g, hg, hB⟩ := GlobalTheory.T.good_origin_component_sections hG E H Dw l Xo c r U h e hC Y₀ T hO Z
  exact linked_of_birOn hC Rd hg hB

end GlobalTheory.CompanionTheory.Ar.Plug.FinLink
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginModelComponentBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_model_component_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y₀ : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)), Top.GoodOrigin Y₀ T → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), FinTr.Linked Rd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.FinLink.linked | exact GlobalTheory.CompanionTheory.Ar.Plug.FinLink.linked | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.FinLink.linked <;> assumption)
end
end
