module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatKRatMulLev
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem latK_rat_mul_lev : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (a : 𝓞 D.host.E) (x : GL (Fin N) (AfE D.host.F D.host.E)) (κ : S.U), ∀ g ∈ UJ (sigD D : D.host.E →+* D.host.E) J, latK D.sp J a (GlobalTheory.TwU.ratA D.host.F g * x * κ.1) S.Lb = SDLat.smulLat (eMat rfl (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (latK D.sp J a x S.Lb) := by
  intro D N J T f bad S a x κ g hg
  letI := D.host.cmStar
  rw [Formalism.MainNotions.G.KAat.latK_tr _ _ _ _ _ g hg (GlobalTheory.TwU.hatStab_of_lev S κ)]
  unfold SDLat.smulLat eMat
  congr 1
  ext v
  simp [Matrix.toLin'_toMatrix']

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTuple
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000

theorem smulLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {a N : ℕ} (hr : a = N) (σ : E →+* E) (Jm : Matrix (Fin N) (Fin N) E)
    (g : GL (Fin N) E) (A A' : Submodule (𝓞 E) (Fin a → E)) (B B' : Submodule (𝓞 E) (Fin N → E)) (hA : HEq A B) (hA' : HEq A' B')
    (hB : B' = SDLat.smulLat (eMat rfl σ Jm g) B) : A' = SDLat.smulLat (eMat hr σ Jm g) A := by
  subst hr
  cases eq_of_heq hA
  cases eq_of_heq hA'
  exact hB

theorem kerN_smul : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLat hMove
  have hLat' : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLat
  have hch : J.chart std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) = J.chart std j hj.le (c, La) :=
    GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c _ _ hLat' hLat
  have h1 := (hD j hj.le (c, La) hLat).2.2.1
  have h2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hLat').2.2.1
  obtain ⟨hg, hpt, -, -⟩ := hMove
  rw [hch, hpt] at h2
  exact smulLat_of_heq hr _ _ g _ _ _ _ h1 h2 (latK_rat_mul_lev D _ _ _ _ _ _ _ _ κ g hg)

end GlobalTheory.TwV.Xc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTupleStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_movedLatticeTuple : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  first | exact @GlobalTheory.TwV.Xc.kerN_smul | exact GlobalTheory.TwV.Xc.kerN_smul | (intros; apply GlobalTheory.TwV.Xc.kerN_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLatticeTupleMoveByRationalIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPtMoveEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem isPt_move_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad), LocGood σ J A → LocInt A → LocHyp S A → A.ActB → (∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) → ∀ (i : G.comp) (γ : (G.lev i).Γ), A.gamI i γ ∈ UJ (σ : E →+* E) J → ∀ κa : S.U, A.IsAway i γ κa.1 → ∀ (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))), (∀ v, colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) = colSpan (G.P.W v) (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) → ∀ x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∃ κ : S.U, x'.1 = GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κ.1 ∧ S.chi κ * S.chi κa = 1 := by
  intro F E _ _ _ _ _ σ n p G A J T f bad S hG hW hH hA hbad i γ hγ κa hκa g g' hg x x' hx hx'
  have hy := A.isPt_smul hA i g x.1 κa.1 hx γ hκa
  have hyU : GlobalTheory.TwU.ratA F (A.gamI i γ) * x.1 * κa.1⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (ratInU _ hγ) x.2) (Subgroup.inv_mem _ ((S.U_eq κa.1).1 κa.2).1)
  obtain ⟨κ₁, e₁, hχ₁⟩ := ptOne_of (A := A) S hW hH hbad i (fun v => colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (fun v => (G.lev i).act v γ * g v) g' ⟨_, hyU⟩ x' (fun v => rfl) (fun v => (hg v).symm) hy hx'
  refine ⟨κa⁻¹ * κ₁, ?_, ?_⟩
  · rw [e₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rw [map_mul, map_inv]
    apply Units.ext
    simp [hχ₁]

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLatticeTupleMoveByRationalIsometry
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.Mv0

theorem frm_gen {E Q : Type} [Field E] [Field Q] (σ : E →+* E) {a N : ℕ} (rk hr : a = N) (J0 : Matrix (Fin N) (Fin N) E)
    (B g : GL (Fin N) E) (iw : E →+* Q) (M : GL (Fin a) Q) (hM : castGL rk Q M = bc iw (B⁻¹ * g * B)) :
    (((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) * (M : Matrix (Fin a) (Fin a) Q) =
    (eMat hr σ J0 g).map iw *
      ((((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) := by
  subst rk
  have hJ : J0.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = J0 := by ext i j; simp
  have hB : ((reGL (finCongr (rfl : a = a)) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = (B : Matrix (Fin a) (Fin a) E) := by
    ext i j
    show (Matrix.reindexAlgEquiv E E (finCongr (rfl : a = a)) (B : Matrix (Fin a) (Fin a) E)) i j = _
    simp [Matrix.reindexAlgEquiv_apply]
  have hMm : (M : Matrix (Fin a) (Fin a) Q) = ((B⁻¹ * g * B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map iw := by
    ext i j
    have h1 := congrArg (fun x : GL (Fin a) Q => (x : Matrix (Fin a) (Fin a) Q) i j) hM
    simp only [castGL_apply] at h1
    exact h1
  have hE : eMat hr σ J0 g = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      (g : Matrix (Fin a) (Fin a) E) *
      LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) := by
    have e0 : eMat hr σ J0 g = LinearMap.toMatrix' (stdG σ J0 g).toLinearMap := by ext i j; simp [eMat]
    rw [e0]
    have e1 : (stdG σ J0 g).toLinearMap = (stdCo σ J0 : (Fin a → E) →ₗ[E] (Fin a → E)) ∘ₗ (Matrix.toLin' (g : Matrix (Fin a) (Fin a) E)) ∘ₗ
        ((stdCo σ J0).symm : (Fin a → E) →ₗ[E] (Fin a → E)) := by
      apply LinearMap.ext; intro x; rfl
    rw [e1, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
  have hsub : ∀ A : Matrix (Fin a) (Fin a) Q, A.submatrix (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = A := fun A => by ext i j; rfl
  rw [hsub, hJ, hB, hMm, hE, ← Matrix.map_mul, ← Matrix.map_mul]
  congr 1
  have hci : LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hBB : (B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
        ((B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) * (g : Matrix (Fin a) (Fin a) E) * (B : Matrix (Fin a) (Fin a) E) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [hBB, Matrix.mul_one]
          calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) * (g : Matrix (Fin a) (Fin a) E) *
                (LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
                  LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E))) * (B : Matrix (Fin a) (Fin a) E) := by
                rw [hci, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc.Mv0

open Formalism.MainNotions.G.CmpJ.PStabEq

theorem regl2 {R : Type} [CommRing R] {a N : ℕ} (h : a = N) (h' : N = a) (y : GL (Fin N) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h') y) = y := by
  subst h
  ext i j
  show (Matrix.reindexAlgEquiv R R (finCongr (rfl : a = a)) (Matrix.reindexAlgEquiv R R (finCongr h') (y : Matrix (Fin a) (Fin a) R))) i j = _
  simp [Matrix.reindexAlgEquiv_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n p : ℕ} {G : GAtP p}
  {A : LocAt F E n G} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {S : StepLevel F E σ J T f bad}
  {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem ptEps_spec (H1 : OneHyp S A y) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    A.IsPt i g (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∧
      (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨c, γ₀, κ₀, hγ₀, hp⟩ := ptEx_of H1.good S y H1.y_bij.2 i g
  exact Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hp, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ₀) (y c).2) (U_le κ₀.2)⟩

theorem pt_gen (H1 : OneHyp S A y) (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) (hL : G.P.IsLatTup L) (κa : S.U)
    (hκa : A.IsAway i γ κa.1) (bas : G.P.Tup → ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hbas : ∀ L' v, bas L' v = Classical.epsilon fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) :
    ∃ κ : S.U, (Classical.epsilon fun x => A.IsPt i (bas ((G.lev i).smul γ L)) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
      GlobalTheory.TwU.ratA F (A.gamI i γ) * (Classical.epsilon fun x => A.IsPt i (bas L) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) * κ.1 ∧
      S.chi κ * S.chi κa = 1 := by
  obtain ⟨g0, hg0⟩ := exists_bases1 L hL
  have hb : ∀ (L' : G.P.Tup) (g1 : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)),
      (∀ v, L' v = colSpan (G.P.W v) (g1 v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
      ∀ v, L' v = colSpan (G.P.W v) (bas L' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
    intro L' g1 h v
    rw [hbas]
    exact Classical.epsilon_spec (p := fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ⟨g1 v, h v⟩
  have hbL := hb L g0 hg0
  have hbγ := hb _ _ (smul_colSpan i γ L g0 hg0)
  have hs := ptEps_spec H1 i (bas L)
  have hs' := ptEps_spec H1 i (bas ((G.lev i).smul γ L))
  exact GlobalTheory.TwV.Xc.isPt_move_eq F E σ n p G A J T f bad S H1.good H1.int H1.hypP H1.actB H1.bad_p i γ (H1.gamU i γ) κa hκa
    (bas L) (bas ((G.lev i).smul γ L)) (fun v => (hbγ v).symm.trans (smul_colSpan i γ L (bas L) hbL v))
    ⟨_, hs.2⟩ ⟨_, hs'.2⟩ hs.1 hs'.1

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem moveBy_zero : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (c : (sysS H X std).Lv.comp 0) (La : ((sysS H X std).Pj 0).Tup) (γ : ((sysS H X std).Lv.lev 0 c).Γ), ((sysS H X std).Pj 0).IsLatTup La → ∃ g κ, MoveBy std J 0 (Nat.zero_le _) c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS c La γ hL
  have hfr : ∀ (hr : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (v : (sysS H X std).Pl),
      (J.fd std).frM 0 (c, La) v * (gamAt (sysS H X std) 0 c γ v : Matrix _ _ _) =
        (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ((A0 J).gamI c γ)).map (J.rho std v) * (J.fd std).frM 0 (c, La) v := by
    intro hr v
    exact Mv0.frm_gen _ (A0 J).rk hr (gramN D 0 (Nat.zero_le _)) (A0 J).B ((A0 J).gamI c γ) ((A0 J).iw v) _ (J.one.actB c v γ)
  obtain ⟨κa, hκa⟩ := awayEx_of J.one.good _ J.one.gam c γ
  obtain ⟨ra, hra1, hra2⟩ := (lev0AtOf_compatible J.Gd.cmp u w hg).chi c γ κa hκa
  have hJpt : ∀ L', (J.pt std 0 (Nat.zero_le _) (c, L')).1 = Classical.epsilon fun x => (A0 J).IsPt c (basesAt _ std _ _ _ _ _ _ _ 0 L') x ∧
      x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro L'
    have hs := Mv0.ptEps_spec J.one c (basesAt _ std _ _ _ _ _ _ _ 0 L')
    have hspec : J.IsPt std 0 (Nat.zero_le _) (c, L') (J.pt std 0 (Nat.zero_le _) (c, L')) :=
      Classical.epsilon_spec (p := J.IsPt std 0 (Nat.zero_le _) (c, L')) ⟨⟨_, hs.2⟩, (A0 J).rk, (Mv0.regl2 _ _ _).symm⟩
    obtain ⟨hr, e⟩ := hspec
    rw [e]
    exact Mv0.regl2 _ _ _
  obtain ⟨κ, hκ1, hκ2⟩ := Mv0.pt_gen J.one c γ La hL κa hκa (basesAt _ std _ _ _ _ _ _ _ 0) (fun L' v => rfl)
  obtain ⟨-, -, hU, hchi⟩ := J.lev0 (J.chart std 0 (Nat.zero_le _) (c, La))
  have hmem : κ.1 ∈ ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) (c, La))).lev.U := by rw [hU]; exact κ.2
  refine ⟨(A0 J).gamI c γ, ⟨κ.1, hmem⟩, J.one.gamU c γ, ?_, hfr, ra⁻¹, ?_, ?_⟩
  · exact (hJpt _).trans (hκ1.trans (by rw [hJpt]))
  · rw [hchi ⟨κ.1, hmem⟩ κ rfl, map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLatticeTupleMoveByRationalIsometryStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (c : (sysS H X std).Lv.comp 0) (La : ((sysS H X std).Pj 0).Tup) (γ : ((sysS H X std).Lv.lev 0 c).Γ), ((sysS H X std).Pj 0).IsLatTup La → ∃ g κ, MoveBy std J 0 (Nat.zero_le _) c La γ g κ) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_zero | exact GlobalTheory.TwV.Xc.moveBy_zero | (intros; apply GlobalTheory.TwV.Xc.moveBy_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMove
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleMoveScalarPowerOfP
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueArithmeticElementAtSite
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LenSmulTup
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwV.Xc

theorem len_smul_tup : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup), (X.Pj j).IsLatTup L → ∀ v, len X v j ((X.Lv.lev j c).smul γ L) = len X v j L - ordP (X.G.P.W v) p (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det := by
  intro p _ X j c γ L hL v
  exact Formalism.L2.G.Pend.len_smul X j c γ L hL v

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KapGEqCharInf
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_qbar {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (q : TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (algebraMap TaylorLogMetric.Qbar ℂ q) = lam q := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left (show algebraMap TaylorLogMetric.Qbar ℂ q ∈ TaylorLogMetric.Qbar from q.2)]
  rfl

theorem kapG_eq_char_inf : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (a : D.host.E), a * D.host.conj a = 1 → (∀ v, (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det = ρ v a) → letI := wittFractionAlgebraCp p; letI := algKfC E; kapG X ℂ_[p] j c γ = E.iK (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) * TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) * (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
  intro D p _ X E pos lam ρ hLP j c γ a ha hdet
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact zero_ne_one ha
  have hconj : D.host.conj a = a⁻¹ := eq_inv_of_mul_eq_one_right ha

  have hcA : cA X ℂ_[p] j (gamAt X j c γ) =
      TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) := by
    let q : ∀ v : X.Pl, Fin (X.G.P.n' v) → TaylorLogMetric.Qbar := fun v s => ⟨TaylorLogMetric.embT D (pos ⟨v, s⟩) a, embT_mem_qbar D _ a⟩
    have h1 : (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) =
        algebraMap TaylorLogMetric.Qbar ℂ (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), q v s ^ X.w v (j + 1) s) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_zpow₀]
      rfl
    rw [h1, lamC_qbar, map_prod]
    unfold cA
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_zpow₀, hdet v]
    have h2 : lam (q v s) = twG X E v s (ρ v (if IsOddPos s then D.host.conj a else a)) := by
      rw [← hLP v s a, ← lamC_qbar lam (q v s)]
      rfl
    rw [h2, twG_eq_tw]
    by_cases hs : IsOddPos s
    · rw [if_pos hs, if_pos hs, hconj, map_inv₀, map_inv₀, inv_zpow', neg_one_mul]
    · rw [if_neg hs, if_neg hs, one_mul]
  have hP : (∏ v : X.Pl, (p : ℂ_[p]) ^ (-(X.vm v (j + 1) * ordP (X.G.P.W v) p
      (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))) =
      (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
    simp_rw [hdet]
    rw [← Finset.sum_neg_distrib]
    induction (Finset.univ : Finset X.Pl) using Finset.cons_induction with
    | empty => simp
    | cons b s hb ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hp, ih]
  unfold kapG
  rw [hcA, hP]
  rfl

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueArithmeticElementAtSite
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.kapG_at_site : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → FillAt (hT := hT) (H := H) (X := X) std j hj → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) ∈ TaylorLogMetric.Qbar ∧ kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ = TaylorLogMetric.lamC S.lam (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hPos j hj c La γ g κ hr hLat hMove hFill
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  obtain ⟨hgU, -, hfr, r, hr1, hr2⟩ := hMove

  obtain ⟨-, hE⟩ := eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)
  obtain ⟨hEu, hEdet⟩ := hE g hgU
  have ha : g.1.det * D.host.conj g.1.det = 1 := by
    have h1 := congrArg Matrix.det hEu
    rw [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one, hEdet] at h1
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj D]
    exact h1

  have hdet : ∀ v, (gamAt (sysS H X std) j c γ v : Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v)).det = J.rho std v g.1.det := by
    intro v
    have h1 := congrArg Matrix.det (hfr hr v)
    have hm : ((eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g).map (J.rho std v)).det = J.rho std v g.1.det := by
      rw [← hEdet]; exact (RingHom.map_det (J.rho std v) _).symm
    rw [Matrix.det_mul, Matrix.det_mul, hm] at h1
    have hu : IsUnit ((J.fd std).frM j (c, La) v).det := isUnit_det_frameMatrix_ofCharts _ _ _ j (c, La) v
    rw [mul_comm (J.rho std v _)] at h1
    exact hu.mul_left_cancel h1
  have ha0 : g.1.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at ha; exact zero_ne_one ha
  have hT0 : ∀ τ, TaylorLogMetric.embT D τ g.1.det ≠ 0 := fun τ => (map_ne_zero _).2 ha0
  have hkap := kapG_eq_char_inf D (D.what₂.places.resChar w) (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) S.lam (J.rho std) hPos j c γ
    g.1.det ha hdet

  obtain ⟨e, he, hmu⟩ := S.law.mu_rat j hj
  have hdetR : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) = ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [GlobalTheory.TwU.ratA, ratId, Formalism.UG.bc, RingHom.map_det]
  have hmuT : S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) = ∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ := by
    rw [hdetR, hmu _ (by simpa using ha)]
    simp
  have hq1 : (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) ∈ TaylorLogMetric.Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem_qbar D τ _) _
  have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral r).map D.what₂.embLL.toRatAlgHom
  have hχ : S.E.toCEmb.iK (algebraMap (sysS H X std).G.O (sysS H X std).G.Kf ((((sysS H X std).Lv.lev j c).χ γ : (sysS H X std).G.Oˣ) : (sysS H X std).G.O)) =
      TaylorLogMetric.lamC S.lam (D.what₂.embLL r) := by
    rw [hr2, S.hK r hz]
    exact (lamC_qbar S.lam ⟨_, hz⟩).symm

  set A : ℤ := (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) with hA
  set B : ℤ := (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ) with hB
  have hfill := hFill e he
  have hq2 : (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) ∈ TaylorLogMetric.Qbar :=
    zpow_mem (prod_mem fun τ _ => embT_mem_qbar D τ _) _
  have hkey : (∏ v : (sysS H X std).Pl, ∏ s : Fin ((sysS H X std).G.P.n' v), TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) g.1.det ^ (sysS H X std).w v (j + 1) s) =
      (∏ τ, TaylorLogMetric.embT D τ g.1.det ^ e τ) * (∏ τ, TaylorLogMetric.embT D τ g.1.det) ^ (-A - B) := by
    simp_rw [hfill]
    rw [← Fintype.prod_sigma (fun x => TaylorLogMetric.embT D (hT.gat_pos u w hg x) g.1.det ^ (e (hT.gat_pos u w hg x) - A - B))]
    rw [Fintype.prod_equiv (hT.gat_pos u w hg) _ (fun τ => TaylorLogMetric.embT D τ g.1.det ^ (e τ - A - B)) (fun _ => rfl)]
    rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_add₀ (hT0 τ)]
    ring_nf
  have hlen : ∀ v, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La) =
      -((sysS H X std).vm v (j + 1) * ordP ((sysS H X std).G.P.W v) (D.what₂.places.resChar w) (J.rho std v g.1.det)) := by
    intro v
    rw [len_smul_tup _ (sysS H X std) j c γ La hLat v, hdet v]
    ring
  refine ⟨hmuT ▸ hq1, ?_⟩
  rw [hkap, hχ, hkey, hmuT, ← hr1, Finset.sum_congr rfl fun v _ => hlen v, Finset.sum_neg_distrib,
    show -A - B = -(A + B) by ring, mul_assoc (D.what₂.embLL r), Formalism.L2.Ker.lamC_mul S.lam hz (mul_mem hq1 (by rw [show -(A + B) = -A - B by ring]; exact hq2))]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueArithmeticElementAtSiteStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvalue_arithmeticElement_at_site : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → FillAt (hT := hT) (H := H) (X := X) std j hj → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) ∈ TaylorLogMetric.Qbar ∧ kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ = TaylorLogMetric.lamC S.lam (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La))) := by
  first | exact @GlobalTheory.TwV.Xc.kapG_at_site | exact GlobalTheory.TwV.Xc.kapG_at_site | (intros; apply GlobalTheory.TwV.Xc.kapG_at_site <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleMoveScalarPowerOfP
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.Xc.MoveScal

theorem embLL_mem' (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

theorem embT_mem' (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (mul_mem hx hy), Formalism.L2.Ker.lamC_of_mem lam hx, Formalism.L2.Ker.lamC_of_mem lam hy, ← map_mul]
  rfl

theorem lamC_ne' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [Formalism.L2.Ker.lamC_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem scal_core {Mp Mg ML Mk χk P x y : ℂ} (e1 e1' e2 n2 : ℤ) (hMg : Mg ≠ 0) (hMk : Mk ≠ 0) (hχ : χk ≠ 0)
    (hP : P ≠ 0) :
    Mp * (Mg * ML * Mk)⁻¹ * (P⁻¹ * x) ^ (-e1) * y ^ e1' * ((P⁻¹ * x) ^ e2 * y ^ (-n2))⁻¹ * (Mk * χk⁻¹) *
        (χk * Mg * P ^ (-(e1 + e2))) =
      Mp * ML⁻¹ * x ^ (-e1) * y ^ e1' * (x ^ e2 * y ^ (-n2))⁻¹ := by
  rw [mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg, zpow_neg P (e1 + e2), zpow_add₀ hP, zpow_neg P e2]
  have hA : P ^ e1 ≠ 0 := zpow_ne_zero _ hP
  have hB : P ^ e2 ≠ 0 := zpow_ne_zero _ hP
  generalize P ^ e1 = A at hA ⊢
  generalize P ^ e2 = B at hB ⊢
  generalize x ^ (-e1) = X1
  generalize x ^ e2 = X2
  generalize y ^ e1' = Y1
  generalize y ^ (-n2) = Y2
  field_simp

end GlobalTheory.TwV.Xc.MoveScal


open GlobalTheory.TwV.Xc.MoveScal in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.moveBy_scal : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)) = (kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ)⁻¹ * (GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSp hPos hPair j hj c La γ g κ hr hLa hMove La' hLa'
  have hγL : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) :=
    (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLa
  have hjm : j < (sysS H X std).mm := by rw [(GlobalTheory.TwV.DelB.sysS_ranks S).1]; exact hj
  obtain ⟨hA1, -, -, -, hs1, hf1, -, -⟩ := hPair j hjm (c, La) La' hLa hLa'
  have hker := GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hSp j hj c La γ g κ hr hLa hMove
  obtain ⟨hMgA, hkap⟩ := GlobalTheory.T.eigenvalue_arithmeticElement_at_site S hD hSp hPos j hj c La γ g κ hr hLa hMove (GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hSp j hj La'.1)
  obtain ⟨hgU, hpt, -, r, hr_eq, -⟩ := hMove
  have hE := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)).2 g hgU
  have hchi := GlobalTheory.ChiMove.chi_detId_smulLat D t.χ t.χ_ok ⟨_, hA1.2.2.1⟩ _ hE.1
  rw [hE.2] at hchi
  have hD1 := (hD j hj.le (c, La) hLa).2.2.2
  have hD2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hγL).2.2.2
  have hUL : (J.fd std).dt j (c, La) ∈ U1 (sigD D) := hD1 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUk : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) :=
    det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, ((((J.St j hj.le).K _).lev.U_eq κ.1).1 κ.2).1⟩
  have hUγ : (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) ∈ U1 (sigD D) :=
    hD2 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUg : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) ∈ U1 (sigD D) := by
    have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) =
        (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) * (Matrix.GeneralLinearGroup.det κ.1)⁻¹ *
          ((J.fd std).dt j (c, La))⁻¹ := by
      rw [hD2, hD1, hpt, map_mul, map_mul, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem hUγ (inv_mem hUk)) (inv_mem hUL)

  have hmm := S.law.mu_mul j hj
  have hMdt : S.muT (j + 1) ((J.fd std).dt j (c, (((sysS H X std).Lv.lev j c).smul γ La))) = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) *
      S.muT (j + 1) ((J.fd std).dt j (c, La)) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) := by
    rw [hD2, hpt, map_mul, map_mul, ← hD1, hmm.2 _ (mul_mem hUg hUL) _ hUk, hmm.2 _ hUg _ hUL]
  have hMg := S.law.mu_ne hj hUg
  have hMk := S.law.mu_ne hj hUk
  have hχ : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hP : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero _).2 (Units.ne_zero (Matrix.GeneralLinearGroup.det g))
  have hcore : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ := by
    simp only [GlobalTheory.TwU.scal0, Base.chiFac]
    rw [hker, hchi, hMdt]
    exact scal_core _ _ _ _ hMg hMk hχ hP
  have hbQ : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ∈ TaylorLogMetric.Qbar :=
    mul_mem (mul_mem (hr_eq ▸ embLL_mem' D r) hMgA) (zpow_mem (prod_mem fun τ _ => embT_mem' D τ _) _)
  have hb0 : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ≠ 0 := mul_ne_zero (mul_ne_zero hχ hMg) (zpow_ne_zero _ hP)
  have hALQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar := mul_mem hs1 (inv_mem hf1)
  have hAγQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar := by
    rw [← mul_inv_cancel_right₀ hb0 (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)), hcore]
    exact mul_mem hALQ (inv_mem hbQ)
  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' = GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    dsimp only
    ring
  have hq0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) ≠ 0 := zpow_ne_zero _ hp0
  have hl0 := lamC_ne' S.lam hbQ hb0
  rw [hkap, hpp, ← hcore, lamC_mul' S.lam hAγQ hbQ]
  field_simp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleMoveScalarPowerOfPStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTupleMove_scalar_power_of_p : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)) = (kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ)⁻¹ * (GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹))) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_scal | exact GlobalTheory.TwV.Xc.moveBy_scal | (intros; apply GlobalTheory.TwV.Xc.moveBy_scal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmpFamMemFunMod
namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions _root_.Formalism.L2.DIV

namespace CmpMem

theorem isLattice_map {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A : GL (Fin k) K)
    {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by
  obtain ⟨g, hg, rfl⟩ := hL
  refine ⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul hg
  · unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

theorem isLatTup_smul (C : Level P) (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) :=
  fun v => isLattice_map (C.act v γ) (hL v)

variable {X : Fields} (T : PlTie X P) {n : ℕ} (hn : n = P.m + 1) {lam : X.Tau → DomWeight n} {c : ℤ}

variable {S : GSD X.K} (Y : PSys X n p lam S)

end CmpMem

end GlobalTheory.GO
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTuple
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem stdG_one_apply {D : D7} {N : ℕ} (J : Matrix (Fin N) (Fin N) D.host.E) (v : Fin N → D.host.E) :
    stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J 1 v = v := by
  have h : ∀ w : Fin N → D.host.E, toLE (1 : GL (Fin N) D.host.E) w = w := by
    intro w
    simp [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]
  show (stdCo _ J) (toLE 1 ((stdCo _ J).symm v)) = v
  rw [h, LinearEquiv.apply_symm_apply]

theorem inFr_stdG_homRe {D : D7} {a b N N' : ℕ} (hr : a = N) (hr' : b = N') (J : Matrix (Fin N) (Fin N) D.host.E)
    (J' : Matrix (Fin N') (Fin N') D.host.E) (g : GL (Fin N) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    Formalism.L2.Col.inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1) (homRe hr hr' x) =
      homRe hr hr' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) J g)) := by
  subst hr hr'
  apply LinearMap.ext
  intro v
  have h1 : ∀ w, (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1).symm w = w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, stdG_one_apply]
  simp only [Formalism.L2.Col.inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, homRe, eMat]
  congr 2
  ext i
  simp [Matrix.toLin'_apply, LinearMap.toMatrix'_mulVec]

end GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.xiM_smul_moveBy : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLa hM La'
  have hj' : j + 1 ≤ D.R.m := hj
  have hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := (GlobalTheory.TwV.DelB.sysS_ranks S).2.2.1 (j + 1)
  obtain ⟨hg, hpt, -, r, hr0, -⟩ := hM
  have hκU := ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U_eq κ.1).1 κ.2).1

  have hdet : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) := det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, hκU⟩
  refine ⟨?_, fun x => ?_⟩
  · have hmu := S.law.mu_alg j hj _ hdet
    have hchi : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
      rw [← hr0]
      exact (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) r).algHom (D.what₂.embLL.toRatAlgHom))
    exact mul_mem hmu (inv_mem hchi)
  · have e1 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, ((sysS H X std).Lv.lev j c).smul γ La) La' x
    have e2 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, La) La'
      (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))
    have hch := GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c (((sysS H X std).Lv.lev j c).smul γ La) La
      (GlobalTheory.GO.CmpMem.isLatTup_smul _ γ hLa) hLa
    rw [e1, e2, hch]
    have hx0 : (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)).1 * κ.1⁻¹ ∈
        UPts (sigD D) (gramN D j hj.le) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      mul_mem (J.pt std j hj.le _).2 (inv_mem hκU)
    have hlev := S.law.lev j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La')
      (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)) (J.pt std (j + 1) hj' La') κ 1
      (by show _ = _ * _ * _; group) (by simp) (homRe hr hr' x)
    have hrat := S.law.rat j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') (J.pt std j hj.le (c, La))
      (J.pt std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La') g hg 1 (one_mem _)
      (by show _ * _ = _; rw [hpt]; group) (by simp) (homRe hr hr' x)
    rw [inFr_stdG_homRe] at hrat
    rw [hrat] at hlev
    simp only [OneMemClass.coe_one, map_one, (S.law.mu_mul j hj).1, one_mul, Units.val_one, mul_one] at hlev
    have hc : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    linear_combination hlev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTupleStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedDatum_movedLatticeTuple : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  first | exact @GlobalTheory.TwV.Xc.xiM_smul_moveBy | exact GlobalTheory.TwV.Xc.xiM_smul_moveBy | (intros; apply GlobalTheory.TwV.Xc.xiM_smul_moveBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStep
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStep
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.MvS

theorem cast_lev {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) (κ : (S.K β).lev.U) :
    ∃ κ' : (St.K (St.chOf c')).lev.U, κ'.1 = κ.1 ∧ (St.K (St.chOf c')).lev.chi κ' = (S.K β).lev.chi κ := by
  subst hSt hc' h hβ
  exact ⟨κ, rfl, rfl⟩


set_option maxHeartbeats 2000000 in
theorem pt_step {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (β : S.Ch) (hC : S.Core e β) (a : S.cmpt β)
    (γ : ((S.charts.gat β).lev a).Γ) (L : G.P.Tup) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (hg' : ∀ v, ((S.charts.gat β).lev a).smul γ L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hx : (S.loc β).IsPt a g x.1) (hx' : (S.loc β).IsPt a g' x'.1) :
    ∃ κ : (S.K β).lev.U, x'.1 = GlobalTheory.TwU.ratA D.host.F ((S.loc β).gamI a γ) * x.1 * κ.1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((S.K β).lev.chi κ : ℂˣ) : ℂ) ∧
        algebraMap G.O G.Kf ((((S.charts.gat β).lev a).χ γ : G.Oˣ) : G.O) = e r := by
  obtain ⟨κa, hκa⟩ := awayEx_of hC.good (S.K β).lev hC.gam a γ
  obtain ⟨ra, hra1, hra2⟩ := hC.chi a γ κa hκa
  obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.TwV.Xc.isPt_move_eq _ _ _ _ _ _ (S.loc β) _ _ _ _ (S.K β).lev hC.good hC.int hC.hypP hC.actB hC.bad_p a γ
    (hC.gamU a γ) κa hκa g g' (fun v => (hg' v).symm.trans (PStabEq.smul_colSpan (G := S.charts.gat β) a γ L g hg v)) x x' hx hx'
  refine ⟨κ, hκ1, ra⁻¹, ?_, ?_⟩
  · rw [map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc.MvS

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem moveBy_succ : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS i hi c La γ hL
  obtain ⟨⟨β, a⟩, rfl⟩ := (I.at' i hi).st.eC.surjective c
  have hC := H.core i hi β
  have hpt : ∀ L', ((I.at' i hi).st.loc β).IsPt a
      (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) L')
      (J.pt std (i + 1) hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).1 := by
    intro L'
    have h := (Joint.pt_succ_isPt t std J i hi ((I.at' i hi).st.eC ⟨β, a⟩, L')).2
    have key : ∀ (b : Σ β : (I.at' i hi).st.Ch, (I.at' i hi).st.cmpt β), b = ⟨β, a⟩ → ∀ g x, ((I.at' i hi).st.loc b.1).IsPt b.2 g x →
        ((I.at' i hi).st.loc β).IsPt a g x := by
      rintro _ rfl g x h
      exact h
    exact key _ (Equiv.symm_apply_apply _ _) _ _ h
  have hb := Joint.basesAt_span t std J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) hL
  have hb' : ∀ v, (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) =
      colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La)) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
    intro v
    unfold basesAt
    exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj (i + 1)).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v (i + 1) (((sysS H X std).Lv.lev (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩)).smul γ La) = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _))
      ⟨_, PStabEq.smul_colSpan (G := (I.at' i hi).st.charts.gat β) a γ La _ (fun v => hb v) v⟩
  obtain ⟨κ, hκ, r, hr1, hr2⟩ := MvS.pt_step (I.at' i hi).st _ β hC a γ La _ _ (fun v => hb v) (fun v => hb' v) _ _ (hpt La) (hpt _)
  have hc : (I.at' i hi).st.chOf (clsOf (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La) = β :=
    (clsOf_chart (S := (I.at' i hi).st) (H.core i hi) ((I.at' i hi).st.eC ⟨β, a⟩) La hL).trans
      (congrArg Sigma.fst (Equiv.symm_apply_apply (I.at' i hi).st.eC ⟨β, a⟩))
  obtain ⟨κ', hκ'1, hκ'2⟩ := MvS.cast_lev (X.onCh i hi) (I.at' i hi).st (J.St (i + 1) hi) (J.st i hi) _
    (clsAt X H (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩) La) (clsAt_succ X H i hi _ La) β hc κ
  refine ⟨((I.at' i hi).st.loc β).gamI a γ, κ', hC.gamU a γ, ?_, ?_, r, ?_, hr2⟩
  · exact hκ.trans (congrArg _ hκ'1.symm)
  · intro hr v
    have hB : (J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc β).rk.symm) ((I.at' i hi).st.loc β).B := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).B = _
      rw [dite_eq_left hi]
      show Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).rk.symm)
        ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).B = _
      rw [Equiv.symm_apply_apply]
    have hJ : (J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) =
        (gramN D (i + 1) hi).reindex (finCongr ((I.at' i hi).st.loc β).rk.symm) (finCongr ((I.at' i hi).st.loc β).rk.symm) := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).J = _
      rw [dite_eq_left hi]
    have hiw : (J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) = ((I.at' i hi).st.loc β).iw := by
      show (dite (i + 1 ≤ D.R.m) _ _ : PtCh _ _).iw = _
      rw [dite_eq_left hi]
      show ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm ((I.at' i hi).st.eC ⟨β, a⟩)).1).iw = _
      rw [Equiv.symm_apply_apply]
    have hρ : J.rho std v = ((I.at' i hi).st.loc β).iw v := (J.iw i hi β v).symm
    have hF : (J.fd std).frM (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v =
        (((LinearMap.toMatrix' ((stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La))).toLinearMap)) *
          ((J.cp std).B (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La)).1).map ((J.cp std).iw (i + 1) ((I.at' i hi).st.eC ⟨β, a⟩, La) v)).submatrix
          (finCongr rfl) (finCongr rfl) := rfl
    rw [hF, hB, hJ, hiw, hρ]
    exact Mv0.frm_gen (Q := (sysS H X std).G.P.Qq v) _ ((I.at' i hi).st.loc β).rk hr (gramN D (i + 1) hi) ((I.at' i hi).st.loc β).B (((I.at' i hi).st.loc β).gamI a γ)
      (((I.at' i hi).st.loc β).iw v) _ (hC.actB a v γ)
  · exact hr1.trans (congrArg (fun z : ℂˣ => (z : ℂ)) hκ'2.symm)

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteMoveLatticeTupleAtSuccStepStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ i (hi : i + 1 ≤ D.R.m) (c : (sysS H X std).Lv.comp (i + 1)) (La : ((sysS H X std).Pj (i + 1)).Tup) (γ : ((sysS H X std).Lv.lev (i + 1) c).Γ), ((sysS H X std).Pj (i + 1)).IsLatTup La → ∃ g κ, MoveBy std J (i + 1) hi c La γ g κ) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_succ | exact GlobalTheory.TwV.Xc.moveBy_succ | (intros; apply GlobalTheory.TwV.Xc.moveBy_succ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMove
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem site_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  intro j hj c L La' γ hL hLa'
  rw [hmm] at hj
  have hr := hN j
  obtain ⟨g, κ, hM⟩ : ∃ g κ, MoveBy std J j hj.le c L γ g κ := by
    cases j with
    | zero => exact GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry S hD hS c L γ hL
    | succ i => exact GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep S hD hS i hj.le c L γ hL
  have hU := ((GlobalTheory.TwV.Xc.eMat_unitary_det _ _ (fun _ => rfl) _ _ hr _ _ (J.pins.crd_orth j hj.le)).2 g hM.1).1
  obtain ⟨hcq, hxi⟩ := GlobalTheory.T.movedDatum_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM La'
  refine ⟨eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g, _, hU, ?_,
    GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM, hcq, hxi, GlobalTheory.T.latticeTupleMove_scalar_power_of_p S hD hS hPos hPair j hj c L γ g κ hr hL hM La' hLa'⟩
  intro v
  rw [GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hD hS j c (((sysS H X std).Lv.lev j c).smul γ L) L]
  exact hM.2.2.1 hr v

end GlobalTheory.TwV.Xc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMoveStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_arithmeticGroup_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Move) := by
  first | exact @GlobalTheory.TwV.Xc.site_move | exact GlobalTheory.TwV.Xc.site_move | (intros; apply GlobalTheory.TwV.Xc.site_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFrames
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem move_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact GlobalTheory.T.kernelSite_arithmeticGroup_move S hD ⟨J.alg0, J.alg⟩ (pos_at_site S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hD)

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFramesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Move) := by
  first | exact @GlobalTheory.TwV.move_at_site | exact GlobalTheory.TwV.move_at_site | (intros; apply GlobalTheory.TwV.move_at_site <;> assumption)
end
