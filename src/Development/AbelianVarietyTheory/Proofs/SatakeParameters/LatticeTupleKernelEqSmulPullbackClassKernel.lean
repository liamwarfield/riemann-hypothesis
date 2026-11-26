module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissible
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem adm_seam_lat_rd_pair : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) u μ i j c c', TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N j c')) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ i j c c'
  rw [← t.O_lat, ← t.O_lat]
  exact ⟨Formalism.L2.Ker.even_rankN _ _, Formalism.L2.Ker.even_rankN _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat j c').2⟩

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissibleStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedLattices_two_classes_admissible : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) u μ i j c c', TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N j c')) := by
  first | exact @GlobalTheory.TwV.adm_seam_lat_rd_pair | exact GlobalTheory.TwV.adm_seam_lat_rd_pair | (intros; apply GlobalTheory.TwV.adm_seam_lat_rd_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelic
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem homRe_rfl {E : Type} [Field E] {a b : ℕ} (x : Formalism.L2.Col.HomE E a b) : homRe (rfl : a = a) (rfl : b = b) x = x := by
  apply LinearMap.ext
  intro v
  funext i
  simp [homRe]

theorem reV_rfl {D : D7} {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) : reV (rfl : a = a) (rfl : b = b) G = G := by
  funext z
  simp [reV]

theorem inFr_symm_inFr {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a) (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (x : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' x) = x := by
  apply LinearMap.ext
  intro v
  simp [Formalism.L2.Col.inFr]

theorem kerTh_homRe {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E a)} {M' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E b)}
    {L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N)} {L' : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E N')}
    (hM : HEq M L) (hM' : HEq M' L') (Ξ : Formalism.L2.Col.HomE D.host.E N N' → ℂ) :
    kerTh B χ SS c M M' (fun x => Ξ (homRe ha hb x)) = reV ha hb (kerTh B χ SS c L L' Ξ) := by
  subst ha hb
  cases eq_of_heq hM
  cases eq_of_heq hM'
  simp only [homRe_rfl, reV_rfl]


set_option maxHeartbeats 1000000 in
theorem kerTh_pair_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj hr hr' La La' hLa hLa'
  obtain ⟨-, -, h1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨-, -, h2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun x =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe hr hr' x) := by
    funext x
    simp only [xiM, movD, Joint.xi0]
    rw [dite_eq_left ⟨hj, hr, hr'⟩, inFr_symm_inFr]
  rw [hx]
  exact kerTh_homRe _ _ _ _ hr hr' h1 h2 _

end GlobalTheory.TwV.DelB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionLatticeTuplePairEqAdelicStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelFunction_latticeTuple_pair_eq_adelic : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)), ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') = reV hr hr' (kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D j (Nat.le_of_succ_le hj)) J.a (J.pt std j (Nat.le_of_succ_le hj) La).1 ((J.St j (Nat.le_of_succ_le hj)).K (J.chart std j (Nat.le_of_succ_le hj) La)).lev.Lb) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La').1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La')).lev.Lb) (S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La')))) := by
  first | exact @GlobalTheory.TwV.DelB.kerTh_pair_eq | exact GlobalTheory.TwV.DelB.kerTh_pair_eq | (intros; apply GlobalTheory.TwV.DelB.kerTh_pair_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaKernelFunctionAdelicPointsEqPullbackClassKe
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTranspor
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RepsOfEqImage
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRepsImage
namespace GlobalTheory.RepresentativesImage

theorem isReps_image {V W : Type} [AddCommGroup V] [AddCommGroup W] [DecidableEq W] (T : V ≃+ W)
    {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S) (h₁ : ∀ x : V, T x ∈ M₁ ↔ x ∈ Λ₁) (h₂ : ∀ x : V, T x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → W) S) := by
  unfold Formalism.L2.Th1.H.IsReps at hS ⊢
  obtain ⟨hmem, hdist, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact (h₂ v).2 (hmem v hv)
  · intro a ha b hb hab
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
    rw [← map_sub] at hab
    rw [hdist v hv u hu ((h₁ _).1 hab)]
  · intro w hw
    obtain ⟨v, rfl⟩ := T.surjective w
    obtain ⟨u, hu, hvu⟩ := hcov v ((h₂ v).1 hw)
    exact ⟨T u, Finset.mem_image_of_mem _ hu, by rw [← map_sub]; exact (h₁ _).2 hvu⟩

end GlobalTheory.RepresentativesImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RepsOfEqImage
noncomputable section

namespace GlobalTheory.TwU.XiTwo

section Abs

open _root_.Formalism.L2.Ker _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.L2.Th1.H _root_.Formalism.L2.PairingIndexBounds.Mv
open _root_.Formalism.L2.KerInert _root_.Formalism.L2.KerInert.PullbackComparison _root_.Formalism.L2.KerInert.RepComb

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [DecidableEq W]
  (H : Sesq V) (α : V → ℂ) (H₁ : Sesq W) (α₁ : W → ℂ) (T : V ≃+ W)

omit [DecidableEq W] in
theorem brk_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (y t : V) : brk H₁ (T y) (T t) = brk H y t := by
  unfold brk altE
  rw [hH]

theorem hatS_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (vol : ℝ) (SA : Finset V) (Φ : W → ℂ) (x y : V) :
    hatS H₁ vol (SA.image T) (fun s => Φ (s - T x)) (T y) = hatS H vol SA (fun s => Φ (T (s - x))) y := by
  unfold hatS
  rw [Finset.card_image_of_injective _ T.injective, Finset.sum_image (fun a _ b _ h => T.injective h)]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [brk_map H H₁ T hH]
  simp only [map_sub]

omit [DecidableEq W] in
theorem opU_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (x : V) (e : W → ℂ) (z : V) :
    opU H₁ (T x) e (T z) = opU H x (fun v => e (T v)) z := by
  unfold opU
  rw [hH, hH, ← map_add (f := _)]

theorem xiL_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (hα : ∀ x, α₁ (T x) = α x) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : W → ℂ) (z : V) :
    xiL H₁ α₁ vol (SX.image T) (SA.image T) (SB.image T) Φ e (T z) =
      xiL H α vol SX SA SB (fun v => Φ (T v)) (fun v => e (T v)) z := by
  rw [xiL_expand, xiL_expand, Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hatS_map H H₁ T hH, hα, hα, hH, hH, ← map_add (f := _), opU_map H H₁ T hH]


omit [Module ℂ V] [Module ℂ W] in
theorem isReps_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) : IsReps M₁ M₂ (S.image T) := by
  first
  | exact @_root_.GlobalTheory.RepresentativesImage.isReps_image
  | exact _root_.GlobalTheory.RepresentativesImage.isReps_image
  | (apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RepresentativesImage.isReps_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RepresentativesImage.isReps_image ..)


omit [Module ℂ V] [Module ℂ W] in
theorem repsOf_eq_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} (hS : ∃ S, IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) :
    ∃ S : Finset V, IsReps Λ₁ Λ₂ S ∧ repsOf M₁ M₂ = S.image T := by
  classical
  obtain ⟨S, hS⟩ := hS
  have hex : ∃ S₁, IsReps M₁ M₂ S₁ := ⟨_, isReps_image T hS h1 h2⟩
  have hR : IsReps M₁ M₂ (repsOf M₁ M₂) := by
    unfold repsOf
    exact Classical.epsilon_spec hex
  refine ⟨(repsOf M₁ M₂).image T.symm, isReps_image T.symm hR (fun x => ?_) (fun x => ?_), ?_⟩
  · rw [← h1, AddEquiv.apply_symm_apply]
  · rw [← h2, AddEquiv.apply_symm_apply]
  · rw [Finset.image_image]
    have : (T ∘ T.symm : W → W) = id := funext fun x => T.apply_symm_apply x
    rw [this, Finset.image_id]

end Abs

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_two : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  intro V W _ _ _ _ H α H₁ α₁ T hH hα A B Λ A₁ B₁ Λ₁ hyp hΛ hA hB hX hSA hSB vol θ Φ hθ hΦ z
  classical
  have hΛA : ∀ x, T x ∈ Λ₁ ⊓ A₁ ↔ x ∈ Λ ⊓ A := fun x => by
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, hΛ, hA]
  obtain ⟨SX, rX, eX⟩ := repsOf_eq_image T hX hΛ hA
  obtain ⟨SA, rA, eA⟩ := repsOf_eq_image T hSA hB hΛA
  obtain ⟨SB, rB, eB⟩ := repsOf_eq_image T hSB hΛ hB
  rw [eX, eA, eB, xiL_map H α H₁ α₁ T hH hα]
  exact twist_representatives V H α A B Λ hyp _ _ _ _ _ _ (GlobalTheory.TwU.KerMove.repsOf_of_exists hX) (GlobalTheory.TwU.KerMove.repsOf_of_exists hSA)
    (GlobalTheory.TwU.KerMove.repsOf_of_exists hSB) rX rA rB vol _ hθ _ hΦ z

end Main

end GlobalTheory.TwU.XiTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RepsOfEqImageStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xiL_two_alt : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  first | exact @GlobalTheory.TwU.XiTwo.xiL_two | exact GlobalTheory.TwU.XiTwo.xiL_two | (intros; apply GlobalTheory.TwU.XiTwo.xiL_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemPeriodLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemPeriodLatticeIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.SeamPer

section Gen

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E') {a b : ℕ}

def trHom (x : HomE E a b) : HomE E' a b := Matrix.toLin' ((LinearMap.toMatrix' x).map e)

theorem trHom_apply (x : HomE E a b) (w : Sp E' a) :
    trHom e x w = fun l => e (x (fun k => e.symm (w k)) l) := by
  funext l
  have h := RingHom.map_mulVec (e : E →+* E') (LinearMap.toMatrix' x) (fun k => e.symm (w k)) l
  rw [LinearMap.toMatrix'_mulVec] at h
  have h2 : ((e : E →+* E') ∘ fun k => e.symm (w k)) = w := by
    funext k
    simp
  rw [h2] at h
  exact h.symm

theorem trHom_trHom_symm (x : HomE E' a b) : trHom e (trHom e.symm x) = x := by
  refine LinearMap.ext fun w => ?_
  simp [trHom_apply]

theorem trHom_add (x y : HomE E a b) : trHom e (x + y) = trHom e x + trHom e y := by
  refine LinearMap.ext fun w => ?_
  funext l
  simp [trHom_apply]

theorem trHom_smul (r : E) (x : HomE E a b) : trHom e (r • x) = e r • trHom e x := by
  refine LinearMap.ext fun w => ?_
  funext l
  simp [trHom_apply]

theorem trHom_mem {A : Submodule (𝓞 E) E} {A' : Submodule (𝓞 E') E'}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {M : Submodule (𝓞 E') (Sp E' a)} {M' : Submodule (𝓞 E') (Sp E' b)}
    (hA : ∀ r ∈ A, e r ∈ A') (hN : ∀ w ∈ M, (fun k => e.symm (w k)) ∈ N) (hN' : ∀ w ∈ N', (fun k => e (w k)) ∈ M')
    {x : HomE E a b} (hx : x ∈ perO A N N') : trHom e x ∈ perO A' M M' := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    refine Submodule.subset_span ⟨e r, hA r hr, trHom e y, ?_, trHom_smul e r y⟩
    intro w hw
    rw [trHom_apply]
    exact hN' _ (hy _ (hN w hw))
  | zero =>
    have h := trHom_smul e 0 (0 : HomE E a b)
    rw [zero_smul, map_zero, zero_smul] at h
    rw [h]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [trHom_add]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    have h : trHom e (r • y) = RingOfIntegers.mapRingEquiv e r • trHom e y := trHom_smul e (r : E) y
    rw [h]
    exact Submodule.smul_mem _ _ hy

theorem map_mem_of_span {S : Set E} {A' : Submodule (𝓞 E') E'} (h : ∀ r ∈ S, e r ∈ A') :
    ∀ r ∈ Submodule.span (𝓞 E) S, e r ∈ A' := by
  intro r hr
  induction hr using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => rw [map_zero]; exact A'.zero_mem
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact A'.add_mem hy hz
  | smul c y _ hy =>
    have h1 : e (c • y) = RingOfIntegers.mapRingEquiv e c • e y := map_mul e (c : E) y
    rw [h1]
    exact A'.smul_mem _ hy

theorem vec_mem_of_span {S : Set (Sp E a)} {M : Submodule (𝓞 E') (Sp E' a)} (h : ∀ w ∈ S, (fun k => e (w k)) ∈ M) :
    ∀ w ∈ Submodule.span (𝓞 E) S, (fun k => e (w k)) ∈ M := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero =>
    have h1 : (fun k => e ((0 : Sp E a) k)) = 0 := by funext k; simp
    rw [h1]; exact M.zero_mem
  | add y z _ _ hy hz =>
    have h1 : (fun k => e ((y + z) k)) = (fun k => e (y k)) + fun k => e (z k) := by funext k; simp
    rw [h1]; exact M.add_mem hy hz
  | smul c y _ hy =>
    have h1 : (fun k => e ((c • y) k)) = RingOfIntegers.mapRingEquiv e c • fun k => e (y k) := by
      funext k
      exact map_mul e (c : E) (y k)
    rw [h1]
    exact M.smul_mem _ hy

end Gen

theorem symm_mem_of_mem_lat {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    ∀ w ∈ s.lat N, (fun k => s.iE.symm (w k)) ∈ N := by
  refine vec_mem_of_span s.iE.symm ?_
  rintro _ ⟨y, hy, rfl⟩
  simpa using hy

theorem vec_mem_lat {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    ∀ w ∈ N, (fun k => s.iE (w k)) ∈ s.lat N :=
  fun w hw => Submodule.subset_span (Set.mem_image_of_mem (fun x i => s.iE (x i)) hw)

theorem seamHom_mem_perO : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), ∀ x : HomE D.host.E a b, seamHom s x ∈ perO (ambOf s B χ cD).AA N N' ↔ x ∈ perO (aaOf D cc) (s.lat N) (s.lat N') := by
  intro D X s _ cc δ B χ cD a b _ _ N N' x
  constructor
  · intro hx
    rw [← trHom_trHom_symm s.iE x]
    refine trHom_mem s.iE ?_ (symm_mem_of_mem_lat s N) (vec_mem_lat s N') hx
    refine map_mem_of_span s.iE ?_
    rintro _ ⟨c, hc, t, ht, rfl⟩
    exact Submodule.subset_span ⟨c, hc, t, ht, s.iE.apply_symm_apply _⟩
  · intro hx
    refine trHom_mem s.iE.symm ?_ (vec_mem_lat s N) (symm_mem_of_mem_lat s N') hx
    refine map_mem_of_span s.iE.symm ?_
    rintro _ ⟨c, hc, t, ht, rfl⟩
    exact Submodule.subset_span ⟨c, hc, t, ht, rfl⟩

end GlobalTheory.TwV.SeamPer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemPeriodLatticeIffStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostHomToColumnFieldHom_mem_periodLattice_iff : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), ∀ x : HomE D.host.E a b, seamHom s x ∈ perO (ambOf s B χ cD).AA N N' ↔ x ∈ perO (aaOf D cc) (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.TwV.SeamPer.seamHom_mem_perO | exact GlobalTheory.TwV.SeamPer.seamHom_mem_perO | (intros; apply GlobalTheory.TwV.SeamPer.seamHom_mem_perO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeSetExponentTransportFieldIsomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeSetExponentTransportFieldIsomorphism
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.SeamExp

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conjP_seamP {D : D7} {X : Fields} (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    conjPrime₂ (seamP s P) = seamP s (conjPrime₂ P) := by
  ext y
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective y
  rw [mem_conjP, mem_seamP, mem_conjP]
  have h : cO D.host.E (RingOfIntegers.mapRingEquiv s.iE x) = RingOfIntegers.mapRingEquiv s.iE (cO X.E x) := by
    apply RingOfIntegers.ext
    show star (s.iE (x : X.E)) = s.iE (star (x : X.E))
    rw [hs.2, star_eq_conj]
  rw [h, mem_seamP]

theorem expS_seam : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (P : HeightOneSpectrum (𝓞 X.E)), expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (seamP s P) = expS SS P := by
  intro D X s hs SS P
  have hm : ∀ Q, seamP s Q ∈ SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding ↔ Q ∈ SS :=
    fun Q => Finset.mem_map' _
  have h1 := hm P
  have h2 := hm (conjPrime₂ P)
  rw [← conjP_seamP s hs] at h2
  unfold expS
  by_cases hP : P ∈ SS
  · rw [if_pos (h1.2 hP), if_pos hP]
  · rw [if_neg (fun h => hP (h1.1 h)), if_neg hP]
    by_cases hQ : conjPrime₂ P ∈ SS
    · rw [if_pos (h2.2 hQ), if_pos hQ]
    · rw [if_neg (fun h => hQ (h2.1 h)), if_neg hQ]

end GlobalTheory.TwU.SeamExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeSetExponentTransportFieldIsomorphismStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeSetExponent_transport_fieldIsomorphism : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (P : HeightOneSpectrum (𝓞 X.E)), expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (seamP s P) = expS SS P := by
  first | exact @GlobalTheory.TwU.SeamExp.expS_seam | exact GlobalTheory.TwU.SeamExp.expS_seam | (intros; apply GlobalTheory.TwU.SeamExp.expS_seam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemTwistedLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemTwistedLatticeIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeamTwist

theorem seamHom_smul {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : X.E) (x : HomE D.host.E a b) :
    seamHom s (s.iE r • x) = r • seamHom s x := by
  refine LinearMap.ext fun w => funext fun l => s.iE.injective ?_
  rw [seamHom_apply]
  show s.iE r * x (fun k => s.iE (w k)) l = s.iE (r * seamHom s x w l)
  rw [map_mul, seamHom_apply]

theorem seamHom_smul_int {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (r : 𝓞 X.E) (x : HomE D.host.E a b) :
    seamHom s (RingOfIntegers.mapRingEquiv s.iE r • x) = r • seamHom s x :=
  seamHom_smul s (r : X.E) x

theorem seamHom_mem_locP {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b))
    (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)) (h : ∀ x, seamHom s x ∈ M ↔ x ∈ M') (P : HeightOneSpectrum (𝓞 X.E))
    (x : HomE D.host.E a b) :
    seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
  show (∃ r ∈ P.asIdeal.primeCompl, r • seamHom s x ∈ M) ↔ ∃ r ∈ (seamP s P).asIdeal.primeCompl, r • x ∈ M'
  constructor
  · rintro ⟨r, hr, hm⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, fun hh => hr ((mem_seamP s P r).1 hh), (h _).1 ?_⟩
    rwa [seamHom_smul_int]
  · rintro ⟨r, hr, hm⟩
    obtain ⟨r, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective r
    refine ⟨r, fun hh => hr ((mem_seamP s P r).2 hh), ?_⟩
    rw [← seamHom_smul_int]
    exact (h _).2 hm

theorem seamHom_mem_twO : ∀ {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ (cl : ℕ) (e : HeightOneSpectrum (𝓞 X.E) → ℤ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ P, e' (seamP s P) = e P) → ∀ x, seamHom s x ∈ twist₂ M cl e ↔ x ∈ twist₂ M' cl e' := by
  intro D X s a b M M' h cl e e' he x
  have key : ∀ P : HeightOneSpectrum (𝓞 X.E),
      ((cl : X.E) ^ e P)⁻¹ • seamHom s x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔
        ((cl : D.host.E) ^ e' (seamP s P))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal M' := by
    intro P
    rw [← seamHom_smul, seamHom_mem_locP s M M' h, he, map_inv₀, map_zpow₀, map_natCast]
  unfold twist₂
  rw [Submodule.mem_iInf, Submodule.mem_iInf]
  constructor
  · intro hx Q
    obtain ⟨P, rfl⟩ : ∃ P, seamP s P = Q :=
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).surjective Q
    exact (key P).1 (hx P)
  · intro hx P
    exact (key P).2 (hx (seamP s P))

end GlobalTheory.SeamTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostHomToColumnFieldHomMemTwistedLatticeIffStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff : ∀ {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ (cl : ℕ) (e : HeightOneSpectrum (𝓞 X.E) → ℤ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ P, e' (seamP s P) = e P) → ∀ x, seamHom s x ∈ twist₂ M cl e ↔ x ∈ twist₂ M' cl e' := by
  first | exact @GlobalTheory.SeamTwist.seamHom_mem_twO | exact GlobalTheory.SeamTwist.seamHom_mem_twO | (intros; apply GlobalTheory.SeamTwist.seamHom_mem_twO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexCoordinatesColumnFieldIdentification
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexCoordinatesColumnFieldIdentification
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TwU.SeamEmb

open _root_.Formalism.L2.Ker

theorem tau_nonempty' (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

variable {D : D7} {X : Fields} (s : Seam D X)

theorem iE_single {a : ℕ} (j : Fin a) : (fun k => s.iE ((Pi.single j (1 : X.E) : Sp X.E a) k)) = (Pi.single j 1 : Fin a → D.host.E) := by
  funext k
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem seamHom_injective {a b : ℕ} : Function.Injective (seamHom s (a := a) (b := b)) := by
  intro x x' h
  refine LinearMap.ext fun v => funext fun l => ?_
  have e1 := seamHom_apply s x (fun k => s.iE.symm (v k)) l
  have e2 := seamHom_apply s x' (fun k => s.iE.symm (v k)) l
  simp only [RingEquiv.apply_symm_apply] at e1 e2
  rw [← e1, ← e2, h]

theorem seamHom_surjective {a b : ℕ} : Function.Surjective (seamHom s (a := a) (b := b)) := by
  intro y
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' y).map s.iE), ?_⟩
  unfold seamHom
  rw [LinearMap.toMatrix'_toLin']
  have : ((LinearMap.toMatrix' y).map s.iE).map s.iE.symm = LinearMap.toMatrix' y := by
    ext p q; simp
  rw [this, Matrix.toLin'_toMatrix']

theorem embH_seamHom (hs : s.Ok) (δ : ℂ) {a b : ℕ} (x : HomE D.host.E a b) :
    embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ) := by
  funext τ i j
  show δ * X.embC s.σ₀ τ (seamHom s x (Pi.single j 1) i) = δ * TaylorLogMetric.embT D (s.iT τ) (x (Pi.single j 1) i)
  congr 1
  show s.σ₀ (X.emb τ _) = _
  rw [hs.1, seamHom_apply, iE_single]

theorem embH_injective {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι]
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) {a b : ℕ} : Function.Injective (embH emb δ (a := a) (b := b)) := by
  intro x y h
  obtain ⟨τ⟩ := (inferInstance : Nonempty ι)
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (emb τ).injective (mul_left_cancel₀ hδ this)

end GlobalTheory.TwU.SeamEmb

namespace GlobalTheory.TwU.SeamEmb

open _root_.Formalism.L2.Ker

theorem seam_coords : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (δ : ℂ) {a b : ℕ}, Function.Bijective (seamHom s (a := a) (b := b)) ∧ (∀ x : HomE D.host.E a b, embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ)) ∧ (∀ (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ v : VV D.what₂.Tau a b, (fun τ => v (s.iT τ)) ∈ laV (X.embC s.σ₀) δ M ↔ v ∈ laV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ M') ∧ (δ ≠ 0 → ∀ (Ξ : HomE X.E a b → ℂ) (v : VV D.what₂.Tau a b), onV (X.embC s.σ₀) δ Ξ (fun τ => v (s.iT τ)) = onV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) v) := by
  intro D X s hs δ a b
  have hemb := embH_seamHom s hs δ (a := a) (b := b)
  have hcomp : ∀ (x : HomE D.host.E a b) (v : VV D.what₂.Tau a b),
      embH (X.embC s.σ₀) δ (seamHom s x) = (fun τ => v (s.iT τ)) ↔ embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
    intro x v
    rw [hemb]
    constructor
    · intro h
      funext σ
      have := congrFun h (s.iT.symm σ)
      simpa using this
    · intro h; rw [h]
  refine ⟨⟨seamHom_injective s, seamHom_surjective s⟩, hemb, ?_, ?_⟩
  · intro M M' hM v
    constructor
    · rintro ⟨y, hy, hyv⟩
      obtain ⟨x, rfl⟩ := seamHom_surjective s y
      exact ⟨x, (hM x).1 hy, (hcomp x v).1 hyv⟩
    · rintro ⟨x, hx, hxv⟩
      exact ⟨seamHom s x, (hM x).2 hx, (hcomp x v).2 hxv⟩
  · intro hδ Ξ v
    haveI : Nonempty D.what₂.Tau := tau_nonempty' D
    haveI : Nonempty X.Tau := ⟨s.iT.symm (Classical.arbitrary _)⟩
    have hex : (∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ)) ↔ ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := seamHom_surjective s y
        exact ⟨x, (hcomp x v).1 hy⟩
      · rintro ⟨x, hx⟩
        exact ⟨seamHom s x, (hcomp x v).2 hx⟩
    unfold onV
    by_cases h' : ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v
    · have h := hex.2 h'
      rw [dite_eq_left h, dite_eq_left h']
      congr 1
      apply embH_injective (X.embC s.σ₀) hδ
      rw [h.choose_spec, (hcomp _ v).2 h'.choose_spec]
    · have h : ¬ ∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ) := fun h => h' (hex.1 h)
      rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.TwU.SeamEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexCoordinatesColumnFieldIdentificationStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCoordinates_columnFieldIdentification : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (δ : ℂ) {a b : ℕ}, Function.Bijective (seamHom s (a := a) (b := b)) ∧ (∀ x : HomE D.host.E a b, embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ)) ∧ (∀ (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ v : VV D.what₂.Tau a b, (fun τ => v (s.iT τ)) ∈ laV (X.embC s.σ₀) δ M ↔ v ∈ laV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ M') ∧ (δ ≠ 0 → ∀ (Ξ : HomE X.E a b → ℂ) (v : VV D.what₂.Tau a b), onV (X.embC s.σ₀) δ Ξ (fun τ => v (s.iT τ)) = onV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) v) := by
  first | exact @GlobalTheory.TwU.SeamEmb.seam_coords | exact GlobalTheory.TwU.SeamEmb.seam_coords | (intros; apply GlobalTheory.TwU.SeamEmb.seam_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunction
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.SeamKer

open _root_.Formalism.L2.Th1.H

variable {D : D7} {X : Fields}

def seamT (s : Seam D X) (a b : ℕ) : VV D.what₂.Tau a b ≃+ VV X.Tau a b where
  toFun v := fun τ => v (s.iT τ)
  invFun w := fun τ => w (s.iT.symm τ)
  left_inv v := by funext τ; simp
  right_inv w := by funext τ; simp
  map_add' _ _ := rfl

theorem HV_seamT (s : Seam D X) {a b : ℕ} (sc : ℝ) (x y : VV D.what₂.Tau a b) :
    HV sc (seamT s a b x) (seamT s a b y) = HV sc x y := by
  show (sc : ℂ) * (∑ τ, ∑ i, ∑ j, x (s.iT τ) i j * (starRingEnd ℂ) (y (s.iT τ) i j)) =
    (sc : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT (fun τ' => ∑ i, ∑ j, x τ' i j * (starRingEnd ℂ) (y τ' i j))]

theorem alV_seamT (s : Seam D X) {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV D.what₂.Tau a b) :
    alV d sc (seamT s a b x) = alV d sc x := by
  have h := HV_seamT s sc x x
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf, h]

theorem seam_kerTh : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.VecP χ → 0 < cl → (∀ Q ∈ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding), conjPrime₂ Q ∉ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → DatLoc D cc (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) → s.push (thC (X.embC s.σ₀) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (ambOf s B χ cD).AA SS N N' cl Ξ ((ambOf s B χ cD).e a b N N')) = kerTh B χ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) := by
  intro D X s hs cc δ B χ cD a b SS cl N N' Ξ hcc hδ hδ0 hVec hcl hSS hA hDat
  classical
  have hyp := KerMove.split_of_adm _ cl (s.lat N) (s.lat N') B hcc hδ hδ0 hA hcl hSS
  have hI := KerMove.finIdx_of_adm (cc := cc) (δ := δ) (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') hA hcl
  have hθ := KerMove.eNat_fixed (s.lat N) (s.lat N') B χ hcc hδ hVec hA
  have := KerMove.tau_nonempty D
  have hΦ := hDat.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
  have hper := GlobalTheory.T.hostHomToColumnFieldHom_mem_periodLattice_iff s hs B χ cD SS cl N N'
  have hemb := GlobalTheory.T.complexCoordinates_columnFieldIdentification s hs δ (a := a) (b := b)
  have hexp := GlobalTheory.T.primeSetExponent_transport_fieldIsomorphism s hs SS
  have hΛ := hemb.2.2.1 _ _ hper
  have hAh := hemb.2.2.1 _ _ (GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff s _ _ hper cl (fun Q => -expS SS Q)
    (fun Q => -expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) Q)
    (fun P => by simp only [hexp]))
  have hBh := hemb.2.2.1 _ _ (GlobalTheory.T.hostHomToColumnFieldHom_mem_twistedLattice_iff s _ _ hper cl (expS SS)
    (expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) hexp)
  have hdat : onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) = fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v) :=
    funext fun v => (hemb.2.2.2 hδ0 Ξ v).symm
  have hvec : B.eNat χ a b (s.lat N) (s.lat N') = fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v) := by
    funext v
    show B.eNat χ a b (s.lat N) (s.lat N') v = B.eNat χ a b (s.lat N) (s.lat N') (fun τ => v (s.iT (s.iT.symm τ)))
    simp only [Equiv.apply_symm_apply]
  have hθ' : (fun v => (ambOf s B χ cD).e a b N N' (seamT s a b v)) ∈ fixedBy _ _ _ := hvec ▸ hθ
  have hΦ' : InvOn _ _ (fun v => onV (X.embC s.σ₀) δ Ξ (seamT s a b v)) := hdat ▸ hΦ
  funext z
  unfold Seam.push kerTh thC xiV
  rw [hdat, hvec]
  exact GlobalTheory.T.xiL_two_alt _ _ _ _ (seamT s a b) (HV_seamT s _) (alV_seamT s _ _) _ _ _ _ _ _ hyp hΛ hAh hBh
    ⟨_, repsOf_spec _ _ hI.1⟩ ⟨_, repsOf_spec _ _ hI.2.1⟩ ⟨_, repsOf_spec _ _ hI.2.2⟩ 1 _ _ hθ' hΦ' z

end GlobalTheory.TwU.SeamKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldKernelPushforwardEqHostKernelFunctionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (cl : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (Ξ : HomE X.E a b → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.VecP χ → 0 < cl → (∀ Q ∈ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding), conjPrime₂ Q ∉ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)) → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') → DatLoc D cc (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) → s.push (thC (X.embC s.σ₀) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (ambOf s B χ cD).AA SS N N' cl Ξ ((ambOf s B χ cD).e a b N N')) = kerTh B χ (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) cl (s.lat N) (s.lat N') (fun x => Ξ (seamHom s x)) := by
  first | exact @GlobalTheory.TwU.SeamKer.seam_kerTh | exact GlobalTheory.TwU.SeamKer.seam_kerTh | (intros; apply GlobalTheory.TwU.SeamKer.seam_kerTh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTranspor
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem th_eq_kerTh : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie Xi muT hL i hi c c'
  obtain ⟨hδ, -, hV, -⟩ := GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws t
  obtain ⟨hl, hS⟩ := GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair A dtU a hP hTie
  exact GlobalTheory.T.columnFieldKernel_pushforward_eq_hostKernelFunction t.seam t.seam_ok t.B t.χ _ (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')
    ((t.rd u μ).Xi i c c') t.cc_ok t.δ_ok hδ hV hl hS (GlobalTheory.T.transportedLattices_two_classes_admissible t u μ i (i + 1) c c')
    (GlobalTheory.T.finiteDatum_pair_classes_has_level A dtU a hP hTie Xi muT hL i hi c c')

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTransporStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.consecutiveClassesKernel_eq_kernelFunction_transported : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  first | exact @GlobalTheory.TwV.th_eq_kerTh | exact GlobalTheory.TwV.th_eq_kerTh | (intros; apply GlobalTheory.TwV.th_eq_kerTh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaKernelFunctionAdelicPointsEqPullbackClassKe
noncomputable section

namespace GlobalTheory.TwV.SPull

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms _root_.Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_scal {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (vol : ℝ)
    (SX SA SB : Finset V) (k : ℂ) (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB (fun v => k * Φ v) e z = k * xiL H α vol SX SA SB Φ e z := by
  have hS : ∀ x, xiS H α vol SA SB (fun s => k * Φ (s - x)) e = fun w => k * xiS H α vol SA SB (fun s => Φ (s - x)) e w := by
    intro x
    funext w
    unfold xiS Formalism.L2.Th1.H.sumU
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : hatS H vol SA (fun s => k * Φ (s - x)) y = k * hatS H vol SA (fun s => Φ (s - x)) y := by
      unfold hatS
      simp only [mul_assoc, ← Finset.mul_sum]
      ring
    beta_reduce
    rw [this]
    ring
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hS x]
  simp only [Formalism.L2.Th1.H.opU]
  ring

theorem kerTh_scal {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k : ℂ) (z : TaylorLogMetric.VC D a b) :
    kerTh B χ SS cl N N' (fun x => k * Ξ x) z = k * kerTh B χ SS cl N N' Ξ z := by
  have hon : Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ (fun x => k * Ξ x) =
      fun v => k * Formalism.L2.Ker.onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ v := by
    funext v
    unfold Formalism.L2.Ker.onV
    split_ifs <;> simp
  unfold kerTh thC xiV
  rw [hon]
  exact xiL_scal _ _ _ _ _ _ _ _ _ _

theorem kerTh_prop {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ Ξ' : Formalism.L2.Col.HomE D.host.E a b → ℂ) (k k' : ℂ)
    (h : ∀ x, k * Ξ x = k' * Ξ' x) (z : TaylorLogMetric.VC D a b) :
    k * kerTh B χ SS cl N N' Ξ z = k' * kerTh B χ SS cl N N' Ξ' z := by
  rw [← kerTh_scal, ← kerTh_scal, funext h]


set_option maxHeartbeats 1000000 in
theorem kerTh_eq_pull : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.Lb) (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.Lb) (Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x') z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * TaylorLogMetric.pull D t.B.tor (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap) (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) ((t.rd u μ).Th t.seam t.amb i c c') z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' z
  obtain ⟨hδ, hLat, hVec, hEq⟩ := GlobalTheory.T.kernelEntry_period_ne_zero_and_lattice_laws t
  obtain ⟨hl, hSS⟩ := GlobalTheory.T.finiteDatum_level_pos_badPrimes_no_conjugate_pair A dtU a hP hA
  have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hA i (Nat.le_of_succ_le hi) γ hγ
  have hu' := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary A dtU a hP hA (i + 1) hi γ' hγ'
  have hN := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hA i (Nat.le_of_succ_le hi) c x γ hγ κ hx
  have hN' := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice A dtU a hP hA (i + 1) hi c' x' γ' hγ' κ' hx'
  have hd := GlobalTheory.T.adelicDatum_rational_translates_vs_classes A dtU a hP hA Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hu'
  have hc := GlobalTheory.T.finiteDatum_pair_classes_has_level A dtU a hP hA Xi muT law i hi c c'
  have hth := GlobalTheory.T.consecutiveClassesKernel_eq_kernelFunction_transported A dtU a hP hA Xi muT law i hi c c'
  have hmv := GlobalTheory.TwU.KerMove.kerTh_move D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok hδ t.χ_ok hLat hVec hEq (ssRec t u μ) (t.rd u μ).lev hl hSS
    _ _ _ _ _ (GlobalTheory.T.transportedLattices_two_classes_admissible t u μ i (i + 1) c c') hc _ _ hu hu'
  rw [hth, ← hmv, hN, hN']
  exact kerTh_prop _ _ _ _ _ _ _ _ _ _ hd z

end GlobalTheory.TwV.SPull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaKernelFunctionAdelicPointsEqPullbackClassKeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernelFunction_adelicPoints_eq_pullback_classKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.Lb) (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.Lb) (Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x') z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * TaylorLogMetric.pull D t.B.tor (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap) (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) ((t.rd u μ).Th t.seam t.amb i c c') z) := by
  first | exact @GlobalTheory.TwV.SPull.kerTh_eq_pull | exact GlobalTheory.TwV.SPull.kerTh_eq_pull | (intros; apply GlobalTheory.TwV.SPull.kerTh_eq_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernel
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

theorem reV_pull_submatrix {D : D7} (T : TaylorLogMetric.Tor D) {a b N N' : ℕ} (ha : a = N) (hb : b = N')
    (e : Matrix (Fin N) (Fin N) D.host.E) (e' : Matrix (Fin N') (Fin N') D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    reV ha hb (TaylorLogMetric.pull D T e e' G) =
      TaylorLogMetric.pull D T (e.submatrix (Fin.cast ha) (Fin.cast ha)) (e'.submatrix (Fin.cast hb) (Fin.cast hb)) (reV ha hb G) := by
  subst ha hb
  rfl

theorem pullAt_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.PullAt S j) := by
  intro D _ _ _ _ _ _ _ _ u μ w hg Lv I H X _ std t J S hD d j hj La La' hLa hLa' z
  have hj1 : j + 1 ≤ D.R.m := hj
  have hj0 : j ≤ D.R.m := Nat.le_of_succ_le hj1
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  rw [GlobalTheory.T.kernelFunction_latticeTuple_pair_eq_adelic S hD j hj1 (hr j) (hr (j + 1)) La La' hLa hLa']
  have hV := GlobalTheory.T.thetaKernelFunction_adelicPoints_eq_pullback_classKernel J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj1 (clsAt X H j La.1 La.2)
    (clsAt X H (j + 1) La'.1 La'.2) (J.pt std j _ La) (J.pt std (j + 1) hj1 La') (d.gam j _ La) (d.mem j _ La)
    (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap j _ La) (d.kap (j + 1) hj1 La') (d.eq j _ La hLa) (d.eq _ _ La' hLa')
  have hN := (GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj (j + 1) hj1 (clsAt X H (j + 1) La'.1 La'.2)
    (J.pt std (j + 1) hj1 La') (d.gam (j + 1) hj1 La') (d.mem _ _ _) (d.kap (j + 1) hj1 La') (d.eq _ _ La' hLa')).2.2
  have e1 : d.eM j La = (gMat J j hj0 (d.gam j hj0 La)).submatrix (Fin.cast (hr j)) (Fin.cast (hr j)) := by
    unfold Dec.eM; rw [dite_eq_left ⟨hj0, hr j⟩]
  have e2 : d.eM (j + 1) La' = (gMat J (j + 1) hj1 (d.gam (j + 1) hj1 La')).submatrix (Fin.cast (hr (j + 1))) (Fin.cast (hr (j + 1))) := by
    unfold Dec.eM; rw [dite_eq_left ⟨hj1, hr (j + 1)⟩]
  have e3 : thCl (X := sysS H X std) t u μ (clsAt X H) j La La' =
      reV (hr j) (hr (j + 1)) ((t.rd u μ).Th t.seam t.amb j (clsAt X H j La.1 La.2) (clsAt X H (j + 1) La'.1 La'.2)) := by
    unfold thCl; rw [dite_eq_left ⟨hr j, hr (j + 1)⟩]
  have e4 : d.sP S j La La' = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap j hj0 La).1) * d.chi (j + 1) hj1 La' /
      (S.muT (j + 1) (Matrix.GeneralLinearGroup.det (d.kap (j + 1) hj1 La').1) * d.chi j hj0 La) := by
    unfold Dec.sP; rw [dite_eq_left hj1]
  rw [e1, e2, e3, e4, ← reV_pull_submatrix]
  have key : ∀ a b c e k p : ℂ, c ≠ 0 → e ≠ 0 → c * e * k = a * b * p → k = a * b / (c * e) * p := by
    intro a b c e k p hc he h
    field_simp
    linear_combination h
  exact key _ _ _ _ _ _ hN (Units.ne_zero _)
    (hV (fun τ i k => z τ (Fin.cast (hr (j + 1)).symm i) (Fin.cast (hr j).symm k)))

end GlobalTheory.TwV.DelB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleKernelEqSmulPullbackClassKernelStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTupleKernel_eq_smul_pullback_classKernel : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std), ∀ j < D.R.m, d.PullAt S j) := by
  first | exact @GlobalTheory.TwV.DelB.pullAt_of_dict | exact GlobalTheory.TwV.DelB.pullAt_of_dict | (intros; apply GlobalTheory.TwV.DelB.pullAt_of_dict <;> assumption)
end
