module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
public import Lean

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.UnitTensorPairings.ThetaLiftDataOverCoefficientExtension
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.OneMapAll GlobalTheory.AdTh GlobalTheory.Mem.R3.Rw.GeoTies

private theorem lift_pt {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel V S'} (hM : ModelSame M M')
    {Γ W W' : Type} {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'} {iW : InnerProductSpace ℂ W}
    {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW) {H : Links.HMod (Γ → W)} {H' : Links.HMod (Γ → W')}
    (hH : HEq H' H) {θ : H.H →ₗ[ℂ] MMap M} {θ' : H'.H →ₗ[ℂ] MMap M'} (hθ : HEq θ' θ) {v : M.Vec} {v' : M'.Vec} (hv : HEq v' v)
    (pt : AutQ V → AutQ V) (hpt : ∀ q, HEq (pt q) q) :
    ∃ e : H.H ≃ₗ[ℂ] H'.H, ∀ y, HEq (e y) y ∧ ∀ q : AutQ V, θ' (e y) v' q.out = θ y v (pt q).out := by
  obtain ⟨e, he⟩ := exists_equiv_lift hM h1 h2 h3 hH hθ hv
  exact ⟨e, fun y => ⟨(he y).1, fun q => by rw [eq_of_heq (hpt q), (he y).2]⟩⟩

private theorem heq_at {L L' : Type} {P : L → Type} {P' : L' → Type} (v : ∀ s, P s) (v' : ∀ s, P' s) {a b : L} {a' b' : L'}
    (h : a = b) (h' : a' = b') (hv : HEq (v' b') (v b)) : HEq (v' a') (v a) := by
  subst h h'
  exact hv

private theorem same_at {D D' : D7} {V : HSp D} {V' : HSp D'} {L L' : Type} {S : L → D.what₂.Tau → SPar} {S' : L' → D'.what₂.Tau → SPar}
    (M : ∀ s, DSModel V (S s)) (M' : ∀ s, DSModel V' (S' s)) {a b : L} {a' b' : L'}
    (h : a = b) (h' : a' = b') (hv : ModelSame (M b) (M' b')) : ModelSame (M a) (M' a') := by
  subst h h'
  exact hv

private theorem sign_at_base_place_eq_embedding {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL :=
  sgAt_mk _ R.hv0

theorem UpperTheory.theta_lift_data_over_coefficient_extension :
    ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
        (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
        (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
        ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
          (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
          (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
          letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
            (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
            (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
            GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
            ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
            ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
              (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (v₀' i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL)) →
            ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → MWOver z.R.toRealDat R'.toRealDat →
            ∀ (pt : AutQ (Wc (w'.st Z').toD7 i') → AutQ (Wc (w.st Z).toD7 i)), (∀ q, HEq (pt q) q) →
              ∃ e : (z.R.HV i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).H ≃ₗ[ℂ]
                  (R'.HV i' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0).H,
                ∀ y, HEq (e y) y ∧ ∀ q, R'.thF i' _ (e y) (v₀' i' (sg0 (w'.st Z').toD7 _)) q.out =
                  z.R.thF i _ y (z.geo.v₀ i (sg0 (w.st Z).toD7 _)) (pt q).out := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hpins hRS κ' hκ v₀' fw' hcrd hv0 i i' hi hMW
    pt hpt
  letI := alg'
  letI := z.alg
  have hs := sign_at_base_place_eq_embedding z.R.toRealDat
  have hs' := sign_at_base_place_eq_embedding R'.toRealDat
  have hcl := hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  have h2 := hRS.2 i i' hi
  have c1 := hcl.1
  have c2 := hcl.2.2.1
  have c3 := hcl.2.2.2.1
  have hH := h2.2.2.1
  have hθ := h2.2.2.2.1
  have hk := hcl.2.2.2.2.2.2.2
  have hMM := same_at (z.R.MW i) (R'.MW i') hs hs' ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hk.2.2.2.2.2.2.1⟩
  have hv := heq_at (z.geo.v₀ i) (v₀' i') hs hs' (hv0 i i' hi)
  clear hcl h2 hk hs hs' hMW hv0 hcrd hκ hRS hpins hc halg
  have h1 := hE.1
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hii : i = (by with_unfolding_all exact (i' :)) := Fin.ext ((by with_unfolding_all exact (hi :)))
  subst hii
  let i' : Fin (w'.st Z').toD7.R.m := (by with_unfolding_all exact (i :))
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).H :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)).fr_gram :)))
  let H₀ : Links.HMod (Bridge.Gf (Vc (w'.st Z').toD7 i') → (z.R.cV i).W) := (by with_unfolding_all exact ((z.R.HV i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) :))
  let θ₀ : H₀.H →ₗ[ℂ] MMap M₀ := (by with_unfolding_all exact ((z.R.thF i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) :))
  let u₀ : M₀.Vec := (by with_unfolding_all exact ((z.geo.v₀ i (sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) :))
  exact (by with_unfolding_all exact ((lift_pt (M := M₀) (M' := R'.MW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) ((hMM)) (W := (z.R.cV i).W) (W' := (R'.cV i').W)
    (nW := (z.R.cV i).nW) (nW' := (R'.cV i').nW) (iW := (z.R.cV i).iW) (iW' := (R'.cV i').iW) ((c1)) ((c2)) ((c3))
    (H := H₀) (H' := R'.HV i' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0) ((hH)) (θ := θ₀) (θ' := R'.thF i' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0) ((hθ))
    (v := u₀) (v' := v₀' i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) ((hv)) ((pt)) ((hpt))) : _))
end

section -- merged from Development.AutomorphicArithmetic.UnitTensorPairings.CuspSectionsOverCoefficientExtension
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.OneMapAll GlobalTheory.AdTh GlobalTheory.Mem.R3.Rw.GeoTies

private theorem UpperTheory.omega_lowering_action {D : D7} {G : Type} [iG : Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type}
    {tup : Tp → T0} (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F) (h₃ : C.Q.c.F ≤ c.F)
    {G' : Type} [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G' → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La} (hlev : HEq lev O.lev)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) (z' : G') (hz : HEq z' z) {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (q q' : AutQ (Wc D i)) (hq : HEq q q') :
    (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) a' : ℂ) * (cc (O.dict q'.out).1 * (O.mu q'.out * rdU (unfBC h₃ (C.U ((i : ℕ) + 1)) (inC c))
      (actLev c (fun g => (lev g, LinearMap.id)) z' (GlobalTheory.FieldBC.rulBC hle f)) (O.dict q'.out).1 (O.dict q'.out).2)) =
      (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * adOver O cc (actLev O.c' O.lev2 z f) q.out := by
  subst hG ha
  cases hi; cases hz; cases hq
  exact congrArg _ (adOver_rulBC O hact c hle h₃ (eq_of_heq hlev) cc _ hf _)

open Classical in
private theorem UpperTheory.weight_function_eq {D : D7} {j : ℕ} (b : WeightFamilies.Wt D j) (aP : type_of% b.aP) (aM : type_of% b.aM) (hP : HEq aP b.aP)
    (hM : HEq aM b.aM) :
    (fun x : (D.host.E →+* ℂ) × ℕ => ∑ t : D.what₂.Tau, ((if x.1 = DV.tauEmb D t then ext0 (aP t) x.2 else 0) +
      if x.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t) then ext0 (aM t) x.2 else 0)) = wtA b := by
  cases hP; cases hM; rfl

private theorem UpperTheory.base_change_mem_section {D : D7} {C : Formalism.L2.Pj.Core D} {j : ℕ} {c c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l} (hle : c.F ≤ c'.F)
    {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n : ℕ} {f : Rul (C.Q.Xo j) c} (hf : f ∈ sec (C.Q.Xo j) c a n) :
    GlobalTheory.FieldBC.rulBC hle f ∈ sec (C.Q.Xo j) c' a' n := ha ▸ GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf

theorem UpperTheory.cusp_sections_over_coefficient_extension :
    ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
        (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
        (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
        ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
          (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
          (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
          letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
            (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
            (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
            GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
            ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
            ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
            ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev →
              ∀ (φ : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (φ g) g) →
            ∀ (pt : AutQ (Wc (w'.st Z').toD7 i') → AutQ (Wc (w.st Z).toD7 i)), (∀ q, HEq (pt q) q) →
                ∀ (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff z.core.Q.l) (hle : (z.geo.O i).c'.F ≤ c.F), HEq (O' i').c' c →
                  ∀ f ∈ sec (z.core.Q.Xo ((i : ℕ) + 1)) (z.geo.O i).c' (wtA (z.geo.κ i)) (Vc (w.st Z).toD7 i).rank,
                    ∃ f' ∈ sec (core'.Q.Xo ((i' : ℕ) + 1)) (O' i').c' (wtA (κ' i')) (Vc (w'.st Z').toD7 i').rank,
                      HEq f' (GlobalTheory.FieldBC.rulBC hle f) ∧ ∀ g q,
                      (lieFac (core'.Q.Dw ((i' : ℕ) + 1)) (xiR (w'.st Z').toD7) (wtA (κ' i')) : ℂ) *
                        adOver (O' i') (core'.cE ((i' : ℕ) + 1) (O' i').s0) (actLev (O' i').c' (O' i').lev2 (φ g) f') q.out =
                      (lieFac (z.core.Q.Dw ((i : ℕ) + 1)) (xiR (w.st Z).toD7) (wtA (z.geo.κ i)) : ℂ) *
                        adOver (z.geo.O i) (z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0) (actLev (z.geo.O i).c' (z.geo.O i).lev2 g f)
                          (pt q).out := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg' hcore Xg tr R' cG' hP hRS κ' hκ O' i i' hii hlev φ hφ pt hpt c hle hcc f₀ hf₀
  have hk := hκ i i' hii
  have a1 := hk.1
  have a2 := hk.2.1
  have a3 := hk.2.2
  clear hk hκ
  obtain ⟨h1, -, -, -⟩ := hE
  clear hP hRS halg'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hG : Gc _ w'.px = Gc B w.px := by rw [hpx']; rfl
  have hi : HEq (inferInstance : Group (Gc _ w'.px)) (inferInstance : Group (Gc B w.px)) := by rw [hpx']; exact HEq.rfl
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  obtain ⟨hH, hl, hc, hDw, hXo, hU, hV, hdict, hmu, -, hcE, -, -, -⟩ := hcore
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((z.core.Q.H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((z.core.Q.H))) (((hH)))).symm : _))
  clear (hH)
  subst e))
  ( (
  have e : @Eq (type_of% (l')) ((by with_unfolding_all exact ((z.core.Q.l) :))) (l') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (l')) (l') (((z.core.Q.l))) (((hl)))).symm : _))
  clear (hl)
  subst e))
  ( (
  have e : @Eq (type_of% (c')) ((by with_unfolding_all exact ((z.core.Q.c) :))) (c') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (c')) (c') (((z.core.Q.c))) (((hc)))).symm : _))
  clear (hc)
  subst e))
  ( (
  have e : @Eq (type_of% (Dw')) ((by with_unfolding_all exact ((z.core.Q.Dw) :))) (Dw') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Dw')) (Dw') (((z.core.Q.Dw))) (((hDw)))).symm : _))
  clear (hDw)
  subst e))
  ( (
  have e : @Eq (type_of% (Xo')) ((by with_unfolding_all exact ((z.core.Q.Xo) :))) (Xo') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Xo')) (Xo') (((z.core.Q.Xo))) (((hXo)))).symm : _))
  clear (hXo)
  subst e))
  ( (
  have e : @Eq (type_of% (U')) ((by with_unfolding_all exact ((z.core.U) :))) (U') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (U')) (U') (((z.core.U))) (((hU)))).symm : _))
  clear (hU)
  subst e))
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((z.core.V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((z.core.V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  ( (
  have e : @Eq (type_of% (dict')) ((by with_unfolding_all exact ((z.core.dict) :))) (dict') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (dict')) (dict') (((z.core.dict))) (((hdict)))).symm : _))
  clear (hdict)
  subst e))
  ( (
  have e : @Eq (type_of% (mu')) ((by with_unfolding_all exact ((z.core.mu) :))) (mu') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (mu')) (mu') (((z.core.mu))) (((hmu)))).symm : _))
  clear (hmu)
  subst e))
  ( (
  have e : @Eq (type_of% (cE')) ((by with_unfolding_all exact ((z.core.cE) :))) (cE') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (cE')) (cE') (((z.core.cE))) (((hcE)))).symm : _))
  clear (hcE)
  subst e))
  have ei : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((@Fin.ext (w'.st Z').toD7.R.m ((i)) i' ((hii))) : _))
  subst ei
  have ha : @Eq (type_of% (wtA (z.geo.κ i))) ((by with_unfolding_all exact ((wtA (κ' ((i)))) : _))) (wtA (z.geo.κ i)) := (by with_unfolding_all exact ((UpperTheory.weight_function_eq (z.geo.κ i) ((by with_unfolding_all exact ((κ' ((i))).aP : _))) ((by with_unfolding_all exact ((κ' ((i))).aM : _))) ((by with_unfolding_all exact (a1 :))) ((by with_unfolding_all exact (a2 :)))) :))
  letI := z.alg
  have hm := UpperTheory.base_change_mem_section (C := z.core.toCore) hle ha hf₀
  have key := fun (g : Gc B w.px) (q : AutQ (Wc (w'.st Z').toD7 ((by with_unfolding_all exact (i :))))) =>
    UpperTheory.omega_lowering_action (z.geo.O i) (z.geo.pins i).2.act.1 c hle (le_trans (z.geo.O i).hle hle) hG hi (lev := (by with_unfolding_all exact ((O' ((i))).lev : _)))
      ((by with_unfolding_all exact (hlev :))) (z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0) g ((by with_unfolding_all exact ((φ g) :))) ((by with_unfolding_all exact ((hφ g) :))) ha hf₀ ((by with_unfolding_all exact ((pt ((q))) : _))) ((by with_unfolding_all exact (q :))) ((by with_unfolding_all exact ((hpt ((q))) : _)))
  have hr : HEq (GlobalTheory.FieldBC.rulBC hle f₀) (GlobalTheory.FieldBC.rulBC hle f₀) := HEq.rfl
  let F1 := GlobalTheory.FieldBC.rulBC hle f₀
  ( (
  have e : @Eq (type_of% (c)) ((by with_unfolding_all exact (((O' ((by with_unfolding_all exact (i :)))).c') :))) (c) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (c)) ((((O' ((by with_unfolding_all exact (i :)))).c'))) (c) (((hcc)))) : _))
  clear (hcc)
  subst e))
  exact ⟨(by with_unfolding_all exact (F1 :)), (by with_unfolding_all exact (hm :)), (by with_unfolding_all exact (hr :)), (by with_unfolding_all exact (key :))⟩
end

section -- merged from Development.AutomorphicArithmetic.UnitTensorPairings.GeometricActionOverCoefficientExtension
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

noncomputable section
namespace UpperTheory.RhoMove

private def RhoP {Rl L G : Type} [Field L] {n : ℕ} (P : Rl → Prop) (act : G → Rl → Rl) (e : Subtype P → Fin n → L)
    (ρ : G → (Fin n → L) →ₗ[L] (Fin n → L)) : Prop :=
  ((∀ g f, P f → P (act g f)) → ∀ g (f : Subtype P), ∃ hf : P (act g f.1), e ⟨act g f.1, hf⟩ = ρ g (e f)) ∧
    (¬ (∀ g f, P f → P (act g f)) → ∀ g, ρ g = 1)

private theorem rhoP_move {Rl L L' G : Type} [Field L] [Field L'] {n : ℕ} (P : Rl → Prop) (act : G → Rl → Rl)
    (e : Subtype P → Fin n → L) (e' : Subtype P → Fin n → L')
    (ρ : G → (Fin n → L) →ₗ[L] (Fin n → L)) (ρ' : G → (Fin n → L') →ₗ[L'] (Fin n → L')) (ι : L →+* L')
    (he : ∀ φ k, e' φ k = ι (e φ k))
    (hρ : ∀ g x x', CrdOver ι x x' → CrdOver ι (ρ g x) (ρ' g x'))
    (h : RhoP P act e ρ) : RhoP P act e' ρ' := by
  have hc : ∀ (x : Fin n → L) (x' : Fin n → L'), (∀ k, x' k = ι (x k)) → CrdOver ι x x' := fun x x' hx =>
    ⟨rfl, fun k k' hk => by obtain rfl : k = k' := Fin.ext hk; exact hx k⟩
  refine ⟨fun hk g f => ?_, fun hk g => ?_⟩
  · obtain ⟨hf, h2⟩ := h.1 hk g f
    refine ⟨hf, funext fun k => ?_⟩
    rw [he, h2]
    exact ((hρ g _ _ (hc _ _ (he f))).2 k k rfl).symm
  · have h1 := h.2 hk g
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    funext k
    have h3 := (hρ g (Pi.single j 1) (Pi.single j 1) (hc _ _ fun k => by
      by_cases hjk : k = j
      · subst hjk; simp
      · simp [Pi.single_eq_of_ne hjk])).2 k k rfl
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Module.End.one_apply]
    rw [h3, h1, Module.End.one_apply]
    by_cases hjk : k = j
    · subst hjk; simp
    · simp [Pi.single_eq_of_ne hjk]

private theorem rhoP_core {D : D7} (T : CoreJ D) (i : Fin D.R.m)
    {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {m m' : ℕ} (hm : m' = m)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {L L' : Type} [Field L] [Field L'] {n n' : ℕ} (hn : n = n')
    (e : T.cuspA ((i : ℕ) + 1) a m → Fin n → L) (e' : T.cuspA ((i : ℕ) + 1) a' m' → Fin n' → L')
    (ρ : G → (Fin n → L) →ₗ[L] (Fin n → L)) (ρ' : G' → (Fin n' → L') →ₗ[L'] (Fin n' → L')) (ι : L →+* L')
    (emb : L →+* ℂ) (emb' : L' →+* ℂ) (hι : ∀ x, emb' (ι x) = emb x)
    (he : ∀ φ φ', HEq φ' φ → ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → emb' (e' φ' k') = emb (e φ k))
    (hρ : ∀ g' g, HEq g' g → ∀ x x', CrdOver ι x x' → CrdOver ι (ρ g x) (ρ' g' x'))
    (h : RhoP (fun f => f ∈ T.cuspA ((i : ℕ) + 1) a m) (fun g f => actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) e ρ) :
    RhoP (fun f => f ∈ T.cuspA ((i : ℕ) + 1) a' m') (fun g f => actLev T.Q.c (fun g => (lev' g, LinearMap.id)) g f) e' ρ' := by
  subst ha hm hG hn
  cases hi; cases hl
  exact rhoP_move _ _ e e' ρ ρ' ι (fun φ k => emb'.injective ((he φ φ HEq.rfl k k rfl).trans (hι _).symm))
    (fun g => hρ g g HEq.rfl) h

private theorem rhoGeo_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    RhoGeo fw O ↔ ∀ i : Fin D.R.m, RhoP (fun f => f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n)
      (fun g f => actLev T.Q.c (fun g => ((O i).lev g, LinearMap.id)) g f)
      (fun φ => ((fw.e i φ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) (fun g => (R.FW i).ρ g) := Iff.rfl

end UpperTheory.RhoMove
end

open UpperTheory.RhoMove in
theorem UpperTheory.geometric_action_over_coefficient_extension :
    ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
        (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
        (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
        ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
          (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
          (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
          letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
            (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
            (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
            GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
            ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
            ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
              (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
            ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev) →
            RhoGeo fw' O' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg' hcore Xg tr R' cG' hP hRS κ' hκ v₀' fw' hcrd O' hO
  obtain ⟨h1, -, -, hR⟩ := hE
  have hι := enlEmb_spec hR
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hG : Gc _ w'.px = Gc B w.px := by rw [hpx']; rfl
  have hi : HEq (inferInstance : Group (Gc _ w'.px)) (inferInstance : Group (Gc B w.px)) := by rw [hpx']; exact HEq.rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hI, -⟩ := hRS.1
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  obtain ⟨hH, hl, hc, hDw, hXo, hU, -, -, -, -, -, -, -, -⟩ := hcore
  obtain rfl : H' = z.core.Q.H := eq_of_heq hH
  obtain rfl : l' = z.core.Q.l := eq_of_heq hl
  obtain rfl : c' = z.core.Q.c := eq_of_heq hc
  obtain rfl : Dw' = z.core.Q.Dw := eq_of_heq hDw
  obtain rfl : Xo' = z.core.Q.Xo := eq_of_heq hXo
  obtain rfl : U' = z.core.U := eq_of_heq hU
  refine (rhoGeo_iff fw' O').2 fun i => ?_
  have hk := hκ i i rfl
  have a1 := hk.1
  have a2 := hk.2.1
  have a3 := hk.2.2
  have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
    have e1 := eq_of_heq a1
    have e2 := eq_of_heq a2
    unfold wtA
    rw [e1, e2]
    rfl
  have hιc := (hI i i rfl).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (enlEmb hR) hι
  have hρ := hιc.2.2.2.1
  have hW := hιc.2.1.2
  have hn : z.R.nW i = R'.nW i := (hW 0 (Submodule.zero_mem _)).elim fun _ h => h.1
  have hz := (@rhoGeo_iff _ _ _ _ _ _ _ _ z.alg _ _ _ z.geo.fw z.geo.O).1 z.geo.rhoGeo i
  have key := rhoP_core z.core i ha a3 hG hi (hO i i rfl) hn _
    ((by with_unfolding_all exact ((fun φ => ((fw'.e i φ : (R'.FW i).WK) : Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL)) :))) _ (fun g => (R'.FW i).ρ g) (enlEmb hR)
    (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL hι ((by with_unfolding_all exact ((hcrd i i rfl) :))) hρ hz
  exact (by with_unfolding_all exact (key :))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivAllEnl
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
set_option maxHeartbeats 4000000

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EqvMove

open _root_.Formalism.L2.DIV

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)

abbrev datW (Pg : Finset (Pl D.host.E)) : LevDat D.host.E ℂ (Wc D i).rank :=
  datY _ D.R.r D.R.t 0 (r_le_rank_Wc i) Pg ∅ (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1) Frm.B

def EqAtP (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {G : Type} [Group G] (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (β : GL (Fin (Wc D i).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) (eG : G → G0 Pg D.R.r) (X : G → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) β (datW i Pg) (eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n,
      actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
      ∃ y : T.Q.c.F, (y : ℂ) = X g ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) h = σ y * phiAt T i σ hV c f (h * k)

def EquivP (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {G : Type} [Group G] (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)
    (β : GL (Fin (Wc D i).rank) (EAf D)) (Pg : Finset (Pl D.host.E)) (eG : G → G0 Pg D.R.r) (X : G → ℂ) : Prop :=
  ∀ g k, Lev.IsLevelLift (Wc D i) β (datW i Pg) (eG g) k →
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n,
      actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
        ∀ h, phiAt T i σ hV c (actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) h = X g * phiAt T i σ hV c f (h * k)

section Gen

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m) (κi : WeightFamilies.Wt D ((i : ℕ) + 1))

theorem phi_eq_phiAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : O.phi cc f = phiAt T i O.s0 O.hV cc f := by
  have key : ∀ (σ : T.Q.c.F →+* ℂ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ),
      adel W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (castDict hV (T.mu ((i : ℕ) + 1) σ)) c) (rdU (T.U ((i : ℕ) + 1) σ) f) =
      castDict hV (adel (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ)
        (muPin (T.V ((i : ℕ) + 1) σ) (T.dict ((i : ℕ) + 1) σ) (T.mu ((i : ℕ) + 1) σ) c) (rdU (T.U ((i : ℕ) + 1) σ) f)) := by
    intro σ W hV c
    subst hV
    rfl
  exact key O.s0 _ O.hV cc

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

theorem eqAt_iff (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ)
    (halg : ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = (y : ℂ)) (hχ : R.grp_chiW) :
    EqAt T R κ O σ hV c ↔ EqAtP T i σ hV c (wtA (κ i)) (κ i).n O.lev (R.βW i) R.Pg (fun g => R.eG g)
      (fun g => D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) := by
  constructor
  · intro h g k hk f hf
    obtain ⟨h1, y, hy, h2⟩ := h g k hk f hf
    exact ⟨h1, y, (halg y).symm.trans (hy.trans (hχ i g).symm), h2⟩
  · intro h g k hk f hf
    obtain ⟨h1, y, hy, h2⟩ := h g k hk f hf
    exact ⟨h1, y, (halg y).trans (hy.trans (hχ i g)), h2⟩

theorem equivAt_iff {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ)
    (hχ : R.grp_chiW) :
    O.EquivAt κi cc ↔ EquivP T i O.s0 O.hV cc (wtA κi) κi.n O.lev (R.βW i) R.Pg (fun g => R.eG g)
      (fun g => D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) := by
  constructor
  · intro h g k hk f hf
    obtain ⟨h1, h2⟩ := h g k hk f hf
    refine ⟨h1, fun x => ?_⟩
    have := h2 x
    rw [phi_eq_phiAt, phi_eq_phiAt] at this
    rw [this, ← hχ i g]
  · intro h g k hk f hf
    obtain ⟨h1, h2⟩ := h g k hk f hf
    refine ⟨h1, fun x => ?_⟩
    rw [phi_eq_phiAt, phi_eq_phiAt, h2 x, ← hχ i g]

end Gen

section Congr

variable {D : D7} (T : CoreJ D) (i : Fin D.R.m)

theorem eqAtP_congr {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ' = σ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (hV' : T.V ((i : ℕ) + 1) σ' = Wc D i)
    {c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ} {c' : (T.U ((i : ℕ) + 1) σ').Comp → ℂ} (hc : HEq c' c)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {β β' : GL (Fin (Wc D i).rank) (EAf D)} (hβ : β' = β) {Pg Pg' : Finset (Pl D.host.E)} (hP : Pg' = Pg)
    {eG : G → G0 Pg D.R.r} {eG' : G' → G0 Pg' D.R.r} (he : HEq eG' eG) {X : G → ℂ} {X' : G' → ℂ} (hX : HEq X' X) :
    EqAtP T i σ' hV' c' a' n' lev' β' Pg' eG' X' ↔ EqAtP T i σ hV c a n lev β Pg eG X := by
  subst ha hn hσ hG hβ hP
  cases hi; cases hc; cases hl; cases he; cases hX
  rfl

theorem equivP_congr {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ' = σ)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (hV' : T.V ((i : ℕ) + 1) σ' = Wc D i)
    {c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ} {c' : (T.U ((i : ℕ) + 1) σ').Comp → ℂ} (hc : HEq c' c)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {β β' : GL (Fin (Wc D i).rank) (EAf D)} (hβ : β' = β) {Pg Pg' : Finset (Pl D.host.E)} (hP : Pg' = Pg)
    {eG : G → G0 Pg D.R.r} {eG' : G' → G0 Pg' D.R.r} (he : HEq eG' eG) {X : G → ℂ} {X' : G' → ℂ} (hX : HEq X' X) :
    EquivP T i σ' hV' c' a' n' lev' β' Pg' eG' X' ↔ EquivP T i σ hV c a n lev β Pg eG X := by
  subst ha hn hσ hG hβ hP
  cases hi; cases hc; cases hl; cases he; cases hX
  rfl

end Congr

theorem heq_fun_of {G G' : Type} {Y : Type} (hG : G' = G) (X : G → Y) (X' : G' → Y)
    (h : ∀ g' g, HEq g' g → X' g' = X g) : HEq X' X := by
  subst hG
  exact heq_of_eq (funext fun g => h g g HEq.rfl)

theorem heq_coe_eG {E : Type} [Field E] [NumberField E] {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G)
    (hi : HEq iG' iG) {Pg Pg' : Finset (Pl E)} {r : ℕ} (hP : Pg' = Pg) (e : G ≃* G0 Pg r) (e' : G' ≃* G0 Pg' r)
    (h : HEq e' e) : HEq (fun g => e' g) (fun g => e g) := by
  subst hG hP
  cases hi
  cases h
  rfl

theorem equivAll_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev) →
        EquivAll core' R'.toRealDat κ' O' ∧ ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          (z.geo.O i).EquivAt (z.geo.κ i) (z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0) →
          (O' i').EquivAt (κ' i') (core'.cE ((i' : ℕ) + 1) (O' i').s0) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg' hcore Xg tr R' cG' hP hRS κ' hκ O' hO
  obtain ⟨h1, -, -, hR⟩ := hE
  have hι := enlEmb_spec hR
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hG : Gc _ w'.px = Gc B w.px := by rw [hpx']; rfl
  have hi : HEq (inferInstance : Group (Gc _ w'.px)) (inferInstance : Group (Gc B w.px)) := by rw [hpx']; exact HEq.rfl
  have hχ' : R'.toRealDat.grp_chiW := hP.char.base.grp.chiW
  have hχ : z.R.toRealDat.grp_chiW := z.pins.char.base.grp.chiW
  obtain ⟨-, -, hβW, -, -, -, -, -, -, hPg, heG, -, hI, -⟩ := hRS.1
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  obtain ⟨hH, hl, hc, hDw, hXo, hU, hV, hdict, hmu, -, hcE, -, -, -⟩ := hcore
  obtain rfl : H' = z.core.Q.H := eq_of_heq hH
  obtain rfl : l' = z.core.Q.l := eq_of_heq hl
  obtain rfl : c' = z.core.Q.c := eq_of_heq hc
  obtain rfl : Dw' = z.core.Q.Dw := eq_of_heq hDw
  obtain rfl : Xo' = z.core.Q.Xo := eq_of_heq hXo
  obtain rfl : U' = z.core.U := eq_of_heq hU
  obtain rfl : V' = z.core.V := eq_of_heq hV
  obtain rfl : dict' = z.core.dict := eq_of_heq hdict
  obtain rfl : mu' = z.core.mu := eq_of_heq hmu
  obtain rfl : cE' = z.core.cE := eq_of_heq hcE

  refine ⟨fun i σ hg hV' hex => ?_, fun i i' hii hE => ?_⟩
  · obtain ⟨c₁, hcu, hq⟩ := hex
    have hA' := (eqAt_iff _ i R'.toRealDat κ' (O' i) σ hV' c₁ halg' hχ').1 hq
    obtain ⟨a1, a2, a3⟩ := hκ i i rfl
    have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
      have e1 := eq_of_heq a1
      have e2 := eq_of_heq a2
      unfold wtA
      rw [e1, e2]
      rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hιc⟩ := hI i i rfl
    obtain ⟨-, -, hchi, -⟩ := hιc (enlEmb hR) hι
    have hX : HEq (fun g => (w'.st Z').toD7.what₂.embLL (((R'.FW i).chi g : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL))
        (fun g => (w.st Z).toD7.what₂.embLL (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) :=
      heq_fun_of hG _ _ fun g' g hgg => by rw [hchi g' g hgg]; exact hι _
    have he := heq_coe_eG hG hi (eq_of_heq hPg) z.R.eG R'.eG heG
    have hβ : R'.βW i = z.R.βW i := congrFun (eq_of_heq hβW) i
    have key := eqAtP_congr z.core i ha a3 (σ := σ) (σ' := σ) rfl hV' hV' (c := c₁) (c' := c₁) HEq.rfl hG hi (hO i i rfl) hβ
      (eq_of_heq hPg) he hX
    have hA := key.1 ((hA'))
    have hz := z.geo.equivAll i σ hg hV' ⟨c₁, hcu, (eqAt_iff z.core i z.R.toRealDat z.geo.κ (z.geo.O i) σ hV' c₁ z.alg_eq hχ).2 hA⟩
    have hB := (eqAt_iff z.core i z.R.toRealDat z.geo.κ (z.geo.O i) σ hV' _ z.alg_eq hχ).1 hz
    have key2 := eqAtP_congr z.core i ha a3 (σ := σ) (σ' := σ) rfl hV' hV' (c := z.core.cE ((i : ℕ) + 1) σ)
      (c' := z.core.cE ((i : ℕ) + 1) σ) HEq.rfl hG hi (hO i i rfl) hβ (eq_of_heq hPg) he hX
    exact (eqAt_iff _ i R'.toRealDat κ' (O' i) σ hV' _ halg' hχ').2 ((key2.mpr hB))

  · obtain rfl : i = i' := Fin.ext hii
    obtain ⟨a1, a2, a3⟩ := hκ i i rfl
    have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
      have e1 := eq_of_heq a1
      have e2 := eq_of_heq a2
      unfold wtA
      rw [e1, e2]
      rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hιc⟩ := hI i i rfl
    obtain ⟨-, -, hchi, -⟩ := hιc (enlEmb hR) hι
    have hX : HEq (fun g => (w'.st Z').toD7.what₂.embLL (((R'.FW i).chi g : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL))
        (fun g => (w.st Z).toD7.what₂.embLL (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) :=
      heq_fun_of hG _ _ fun g' g hgg => by rw [hchi g' g hgg]; exact hι _
    have he := heq_coe_eG hG hi (eq_of_heq hPg) z.R.eG R'.eG heG
    have hβ : R'.βW i = z.R.βW i := congrFun (eq_of_heq hβW) i
    have hB := (equivAt_iff z.core i (z.geo.κ i) z.R.toRealDat (z.geo.O i) _ hχ).1 hE
    have hσ : (O' i).s0 = (z.geo.O i).s0 := (sOv_eq _ _ _).trans (sOv_eq _ _ _).symm
    have key := equivP_congr z.core i ha a3 hσ (z.geo.O i).hV (O' i).hV (c := z.core.cE ((i : ℕ) + 1) (z.geo.O i).s0)
      (c' := z.core.cE ((i : ℕ) + 1) (O' i).s0) (by rw [hσ]) hG hi (hO i i rfl) hβ (eq_of_heq hPg) he hX
    exact (equivAt_iff (D := (w'.st Z').toD7) _ i (κ' i) R'.toRealDat (O' i) _ hχ').2 ((key.mpr hB))

end GlobalTheory.Mem.R3.Rw.EqvMove

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.OneMapAll GlobalTheory.AdTh GlobalTheory.Mem.R3.Rw.GeoTies

namespace UpperTheory.Mem.GeoExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}

section Two

variable {D' : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0' T0' : Type} {A' : FamIn D'.what₂.LL G' Pl0' T0' D'.R.m}
  {T' : CoreJ D'} [Algebra T'.Q.c.F D'.what₂.LL] {R' : RealDat D' A' T'.Q.c.F} {κ' : ∀ i : Fin D'.R.m, WeightFamilies.Wt D' ((i : ℕ) + 1)}
  {v₀' : ∀ (i : Fin D'.R.m) (σ : D'.what₂.LL →+* ℂ), (R'.MW i σ).Vec} {i' : Fin D'.R.m}

theorem center_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {z : G} (hz : z ∈ Subgroup.center G) :
    φ z ∈ Subgroup.center G' := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g, rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz g]


set_option maxHeartbeats 2000000 in
theorem oneMapOf_two (hR : PreChar R') (hchi : R'.grp_chiW) (hT : TieIn T' R' κ' v₀')
    (O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0)) (hF : O'.c'.F = D'.what₂.embLL.toRatAlgHom.fieldRange)
    (hP' : O'.Pins (κ' i') (v₀' i' (sg0 D' A')) (iotaW T' i') (T'.x₀ ((i' : ℕ) + 1) O'.s0))
    {cE' : (T'.U ((i' : ℕ) + 1) O'.s0).Comp → ℂ} (hU : ∀ k, ‖cE' k‖ = 1) (hE : O'.EquivAt (κ' i') cE')
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec} {ι x₀}
    (hP : O.Pins κ v₀ ι x₀) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.OneMapOf κ v₀ cE 1)
    (hV : R.models_HV) (hj : R.models_jV) (hL : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (hO : OmOver O O')
    (φ : G ≃* G') (pt : AutQ (Wc D' i') → AutQ (Wc D i)) (e : (R.HV i A.μ0).H ≃ₗ[ℂ] (R'.HV i' A'.μ0).H)
    (he : ∀ y, HEq (e y) y ∧ ∀ q, R'.thF i' A'.μ0 (e y) (v₀' i' (sg0 D' A')) q.out = R.thF i A.μ0 y v₀ (pt q).out)
    (hf : ∀ (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (hle : O.c'.F ≤ c.F), HEq O'.c' c →
      ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank,
        ∃ f' ∈ sec (T'.Q.Xo ((i' : ℕ) + 1)) O'.c' (wtA (κ' i')) (Vc D' i').rank, HEq f' (GlobalTheory.FieldBC.rulBC hle f) ∧ ∀ z q,
          (lieFac (T'.Q.Dw ((i' : ℕ) + 1)) (xiR D') (wtA (κ' i')) : ℂ) * adOver O' cE' (actLev O'.c' O'.lev2 (φ z) f') q.out =
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cE (actLev O.c' O.lev2 z f) (pt q).out) :
    O'.OneMapOf (κ' i') (v₀' i' (sg0 D' A')) cE' 1 := by
  refine (lift_of_oneMapOf O hP h).elim fun z h0 => h0.2.elim fun ζ h0' => h0'.2.2.elim fun r h0'' => h0''.elim fun J h1 => ?_
  refine hO.2.elim fun c hO => hO.elim fun hle hO => (hO.2 r J h1.1).elim fun r' h2 => h2.elim fun J' h2 => ?_
  refine oneMapOf_of_span hR hchi hT O' hF hP' hU hE (center_map φ h0.1) (hL h0'.1) h0'.2.1 ?_
  have h3 := span_image e (GlobalTheory.LiftScalarCompare.span_jVx hV hj)
  refine top_le_iff.1 (h3.ge.trans (Submodule.span_mono fun y hy => ?_))
  refine hy.elim fun y₁ hy => hy.1.elim fun y₀ hy₀ => ?_
  have hy' : e (jVx R i A.μ0 y₀) = y := (congrArg e hy₀).trans hy.2
  refine hy' ▸ ?_
  refine (h1.2 y₀).elim fun x h4 => h4.elim fun f h4 => ?_
  refine (h2.2 y₀ x h4.1 _ (he _).1).elim fun x' h8 => ?_
  refine (hf c hle hO.1 f h4.2.1).elim fun f' h10 => ?_
  refine ⟨r', J', x', f', h2.1, h8.1, h10.1, h8.2 _ _ f h4.2.1 h4.2.2.1 f' h10.2.1, fun q => ?_⟩
  exact ((he _).2 q).trans ((h4.2.2.2 _).trans ((mul_assoc _ _ _).trans ((congrArg (ζ * ·) (h10.2.2 z q).symm).trans
    (mul_assoc _ _ _).symm)))

end Two

theorem preChar_of {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) : PreChar R.toRealDat :=
  ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
    RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩


set_option maxHeartbeats 4000000 in
theorem cpt : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          (∃ φ : Gc B w.px ≃* Gc B' w'.px, ∀ g, HEq (φ g) g) ∧ ∃ pt : AutQ (Wc (w'.st Z').toD7 i') → AutQ (Wc (w.st Z).toD7 i), ∀ q, HEq (pt q) q := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ i i' hi
  obtain ⟨h1, -, -, -⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  rcases w' with ⟨px'⟩
  obtain rfl : px' = w.px := eq_of_heq hpx
  obtain rfl : i' = Fin.cast rfl i := Fin.ext hi.symm
  exact ⟨⟨(by with_unfolding_all exact ((MulEquiv.refl (Gc B w.px)) :)), fun g => HEq.rfl⟩, (by with_unfolding_all exact ((id : AutQ (Wc (w.st Z).toD7 i) → AutQ (Wc (w.st Z).toD7 i)) :)), fun q => HEq.rfl⟩

theorem ties_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (v₀' i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL)) →
        ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
        (∀ i, OMPins core' R'.toRealDat κ' v₀' O' i) →
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → OmOver (z.geo.O i) (O' i')) →
        z.R.toRealDat.ExAt → z.R.toRealDat.LUnif → R'.toRealDat.ExAt → MWOver z.R.toRealDat R'.toRealDat →
        BarTie fw' ∧ RhoGeo fw' O' ∧ EquivAll core' R'.toRealDat κ' O' ∧ (∀ i, CTie core' R'.toRealDat κ' v₀' O' i) ∧
          ∀ i, R'.toRealDat.LUnif → PhaseTie core' R'.toRealDat κ' v₀' O' (fun _ => 1) i := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd hv0 O'
    hOP hOm hEx hLU hEx' hMW
  letI := alg'
  have hz := z.pins.char
  have hpz := preChar_of z.R z.F hz hEx
  have hp' := preChar_of R' _ hPins.char hEx'
  have hio := GlobalTheory.IoExtremal.ioExt _ _ _ _ _ _ z.R.toRealDat hpz.lev hpz.fam hpz.models hpz.thP
  have hm : (w.st Z).toD7.R.m = (w'.st Z').toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1.symm
  have key : ∀ i', (O' i').OneMapOf (κ' i') (v₀' i' (sg0 _ _)) (core'.cE ((i' : ℕ) + 1) (O' i').s0) 1 := by
    intro i'
    let i : Fin (w.st Z).toD7.R.m := Fin.cast hm.symm i'
    have hi : (i : ℕ) = i' := rfl
    have h0 := GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses GlobalTheory.ChartFree.chartIndep _ _ _ _ _ z.core z.R.toRealDat _
      z.geo.κ z.geo.v₀ hpz.lev hz.base.grp hpz.fam hpz.models hpz.thP (GlobalTheory.OneMapRefObj.tieIn_of_fwTie z.geo.fw) hio z.geo.O i
      (z.geo.pins i)
    have h1 := z.geo.phase i hLU h0
    have hc0 := cpt w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ i i' hi
    refine hc0.1.elim fun φ hφ => hc0.2.elim fun pt hpt => ?_
    have hl := UpperTheory.theta_lift_data_over_coefficient_extension w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd hv0
      i i' hi hMW pt hpt
    have hf := UpperTheory.cusp_sections_over_coefficient_extension w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ O' i i' hi
      (hOm i i' hi).1 φ hφ pt hpt
    refine hl.elim fun e he => ?_
    have hE' := (EqvMove.equivAll_enl w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ O'
      (fun i i' h => (hOm i i' h).1)).2 i i' hi h1.1
    refine oneMapOf_two hp' hPins.char.base.grp.chiW (GlobalTheory.OneMapRefObj.tieIn_of_fwTie fw') (O' i') (hOP i').1 (hOP i').2
      (fun k => fw'.laws.cUnit _ (inR i') _ ((by with_unfolding_all exact (core'.toCore.good_σ₀ :))) k) hE'
      (z.geo.O i) (z.geo.pins i).2 h1 hpz.models.HV hpz.models.jV ((by with_unfolding_all exact (hE.2.2.2 :))) (hOm i i' hi) φ pt e he hf
  exact ⟨barTie_enl w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd hMW,
    UpperTheory.geometric_action_over_coefficient_extension w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ v₀' fw' hcrd O'
      (fun i i' h => (hOm i i' h).1),
    (EqvMove.equivAll_enl w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hPins hRS κ' hκ O'
      (fun i i' h => (hOm i i' h).1)).1,
    fun i' _ => ⟨1, key i'⟩, fun i' _ _ => key i'⟩

end UpperTheory.Mem.GeoExt

end
