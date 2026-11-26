module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoices
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsReadingResetBaseEnlargement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResetTupleFreeFieldsKeepsClausesComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsReadingResetBaseEnlargementStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteFormsReading_reset_baseEnlargement : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → (∀ i, Seed.FrmC.StdLat (Vc (w'.st Z').toD7 i)) → Seed.FrmC.StdLat (w'.st Z').toD7.sp.X' → ValsIn w'.I →
    ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideA z Wt' R₁ := by
  first | exact @GlobalTheory.Mem.R3.RsA.reset_side | exact GlobalTheory.Mem.R3.RsA.reset_side | (intros; apply GlobalTheory.Mem.R3.RsA.reset_side <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResetModelsMeasuresFormsEnlargedCoefficientBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLExistsBaseChangeCoordinates
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem formsL_exists_baseChange_coordinates : ∀ {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L] [Algebra Ks L'] (ι : L →+* L'), (∀ y : Ks, ι (algebraMap Ks L y) = algebraMap Ks L' y) → ∀ (n : ℕ) (W : (L →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] (G : Type) [Group G] (F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G),
  ∃ F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G,
    (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
    (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
    (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
    (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
    F'.Pt = F.Pt ∧
    ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) → F'.nrm lp y' φ' = F.nrm lp y φ := by
  intro L L' Ks _ _ _ _ _ _ _ _ ι hι n W _ _ G _ F
  let m : (Fin n → L) →ₗ[Ks] (Fin n → L') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by funext k; simp
      map_smul' := fun c x => by
        funext k
        simp only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  have minj : Function.Injective m := by
    intro x y h
    funext k
    exact ι.injective (congrFun h k)
  let e := Submodule.equivMapOfInjective m minj F.WK
  let ρ' : G →* ((Fin n → L') →ₗ[L'] (Fin n → L')) :=
    (Matrix.toLinAlgEquiv' (R := L') (n := Fin n)).toMonoidHom.comp
      ((ι.mapMatrix (m := Fin n)).toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv' (R := L) (n := Fin n)).toMonoidHom.comp F.ρ))
  let j' : ∀ σ' : L' →+* ℂ, (Fin n → L') →ₛₗ[σ'] W (σ'.comp ι) := fun σ' =>
    { toFun := fun x' => ∑ k, σ' (x' k) • F.j (σ'.comp ι) (Pi.single k 1)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  let F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G :=
    { WK := F.WK.map m
      Pt := F.Pt
      nrm := fun lp y φ' => F.nrm lp y (e.symm φ')
      nrm_nonneg := fun lp y f => F.nrm_nonneg lp y _
      nrm_zero := fun lp y => by rw [e.symm.map_zero]; exact F.nrm_zero lp y
      nrm_add := fun lp y f g => by rw [e.symm.map_add]; exact F.nrm_add lp y _ _
      nrm_smul := fun lp y a f => by rw [e.symm.map_smul]; exact F.nrm_smul lp y a _
      towKs := inferInstance
      ρ := ρ'
      chi := (Units.map ι.toMonoidHom).comp F.chi
      j := j' }
  refine ⟨F', ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro σ' x
    have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → L) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    show ∑ k, σ' (ι (x k)) • F.j (σ'.comp ι) (Pi.single k 1) = F.j (σ'.comp ι) x
    conv_rhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, RingHom.comp_apply]
  · intro x'
    show x' ∈ F.WK.map m ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · intro g; rfl
  · intro g x
    show Matrix.toLin' ((LinearMap.toMatrix' (F.ρ g)).map ι) (fun k => ι (x k)) = _
    funext k
    rw [Matrix.toLin'_apply]
    have := RingHom.map_mulVec ι (LinearMap.toMatrix' (F.ρ g)) x k
    rw [LinearMap.toMatrix'_mulVec] at this
    exact this.symm
  · intro lp y' y hy φ' φ hφ
    have hyy : y' = y := eq_of_heq hy
    subst hyy
    show F.nrm lp y' (e.symm φ') = F.nrm lp y' φ
    have : φ' = e φ := Subtype.ext hφ
    rw [this, LinearEquiv.symm_apply_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResetModelsMeasuresFormsEnlargedCoefficientBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw

def labEE {D : D7} (e : D.host.E →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  e.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)


open Classical in
def labX {D : D7} (e : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : D.what₂.Tau :=
  if h : ∃ τ, labEE e τ = tauE D ρ ∨ labEE e τ = (starRingEnd ℂ).comp (tauE D ρ) then h.choose else ρ


open Classical in
def parAtE {D : D7} (W : HSp D) (e : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : SPar :=
  if labEE e (labX e ρ) = tauE D ρ then
    Formalism.L2.NTheta.holPar (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 (Formalism.L2.NTheta.kapW (D.hc (labX e ρ)) _ _)
  else Formalism.IndefR.Mult.dualPar
    (Formalism.L2.NTheta.holPar (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 (Formalism.L2.NTheta.kapW (D.hc (labX e ρ)) _ _))

theorem parAt_eq_parAtE {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) : parAt W σ = parAtE W (σ.comp D.embE) := rfl

theorem exists_heq_io {L : Type} (F : L → Type) [∀ a, AddCommGroup (F a)] [∀ a, Module ℂ (F a)] {P : Type} [AddCommGroup P]
    [Module ℂ P] {a b : L} (hab : a = b) {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W]
    [nW' : NormedAddCommGroup W'] [iW' : InnerProductSpace ℂ W'] (h1 : W' = W) (h2 : HEq nW' nW) (h3 : HEq iW' iW)
    (f : F b →ₗ[ℂ] W →ₗ[ℂ] P) : ∃ f' : F a →ₗ[ℂ] W' →ₗ[ℂ] P, HEq f' f := by
  subst hab h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  exact ⟨f, HEq.rfl⟩

theorem forms_crdOver {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L]
    [Algebra Ks L'] {ι ι₂ : L →+* L'} (hι : ι₂ = ι) {n : ℕ} {W : (L →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] {G : Type} [Group G] {F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G}
    {F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G}
    (h : (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
      (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
      (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
      (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
      F'.Pt = F.Pt ∧
      ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) →
        F'.nrm lp y' φ' = F.nrm lp y φ) :
    (∀ (σ' : L' →+* ℂ) x x', CrdOver ι₂ x x' → HEq (F'.j σ' x') (F.j (σ'.comp ι₂) x)) ∧
      ((∀ x x', CrdOver ι₂ x x' → (x' ∈ F'.WK ↔ x ∈ F.WK)) ∧ ∀ x' ∈ F'.WK, ∃ x : Fin n → L, CrdOver ι₂ x x') ∧
      (∀ g' g, HEq g' g → ((F'.chi g' : L'ˣ) : L') = ι₂ ((F.chi g : Lˣ) : L)) ∧
      (∀ g' g, HEq g' g → ∀ x x', CrdOver ι₂ x x' → CrdOver ι₂ (F.ρ g x) (F'.ρ g' x')) ∧
      HEq F'.Pt F.Pt ∧
      (∀ lp' lp, HEq lp' lp → ∀ y' y, HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), CrdOver ι₂ φ.1 φ'.1 →
        F'.nrm lp' y' φ' = F.nrm lp y φ) := by
  subst hι
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hc : ∀ (x : Fin n → L) (x' : Fin n → L'), CrdOver ι₂ x x' ↔ x' = fun k => ι₂ (x k) := fun x x' =>
    ⟨fun hx => funext fun k => hx.2 k k rfl, fun hx => ⟨rfl, fun k k' e => by rw [hx, Fin.ext e]⟩⟩
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, heq_of_eq h5, ?_⟩
  · intro σ' x x' hx
    rw [(hc _ _).1 hx, h1]
  · intro x x' hx
    rw [(hc _ _).1 hx, h2]
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain rfl : x = y := funext fun k => ι₂.injective (congrFun hyx k)
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  · intro x' hx'
    obtain ⟨x, -, e⟩ := (h2 x').1 hx'
    exact ⟨x, (hc _ _).2 e⟩
  · intro g' g e
    obtain rfl := eq_of_heq e
    exact h3 g'
  · intro g' g e x x' hx
    obtain rfl := eq_of_heq e
    rw [hc, (hc _ _).1 hx, h4]
  · intro lp' lp e y' y ey φ' φ hx
    obtain rfl := eq_of_heq e
    exact h6 lp' y' y ey φ' φ ((hc _ _).1 hx)


set_option maxHeartbeats 4000000 in
theorem resetW : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
    (∀ y : core'.Q.c.F, B'.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) = (y : ℂ)) →
    HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG → RSideA z Wt' R →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideW z Wt' R₁ := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp core' alg' halg eH el ec Xg tr R cG hK hA
  obtain ⟨hPre, -, -, hLL⟩ := hE
  have hι := enlEmb_spec hLL
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := core'
  dsimp only at eH el ec
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  set D := (w.st Z).toD7 with hD
  set D' := (ColW.st _ Z').toD7 with hD'
  set ι := enlEmb hLL with hιdef
  have hιc : D'.what₂.embLL.comp ι = D.what₂.embLL := RingHom.ext hι
  have hE' : D'.embE = ι.comp D.embE := by
    ext x
    apply D'.what₂.embLL.injective
    have h1 := RingHom.congr_fun D'.embE_φ₀ x
    have h2 := RingHom.congr_fun D.embE_φ₀ x
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    exact (h1.trans h2.symm).trans (hι _).symm
  have hpar : ∀ (i : Fin D.R.m) (σ' : D'.what₂.LL →+* ℂ), parAt (Wc D' i) σ' = parAt (Wc D i) (σ'.comp ι) := by
    intro i σ'
    rw [parAt_eq_parAtE, parAt_eq_parAtE, hE']
    rfl

  let MW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), Mult.DSModel (Wc D' i) (parAt (Wc D' i) σ') := fun i σ' =>
    { z.R.MW i (σ'.comp ι) with enum := fun τ => by rw [hpar i σ']; exact (z.R.MW i (σ'.comp ι)).enum τ }
  let HW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), HMod (Mult.MMap (MW' i σ')) := fun i σ' => z.R.HW i (σ'.comp ι)
  let gW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), Representation ℂ (Gc B w.px) (HW' i σ').H := fun i σ' => z.R.gW i (σ'.comp ι)
  have hs0' := sgAt_mk _ R.hv0
  have hs0 := sgAt_mk _ z.R.hv0
  have hs := (congrArg (fun s => RingHom.comp s ι) hs0').trans (hιc.trans hs0.symm)
  have hA0 := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcV, hjL⟩ := hA
  have hio := fun i : Fin D.R.m =>
    exists_heq_io (fun σ => LowT (z.R.MW i σ)) hs (eq_of_heq (hcV i i rfl).1) (hcV i i rfl).2.2.1 (hcV i i rfl).2.2.2 (z.R.ioP i)
  choose ioP' hioP using hio
  letI := z.alg
  have halgι : ∀ y : z.core.Q.c.F, ι (algebraMap z.core.Q.c.F D.what₂.LL y) = algebraMap z.core.Q.c.F D'.what₂.LL y := by
    intro y
    apply D'.what₂.embLL.injective
    exact (hι _).trans ((z.alg_eq y).trans (halg y).symm)
  have hfw := fun i : Fin D.R.m => GlobalTheory.formsL_exists_baseChange_coordinates (L := D.what₂.LL) (L' := D'.what₂.LL) ι halgι (z.R.nW i) (fun σ => (z.R.HW i σ).H) _ (z.R.FW i)
  choose FW' hFW using hfw
  let R₁ : RealDat3 D' _ z.core.Q.c.F :=
    { R with
      MW := MW'
      HW := HW'
      gW := gW'
      νW := (fun i => z.R.νW i)
      fdW := (fun i => z.R.fdW i)
      vacP := (fun i => z.R.vacP i)
      BV := (fun i => z.R.BV i)
      ioP := ioP'
      nW := z.R.nW
      FW := FW'
      thF := (fun _ _ => 0)
      thG := (fun _ _ => 0) }
  refine ⟨R₁, cG, ?_, ?_⟩
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hK
    have f6 := k6.fam
    refine ⟨k1, k2, k3, k4, k5,
      { k6 with fam := ⟨f6.tie, f6.Sb, f6.roots, f6.pl_onto, f6.degR, f6.degL, f6.muVal, f6.etaVal⟩, order := ?hord },
      ⟨k7.tie, k7.onto, k7.hR, k7.hL, k7.SF⟩, ⟨k8.mu_off, k8.mu_used, k8.mu_ne, k8.mu_conj, k8.mu_on⟩, k9,
      { k10 with frameKs := ⟨?hfk1, ?hfk2⟩ }, k11⟩
    case hord =>
      intro i τ a
      have e := z.pins.char.base.models.order i τ a
      exact (congrArg (fun s => (z.R.MW i s).ε τ a) hs).trans e
    case hfk1 =>
      intro i σ σ' h ρ
      have h' : (σ.comp ι).comp (algebraMap z.core.Q.c.F D.what₂.LL) = (σ'.comp ι).comp (algebraMap z.core.Q.c.F D.what₂.LL) := by
        ext y
        have := RingHom.congr_fun h y
        show σ (ι (algebraMap _ D.what₂.LL y)) = σ' (ι (algebraMap _ D.what₂.LL y))
        rw [halgι]
        exact this
      exact z.pins.keep.frameKs.1 i (σ.comp ι) (σ'.comp ι) h' ρ
    case hfk2 =>
      intro i σ h τ a
      have h'' : ∀ ρ, labE (σ.comp ι) (lab (σ.comp ι) ρ) = tauE D ρ := by
        intro ρ
        have e : labEE (D := D') (σ.comp D'.embE) (labX (D := D') (σ.comp D'.embE) ρ) = tauE D' ρ := h ρ
        rw [hE'] at e
        exact e
      exact z.pins.keep.frameKs.2 i (σ.comp ι) h'' τ a
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, -⟩ := hA0
    have hinj : Function.Injective ι := ι.injective
    refine ⟨a1, a2, a3, a4, a5, HEq.rfl, a6, a7, a8, a9, a10, a11, ?blk, hjL⟩
    rintro i ⟨i', hi'⟩ e
    dsimp only at e
    subst e
    refine ⟨(hcV i i rfl).1, (hcV i i rfl).2.1, (hcV i i rfl).2.2.1, (hcV i i rfl).2.2.2, HEq.rfl, hioP i, HEq.rfl,
      congr_arg_heq (fun s => (z.R.MW i s).H) hιc, congr_arg_heq (fun s => (z.R.MW i s).nacg) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).ips) hιc, congr_arg_heq (fun s => (z.R.MW i s).σ) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).lam) hιc, congr_arg_heq (fun s => (z.R.MW i s).ε) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).fr) hιc, proof_irrel_heq _ _, congr_arg_heq (z.R.HW i) hιc, HEq.rfl, HEq.rfl, ?rest⟩
    intro ι₂ hι₂
    have hιι : ι₂ = ι := RingHom.ext fun x => D'.what₂.embLL.injective ((hι₂ x).trans (hι x).symm)
    have hσ : ∀ σ' : D'.what₂.LL →+* ℂ, σ'.comp ι = σ'.comp ι₂ := fun σ' => congrArg σ'.comp hιι.symm
    have hF := forms_crdOver (L := D.what₂.LL) (L' := D'.what₂.LL) (n := z.R.nW i) (W := fun σ => (z.R.HW i σ).H) (F := z.R.FW i)
      (F' := FW' i) hιι (hFW i)
    refine ⟨fun σ' => ⟨⟨congr_arg_heq (fun s => (z.R.MW i s).H) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).nacg) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).ips) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).σ) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).lam) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).ε) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).fr) (hσ σ'), proof_irrel_heq _ _⟩,
        congr_arg_heq (z.R.HW i) (hσ σ'), congr_arg_heq (z.R.gW i) (hσ σ'), hF.1 σ'⟩,
      hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2⟩

end GlobalTheory.Mem.R3.Rw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResetModelsMeasuresFormsEnlargedCoefficientBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reset_modelsMeasuresForms_enlargedCoefficientBase : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
    (∀ y : core'.Q.c.F, B'.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) = (y : ℂ)) →
    HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG → RSideA z Wt' R →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideW z Wt' R₁ := by
  first | exact @GlobalTheory.Mem.R3.Rw.resetW | exact GlobalTheory.Mem.R3.Rw.resetW | (intros; apply GlobalTheory.Mem.R3.Rw.resetW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResetTupleFreeFieldsKeepsClausesComparison
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 2000000 in
theorem reset_stepW : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        (LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) →
        ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₁.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₁.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₁.eG.trans cG₁) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₁.mu R₁.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₁.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₁.IsInert ∧ R₁.IsTup ∧
        R₁.AllPlaces ∧ Keep R₁.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG₁ ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₁.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₁) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg ?_)
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  rintro K ⟨hK, hO⟩
  refine hO.imp ?_
  rintro B' f' T' hOv hOB w' ⟨pin⟩ B f T w hE hf _ hp Z hX Wt z _ _ hFine _ Z' hX' _ hgrp _ core' alg' ha _ hKs hc _ _ _ _
  intro Xg tr R₀ cG hKept
  letI := alg'
  obtain ⟨hHH, -, -, hPos, hStd, hStdX, -, -⟩ := hK (w'.st Z') hOv
  obtain ⟨hVals, -⟩ := hOB w'.px w'.I hX' w'.ok w'.C_eq w'.xi_range
  refine (GlobalTheory.T.definiteFormsReading_reset_baseEnlargement z hE hf hp hFine.2.2.2 (fun i => (hStd _).2.1) hStdX hVals R₀ cG hKept).elim fun Ra h => h.elim fun cGa h => ?_
  refine (GlobalTheory.T.reset_modelsMeasuresForms_enlargedCoefficientBase z hE hf hp core' ha hc.1 hc.2.1 hc.2.2.1 Ra cGa h.1 h.2).elim fun R₁ h => h.elim fun cG₁ h => ?_
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩, b⟩ := h
  exact ⟨R₁, cG₁, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, b⟩

end GlobalTheory.Mem.R3.Rw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResetTupleFreeFieldsKeepsClausesComparisonStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reset_tuple_free_fields_keeps_clauses_comparison : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        (LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) →
        ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₁.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₁.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₁.eG.trans cG₁) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₁.mu R₁.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₁.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₁.IsInert ∧ R₁.IsTup ∧
        R₁.AllPlaces ∧ Keep R₁.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG₁ ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₁.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₁) := by
  first | exact @GlobalTheory.Mem.R3.Rw.reset_stepW | exact GlobalTheory.Mem.R3.Rw.reset_stepW | (intros; apply GlobalTheory.Mem.R3.Rw.reset_stepW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFirstAnalyticDataEnlargedColumnChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFirstAnalyticDataEnlargedColumnChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 4000000 in
theorem seed_at_enl : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg ?_)
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  rintro K ⟨hK, hO⟩
  refine hO.imp ?_
  rintro B' f' T' hOv hOB w' ⟨pin⟩ B f T w _ _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ hgrp _ core' alg' _ _ hKs _ _ _ _ _

  set Wt' : Set B'.places.Pl := {v | B'.places.resChar v ∈ T'.pl} with hWt
  letI := alg'
  obtain ⟨hHH, -, -, hPos, hStd, hStdX, -, -⟩ := hK (w'.st Z') hOv
  have hok := w'.ok
  have hC := w'.C_eq
  have hrange := w'.xi_range
  have hsel : SelHalf w'.I := by
    intro a b P hP P' hP' hq
    obtain ⟨q, hq, hqP, hqP'⟩ := hq
    obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
    obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
    have hab : ∀ v, (w'.I.sel v).under (𝓞 B'.host.F) = v := fun v => by
      have h := pin.above v
      unfold Formalism.L2.Host.aboveF at h
      rw [Set.Finite.mem_toFinset] at h
      exact h
    have hmem : ∀ v, ((q : 𝓞 B'.host.E) ∈ (w'.I.sel v).asIdeal) → (q : 𝓞 B'.host.F) ∈ v.asIdeal := fun v h => by
      rw [← hab v]
      show (q : 𝓞 B'.host.F) ∈ (w'.I.sel v).asIdeal.comap (algebraMap _ _)
      rw [Ideal.mem_comap, map_natCast]
      exact h
    have := pin.half v v' q hq (hmem v hqP) (hmem v' hqP')
    exact congrArg HeightOneSpectrum.asIdeal this
  have hfin : Wt'.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B' T'.pl
  have hconj : ∀ v ∈ Wt', B'.places.conj v ∈ Wt' :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f' ≤ B'.KsC := (GlobalTheory.Mem.Base.KsExact.lower w'.exact).2.2.1
  obtain ⟨hVals, -⟩ := hOB w'.px w'.I hX' hok hC hrange
  have hrange' : Set.range w'.I.xi = T'.set w'.I.C := by rw [hC]; exact hrange
  have hCK : ∀ x ∈ (w'.st Z').B.Ks, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = x := hKs
  have hCE : ∀ x : (w'.st Z').toD7.host.E, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = (w'.st Z').toD7.embE x :=
    fun x => hKs _ (B'.E_le_Ks x)
  have hmu : ∀ (L : Formalism.IndefR.Links.LevCh (w'.st Z').toD7 (TupU w'.I (usedOf w'.I T' Wt'))),
      L.Is (mu0F (X := (w'.st Z').B.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) → L.C = Top.Fr.at (w'.st Z') w'.I.C →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (x : (AE (w'.st Z').toD7)ˣ), infPart (w'.st Z').toD7 (x : AE (w'.st Z').toD7) = 1 →
        ∃ y : core'.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) := by
    intro L hL hLC i x hx
    have hLC' : L.C = Fr.at (w'.st Z') f' := hLC.trans (by rw [hC])
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ Formalism.L2.Pj.FO (w'.st Z').toD7 := by
      refine GlobalTheory.CoreExact.char_mem_of_values (w'.st Z').toD7 _ _ (hL.mu0 i) (Formalism.L2.Pj.FO (w'.st Z').toD7) ?_ ?_ x hx
      · rw [hLC', ← GlobalTheory.CoreExact.KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f'.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => ((w'.st Z').toD7.hc ((w'.st Z').toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (Formalism.L2.Pj.conj_mem_FO _ _ _) (Formalism.L2.Pj.conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨x₁, hx₁, hx₁'⟩ := (mem_FO_assembled_iff (w'.st Z') _).1 hmem
    obtain ⟨y, hy⟩ := hCK x₁ hx₁
    exact ⟨y, by rw [hy]; exact hx₁'.symm⟩
  exact GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices (w'.st Z') w'.px w'.I hX' T' Wt' core'.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hStdX hPos hCK hCE hmu

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFirstAnalyticDataEnlargedColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_firstAnalyticData_enlargedColumnChoices : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) := by
  first | exact @GlobalTheory.Mem.R3.Rw.seed_at_enl | exact GlobalTheory.Mem.R3.Rw.seed_at_enl | (intros; apply GlobalTheory.Mem.R3.Rw.seed_at_enl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataEnlargedBaseTupleFree
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw

theorem exists_realDat_keep_rsideW : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀) := by
  intro p1 p2 p3 p4 p5 p6 p7
  refine StepW.trans (StepW.and (GlobalTheory.T.exists_firstAnalyticData_enlargedColumnChoices p1 p2 p3 p4 p5 p6 p7) (GlobalTheory.T.reset_tuple_free_fields_keeps_clauses_comparison p1 p2 p3 p4 p5 p6 p7)) (StepW.of_all fun K B' f' T' w' _ _ H => ?_)
  intro B f T w e hf hp hpx Z hX Wt z g1 g2 fz hl Z' hX' g3 g4 vt core' alg' a1 a2 a3 hq lc cn dw pb
  obtain ⟨Xg, tr₀, R₀, cG, hc⟩ := H.1 B f T w e hf hp hpx Z hX Wt z g1 g2 fz hl Z' hX' g3 g4 vt core' alg' a1 a2 a3 hq lc cn dw pb
  obtain ⟨R₁, cG₁, hc1⟩ := H.2 B f T w e hf hp hpx Z hX Wt z g1 g2 fz hl Z' hX' g3 g4 vt core' alg' a1 a2 a3 hq lc cn dw pb Xg tr₀ R₀ cG hc
  exact ⟨Xg, tr₀, R₁, cG₁, hc1⟩

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataEnlargedBaseTupleFreeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticData_enlargedBase_tupleFree : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₀) := by
  exact GlobalTheory.Mem.R3.Rw.exists_realDat_keep_rsideW
end
