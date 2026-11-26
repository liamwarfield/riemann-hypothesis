module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormAlternating
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Rep
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem rep_add {a b : IdF A} {j : ℕ} {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c c' : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (h' : CrystallineSemistableComparison.Pb.Rep a b z' c') :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => z s + z' s) (c + c') := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  obtain ⟨f', hf', rfl, hv'⟩ := h'
  refine ⟨f + f', by rw [map_add (f := _), hf, hf', add_zero], rfl, fun s => ?_⟩
  rw [map_add (f := _), ← hv, ← hv']
  rfl

theorem rep_smul {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c : CH.H (sq a b) j} (r : R) (h : CrystallineSemistableComparison.Pb.Rep a b z c) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => r • z s) (r • c) := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  have e : Ideal.Quotient.mk (b.S (s.obj (Fin.last j))) (r • z s) = r • Ideal.Quotient.mk (b.S (s.obj (Fin.last j))) (z s) := rfl
  rw [e, ← hv]
  rfl

theorem rep_congr {a b : IdF A} {j : ℕ} {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (e : ∀ s, z s - z' s ∈ b.S _) : CrystallineSemistableComparison.Pb.Rep a b z' c := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  exact ⟨f, hf, rfl, fun s => (hv s).trans (Ideal.Quotient.eq.2 (e s))⟩

theorem rep_unique {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c c' : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (h' : CrystallineSemistableComparison.Pb.Rep a b z c') : c = c' := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  obtain ⟨f', hf', rfl, hv'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hv s).trans (hv' s).symm)
  subst e
  rfl

theorem rep_zero {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    (e : ∀ s, z s ∈ b.S _) : CrystallineSemistableComparison.Pb.Rep a b z 0 := by
  refine ⟨0, map_zero _, ?_, fun s => ?_⟩
  · exact (Submodule.Quotient.mk_zero _).symm
  · exact (Ideal.Quotient.eq_zero_iff_mem.2 (e s)).symm

theorem d_val {a b : IdF A} {j : ℕ} (f : CH.Cn (sq a b) j) (z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j)))
    (hv : ∀ s, (show sqM a b _ from f s).1 = Ideal.Quotient.mk _ (z s)) (s : ComposableArrows C (j + 1)) :
    (show sqM a b _ from CH.d _ j f s).1 = Ideal.Quotient.mk _
      (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (z (face i s))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (f (face i s)) :
      sqM a b _) = _
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s) (f (face i s))).1 = _
  rw [GlobalTheory.CompanionTheory.GrDelta.sqMap_val a b _ _ _ (hv _)]

theorem rep_exists {a b : IdF A} {j : ℕ} (g : CH.Cn (CH.modF A) j) (hg : ∀ s, g s ∈ a.S _)
    (hd : ∀ s, CH.d _ j g s ∈ b.S _) : ∃ c, CrystallineSemistableComparison.Pb.Rep a b (fun s => g s) c := by
  let f : CH.Cn (sq a b) j := fun s => sqMk a b (g s) (hg s)
  have hd0 : CH.d _ j f = 0 := by
    funext s
    refine Subtype.ext ?_
    rw [d_val f (fun s => g s) (fun _ => rfl)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hd s)
  exact ⟨_, f, hd0, rfl, fun _ => rfl⟩

theorem rep_d {a b : IdF A} {j : ℕ} (g : CH.Cn (CH.modF A) j) (hg : ∀ s, g s ∈ a.S _) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => CH.d _ j g s) 0 := by
  let f : CH.Cn (sq a b) j := fun s => sqMk a b (g s) (hg s)
  refine ⟨CH.d _ j f, CH.d_d _ j f, ?_, fun s => d_val f (fun s => g s) (fun _ => rfl) s⟩
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).symm
  change CH.d _ j f ∈ (CH.cx _).B (j + 1)
  exact ⟨f, rfl⟩

end Rep

end GlobalTheory.CompanionTheory.ConeLocal

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Res
variable {b : Base} {L : b.Fun}

theorem rep_res {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) {j : ℕ}
    {z : ∀ s : ComposableArrows Q.FullSubcategory j, (sP Q).A.obj (s.obj (Fin.last j))} {x : HQ Q r r' j}
    (hx : CrystallineSemistableComparison.Pb.Rep (sFil Q r) (sFil Q r') z x) :
    CrystallineSemistableComparison.Pb.Rep (sFil Q' r) (sFil Q' r') (fun s => z (s ⋙ ObjectProperty.ιOfLE h))
      (((incl h).sq (incl_fil _ r) (incl_fil _ r')).pull j x) := by
  obtain ⟨f, hf, rfl, hv⟩ := hx
  refine ⟨((incl h).sq (incl_fil _ r) (incl_fil _ r')).pullC j f, ?_, rfl, fun s => ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · change Ideal.quotientMap _ _ _ (show sqM _ _ _ from f (s ⋙ ObjectProperty.ιOfLE h)).1 = _
    rw [hv]
    rfl

def resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (f : CH.Cn (CH.modF (sP Q).A) k) :
    CH.Cn (CH.modF (sP Q').A) k :=
  fun s => f (s ⋙ ObjectProperty.ιOfLE h)

theorem d_resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (f : CH.Cn (CH.modF (sP Q).A) k) :
    CH.d _ k (resQ h f) = resQ h (CH.d _ k f) :=
  (CH.Mor.d_pullC (⟨ObjectProperty.ιOfLE h, fun _ => LinearMap.id, fun _ _ => rfl⟩ :
    CH.Mor (CH.modF (sP Q).A) (CH.modF (sP Q').A) (RingHom.id _)) k f)

theorem cup_resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (ℓ : Fin k → CH.Cn (CH.modF (sP Q).A) 1) :
    resQ h (cupListC (sP Q).A ℓ) = cupListC (sP Q').A fun i => resQ h (ℓ i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext s
    have e := ih fun i => ℓ (Fin.castSucc i)
    change _ = (CH.mulP (sP Q').A).cupC _ (cupListC (sP Q').A fun i => resQ h (ℓ (Fin.castSucc i))) (resQ h (ℓ (Fin.last k))) s
    rw [← e]
    rfl

end Res

section Frames
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def Taylor (Fil : ℤ → IdF Φ.A) {d : ℕ} (E : Frame Φ d) (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) : Prop :=
  ∀ (T : C) (u v : E.D ⟶ T) (x : Φ.A.obj E.D),
    (Φ.A.map u).hom x - (Φ.A.map v).hom x - ∑ k, E.τ k v u * (Φ.A.map v).hom (p k x) ∈ (Fil 2).S T

def sgn {m d : ℕ} (I : Idx m d) (J : Fin m → Fin d) : ℤ :=
  ∑ π : Equiv.Perm (Fin m), if J = I.1 ∘ π then (Equiv.Perm.sign π : ℤ) else 0

end Frames

section Loc
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def IsLoc (s : ℕ) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D) : Prop :=
  E.GrConst (sFil (KS q s {W})) ∧
  (∀ x, x ∈ (sFil (KS q s {W}) 1).S E.D → x = 0) ∧
  (∀ a : K, ε (strV q W a) = algebraMap K ((sP (KS q s {W})).A.obj E.D) a) ∧
  (∀ (T : (KS q s {W}).FullSubcategory) (u : E.D ⟶ T) (g : Γ(X, W)),
    ev T.obj (ks_in q s W _ T.property) g = Ideal.Quotient.mk T.obj.J (((sP (KS q s {W})).A.map u).hom (ε g))) ∧
  ∀ (i : Fin d) {T : (KS q s {W}).FullSubcategory} (u v : E.D ⟶ T),
    E.τ i u v = ((sP (KS q s {W})).A.map v).hom (ε (t i)) - ((sP (KS q s {W})).A.map u).hom (ε (t i))

end Loc
end GlobalTheory.CompanionTheory.ConeLocal
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrMod

theorem factor_factor {R : Type} [CommRing R] {I J K : Ideal R} (h1 : I ≤ J) (h2 : J ≤ K) (y : R ⧸ I) :
    Ideal.Quotient.factor h2 (Ideal.Quotient.factor h1 y) = Ideal.Quotient.factor (h1.trans h2) y := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem fil_extend {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    (δ : DividedPowers J) (δ' : DividedPowers J') (φ : B →+* B') (hJ : J' = J.map φ)
    (h : IsDPMorphism δ δ' φ) (r : ℕ) : fil δ' r = (fil δ r).map φ := by
  subst hJ
  exact (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers δ φ δ' h).1 r

theorem pow_mem_span {R : Type} [CommRing R] {I : Ideal R} (δ : DividedPowers I) {p : ℕ} (hp : p ≠ 0)
    {x : R} (hx : x ∈ I) : x ^ p ∈ Ideal.span {(p : R)} := by
  rw [← δ.factorial_mul_dpow_eq_pow hx]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem l_mem_pfil : (l : A.Acr n) ∈ A.PFil n :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

theorem sharp_zero : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem uToPQ_th (x : A.W) : A.uToPQ n (A.th x) = Ideal.Quotient.mk _ (A.toAcr n x) := by
  rw [uToPQ, RingHom.comp_apply, uToQ_th, Ideal.Quotient.factor_mk]

theorem exists_pi : ∃ π : A.A →+* A.Acr n ⧸ A.PFil n,
    (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧
      π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi}) := by
  let g : A.W →+* A.Acr n ⧸ A.PFil n := (Ideal.Quotient.mk _).comp (A.toAcr n)
  let π : A.A →+* A.Acr n ⧸ A.PFil n :=
    (WittVector.constantCoeff : A.W →+* A.A).liftOfSurjective A.constantCoeff_surjective ⟨g, fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff x).2 hx)
      rw [RingHom.mem_ker, map_mul, RingHom.comp_apply (Ideal.Quotient.mk _) (A.toAcr n) (l : A.W), map_natCast,
        Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n), mul_zero]⟩
  have hπ : ∀ x : A.W, π (x.coeff 0) = g x := fun x => RingHom.liftOfSurjective_comp_apply _ _ _ x
  have ht : ∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a)) := fun a => by
    have := hπ (WittVector.teichmuller l a)
    rwa [WittVector.teichmuller_coeff_zero] at this
  have hs : ∀ a, π a = A.uToPQ n (A.sharp a) := fun a => by
    rw [ht]
    exact (uToPQ_th A n _).symm
  refine ⟨π, ht, fun y => ?_, ?_, fun hn => ?_⟩
  · obtain ⟨u, rfl⟩ := (RL.uToQ A n).2.2.1 y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, (hπ x).trans (uToPQ_th A n x).symm⟩
  · rw [hs, sharp_pi, map_natCast, ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n)
  · ext a
    have h := (RL.sharp_cong A).2.1 a 0
    rw [sharp_zero, sub_zero, sub_zero] at h
    rw [RingHom.mem_ker, hs, ← RingHom.mem_ker, (RL.uToQ A n).2.2.2 hn, h]

theorem fil_eq_map (r : ℕ) : A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n) := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 (mapAcr_fil A.fromBase n r))
  rw [PAlg.Fil, Ideal.span_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [← mapAcr_dxi A.fromBase n k]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, hk, rfl⟩)

theorem pfil_eq_map : A.PFil n = ((base l).PFil n).map (mapAcr A.fromBase n) := by
  rw [PFil, PFil, Ideal.map_sup, ← fil_eq_map, Ideal.map_span, Set.image_singleton, map_natCast]

theorem jj_eq_map (k : Bool) : JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n) := by
  cases k
  · exact fil_eq_map A n 1
  · exact pfil_eq_map A n

theorem fil_mono {r s : ℕ} (h : r ≤ s) : A.Fil n s ≤ A.Fil n r := by
  refine Ideal.span_mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, h.trans hk, rfl⟩

theorem fil_pdFil (r : ℕ) : fil (A.pdFil n) r = A.Fil n r := by
  refine le_antisymm ?_ ?_
  · have hprod : ∀ L : List (ℕ × A.Acr n), (∀ p ∈ L, p.2 ∈ A.Fil n 1) →
        (L.map fun p => (A.pdFil n).dpow p.1 p.2).prod ∈ A.Fil n (L.map Prod.fst).sum := by
      intro L
      induction L with
      | nil =>
        intro _
        simp only [List.map_nil, List.prod_nil, List.sum_nil]
        rw [(RL.filtration_multiplicative A).2.2.2.2.2.2.1 n]
        trivial
      | cons p L ih =>
        intro hL
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact (RL.filtration_multiplicative A).2.2.2.2.2.2.2 n _ _ (Ideal.mul_mem_mul
          (A.dpow_mem_fil n p.1 (hL p (by simp))) (ih fun q hq => hL q (by simp [hq])))
    refine Ideal.span_le.2 ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact fil_mono A n h2 (hprod L h1)
  · rw [PAlg.Fil, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [← A.dpow_dxi n k]
    have h1 : A.dxi n 1 ∈ A.Fil n 1 := Ideal.subset_span ⟨1, le_rfl, rfl⟩
    exact GlobalTheory.CompanionTheory.PDMap.fil_anti (A.pdFil n) hk (GlobalTheory.CompanionTheory.PDMap.dpow_mem_fil (A.pdFil n) h1 k)

theorem pfil_pow (x : A.Acr n) (hx : x ∈ A.PFil n) : IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)} := by
  have h := pow_mem_span (A.pdPFil n) (Fact.out : l.Prime).ne_zero hx
  refine ⟨?_, h⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨l * n, by rw [pow_mul, ← hc, mul_pow, A.pow_l_acr n, mul_zero]⟩

theorem uJ_facts (k : Bool) (hn : n ≠ 0) :
    Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨u, hu⟩ := (RL.uToQ A n).1 (Ideal.Quotient.mk _ z)
    refine ⟨u, ?_⟩
    rw [uJ, RingHom.comp_apply, hu, Ideal.Quotient.factor_mk]
  · have e : A.uToPQ n x = Ideal.Quotient.factor (le_pfil k A n) (uJ k A n x) := by
      rw [uJ, RingHom.comp_apply, factor_factor]
      rfl
    have h0 : x ∈ RingHom.ker (A.uToPQ n) := by
      rw [RingHom.mem_ker, e, RingHom.mem_ker.1 hx, map_zero]
    rw [(RL.uToQ A n).2.2.2 hn] at h0
    exact (Ideal.span_singleton_le_iff_mem _).2 (R.mem_jacobson_of_complete (l : A.U)) h0

theorem acr_modp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  intro l _ A n
  exact ⟨exists_pi A n, fil_eq_map A n, jj_eq_map A n, fil_pdFil A n,
    fun k r => fil_extend _ _ _ (jj_eq_map A n k) (dd_map k A.fromBase n) r,
    pfil_pow A n, fun k hn => uJ_facts A n k hn⟩

end GlobalTheory.CompanionTheory.AcrMod
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_base_change_from_universal : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  first | exact @GlobalTheory.CompanionTheory.AcrMod.acr_modp | exact GlobalTheory.CompanionTheory.AcrMod.acr_modp | (intros; apply GlobalTheory.CompanionTheory.AcrMod.acr_modp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionIsUnitOfCoeffZero
namespace GlobalTheory

open IsLocalRing

theorem _root_.GlobalTheory.preTilt_isLocalRing : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Fact ¬IsUnit (p : O)], IsLocalRing (PreTilt O p) := by
  intro p _ O _ _ _
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Perfection.coeff (ModP O p) p 0) := by
    refine ⟨fun x hx => ?_⟩
    have hunit : ∀ n, IsUnit (Perfection.coeff (ModP O p) p n x) := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        rw [← Perfection.coeff_pow_p' x n] at ih
        exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ih
    let y : Perfection (ModP O p) p := ⟨fun n => ↑(hunit n).unit⁻¹, fun n => by
      have key : (hunit (n + 1)).unit ^ p = (hunit n).unit :=
        Units.ext (by simpa using Perfection.coeff_pow_p' x n)
      rw [← Units.val_pow_eq_pow_val, inv_pow, key]⟩
    have hxy : x * y = 1 := Perfection.ext fun n => by
      rw [map_mul, map_one]
      show Perfection.coeff (ModP O p) p n x * ↑(hunit n).unit⁻¹ = 1
      exact (hunit n).mul_val_inv
    exact ⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩
  exact (Perfection.coeff (ModP O p) p 0).domain_isLocalRing

end GlobalTheory
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsFacts

variable {l : ℕ} [Fact l.Prime]

theorem geom_sum_eq_zero {R : Type*} [CommRing R] [IsDomain R] {z : R} {m : ℕ} (h : z ^ m = 1) (h1 : z ≠ 1) :
    ∑ i ∈ Finset.range m, z ^ i = 0 := by
  have e := mul_geom_sum z m
  rw [h, sub_self] at e
  exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 h1)

theorem pow_chain {M : Type*} [Monoid M] {m : ℕ} (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ m = e k) (k j : ℕ) :
    e (k + j) ^ m ^ j = e k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ m j, mul_comm, pow_mul, ← add_assoc, hs, ih]

theorem prim_chain {M : Type*} [CommMonoid M] (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ l = e k) (h0 : e 0 = 1)
    (h1 : e 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (e m) (l ^ m) := by
  cases m with
  | zero => simpa [h0] using IsPrimitiveRoot.one
  | succ k =>
    have a : e (k + 1) ^ l ^ k = e 1 := by
      have := pow_chain e hs 1 k
      rwa [add_comm 1 k] at this
    have b : e (k + 1) ^ l ^ (k + 1) = 1 := by
      have := pow_chain e hs 0 (k + 1)
      rwa [zero_add, h0] at this
    have o : orderOf (e (k + 1)) = l ^ (k + 1) :=
      orderOf_eq_prime_pow (by rw [a]; exact h1) b
    exact o ▸ IsPrimitiveRoot.orderOf _

theorem coeff_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] (a : R) (ha : ¬ IsUnit (a - 1)) (i : ℕ) :
    ¬ IsUnit ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) := by
  have h1 : IsLocalRing.residue R a = 1 := by
    have : IsLocalRing.residue R (a - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 ha)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have h2 : WittVector.map (IsLocalRing.residue R) (WittVector.teichmuller l a - 1 : WittVector l R) = 0 := by
    rw [map_sub, map_one, WittVector.map_teichmuller, h1, map_one, sub_self]
  have h3 : IsLocalRing.residue R ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) = 0 := by
    rw [← WittVector.map_coeff, h2, WittVector.zero_coeff]
  exact (IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3)

variable (l) in
theorem isLocalRing_oc : IsLocalRing (OC l) := ValuationRing.isLocalRing (OC l)

variable (l) in
theorem isLocalRing_ob : IsLocalRing (Ob l) :=
  haveI := isLocalRing_oc l
  GlobalTheory.preTilt_isLocalRing l (OC l)

variable (l) in
theorem pFlat_not_isUnit : ¬ IsUnit (pFlat l) := fun h => by
  have h1 : IsUnit (theta0 l (WittVector.teichmuller l (pFlat l))) := (h.map (WittVector.teichmuller l)).map (theta0 l)
  rw [WittVector.fontaineTheta_teichmuller, untilt_pFlat] at h1
  exact (inferInstance : Fact (¬ IsUnit (l : OC l))).out h1

theorem integral_prime_dvd_epsilon_zero_sub_one (ε : Eps l) : pFlat l ∣ ((ε.e 0 : Ob l) - 1) := by
  have h := ((RL.sharp_cong (base l)).2.1 (ε.e 0 : Ob l) 1).1 (by
    have h0 : (base l).sharp (ε.e 0 : Ob l) = 1 := ε.sharp_e (base l)
    rw [h0, map_one, sub_self]
    exact zero_mem _)
  exact Ideal.mem_span_singleton.1 h

theorem epsilon_one_sub_one_not_isUnit (ε : Eps l) : ¬ IsUnit ((ε.e 1 : Ob l) - 1) := fun h => by
  haveI : CharP (Ob l) l := inferInstance
  have h1 : IsUnit (((ε.e 1 : Ob l) - 1) ^ l) := h.pow l
  have e : (ε.e 1 : Ob l) ^ l = ε.e 0 := by
    have := congrArg Units.val (ε.succ 0)
    rwa [Units.val_pow_eq_pow_val] at this
  rw [sub_pow_char, e, one_pow] at h1
  exact pFlat_not_isUnit l (isUnit_of_dvd_unit (integral_prime_dvd_epsilon_zero_sub_one ε) h1)

theorem theta_e_succ (ε : Eps l) (k : ℕ) :
    theta0 l (WittVector.teichmuller l (ε.e (k + 1) : Ob l)) ^ l = theta0 l (WittVector.teichmuller l (ε.e k : Ob l)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]

theorem qk_succ (ε : Eps l) (k : ℕ) : ε.qk (k + 1) ^ l = ε.qk k := by
  rw [Eps.qk, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ, Eps.qk]

theorem sum_mem_ker (ε : Eps l) :
    ∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i ∈ RingHom.ker (theta0 l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [RingHom.mem_ker, map_sum]
  simp only [map_pow]
  exact geom_sum_eq_zero ((theta_e_succ ε 0).trans ε.one) ε.prim

theorem cris_sum_mem (ε : Eps l) (A : PAlg l) (n : ℕ) :
    A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1 := by
  have e : ∑ i ∈ Finset.range l, ε.qk 1 ^ i =
      algebraMap (Ainf l) (Acris l) (∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, Eps.qk]
  have h := sum_mem_ker ε
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  rw [e, cris_algebraMap, ← hc, map_mul, map_mul]
  change _ * A.toAcr n A.xi ∈ _
  rw [toAcr_xi]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem mu_eq (ε : Eps l) : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i := by
  rw [mul_geom_sum, qk_succ ε 0, Eps.μ]

theorem eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  intro l _ ε
  haveI := isLocalRing_ob l
  exact ⟨fun i => coeff_not_isUnit _ (epsilon_one_sub_one_not_isUnit ε) i, qk_succ ε, cris_sum_mem ε, mu_eq ε,
    prim_chain (fun m => theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (theta_e_succ ε) ε.one ε.prim⟩

end GlobalTheory.CompanionTheory.EpsFacts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementPropertiesStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_cyclotomic_element_properties : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.EpsFacts.eps_facts | exact GlobalTheory.CompanionTheory.EpsFacts.eps_facts | (intros; apply GlobalTheory.CompanionTheory.EpsFacts.eps_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormFrame
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.FrameEx

theorem dividedPowerFiltration_dividedPowersBot (O : Type) [CommRing O] {n : ℕ} (hn : n ≠ 0) :
    pdP (dividedPowersBot O) n = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have hpos : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra hne
    push_neg at hne
    have : (l.map Prod.fst).sum = 0 := by
      refine List.sum_eq_zero ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hne p hp
    omega
  obtain ⟨p, hp, hp0⟩ := hpos
  have h0 : p.2 = 0 := by simpa using hl p hp
  have : (dividedPowersBot O).dpow p.1 p.2 = 0 := by
    rw [h0]; exact (dividedPowersBot O).dpow_eval_zero hp0
  have hz : (l.map fun q => (dividedPowersBot O).dpow q.1 q.2).prod = 0 :=
    List.prod_eq_zero (List.mem_map.2 ⟨p, hp, this⟩)
  rw [hz]
  exact Ideal.zero_mem _

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem inU_of_SS {l s : ℕ} {W : X.Opens} (T : Thick (LL q)) (h : SS q l s W T) : InU W T := by
  obtain ⟨-, V, hV, hT⟩ := h
  rw [Set.mem_singleton_iff.1 hV] at hT
  exact hT

end GlobalTheory.CompanionTheory.GrForm.FrameEx

namespace GlobalTheory.CompanionTheory.GrForm

open FrameEx in
theorem stFrame : StFrame := by
  intro O _ l s hb X q W d c u hu
  letI := (strV q W).toAlgebra
  obtain ⟨c', e, hTF, he1, het, hev⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (I := ⊥) (dividedPowersBot O) l s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  have good := GlobalTheory.T.chart_is_good c'
  have hQ : ∀ T, SS q l s W T → InU W T := inU_of_SS
  have hD : SS q l s W c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpow, hgr⟩ := GlobalTheory.T.chart_divided_powers_graded_constant c' good (SS q l s W) hQ hD
  have hval : ∀ (T : Thick (LL q)) (h : InU W T) (σ : c'.D ⟶ T) (f : Γ(X, W)),
      Ideal.Quotient.mk T.J (σ.φ (e (1 ⊗ₜ f))) = ev T h f := by
    intro T h σ f
    rw [ev_nat σ c'.inV h f, hev f]
    rfl
  have hσ : ∀ T : (SS q l s W).FullSubcategory, ∃ σ : c'.D ⟶ T.obj, ∀ i, σ.φ (c'.t i) = u i T.obj := by
    intro T
    have hT := hQ _ T.property
    obtain ⟨σ₀⟩ := good.1 T.obj hT
    obtain ⟨σ, h1, -⟩ := good.2 T.obj σ₀ (fun i => u i T.obj - σ₀.φ (c'.t i)) (fun i => by
      refine Ideal.Quotient.eq.1 ?_
      rw [hu i T.obj hT, ← het i, hval T.obj hT σ₀])
    exact ⟨σ, fun i => by simpa using h1 i⟩
  choose σ hσ using hσ
  let θ : Γ(X, W) ≃+* (sP (SS q l s W)).A.obj (c'.frame good (SS q l s W) hQ hD).D :=
    ((Algebra.TensorProduct.lid O Γ(X, W)).symm.toRingEquiv).trans e
  have hθ : ∀ f, θ f = e (1 ⊗ₜ f) := fun f => rfl
  refine ⟨c'.frame good (SS q l s W) hQ hD, fun T => ObjectProperty.homMk (σ T), θ, hgr, ?_, ?_, ?_, ?_⟩
  · intro n hn
    change c'.D.pdPow ((n : ℤ).toNat) = ⊥
    rw [Int.toNat_natCast, hpow, dividedPowerFiltration_dividedPowersBot O hn, Ideal.map_bot]
  · intro i T s s'
    change (s'.hom.φ (c'.t i) - s.hom.φ (c'.t i) : T.obj.B) = s'.hom.φ (θ (c.t i)) - s.hom.φ (θ (c.t i))
    rw [hθ, het]
  · intro i T
    change (σ T).φ (θ (c.t i)) = u i T.obj
    rw [hθ, het, hσ]
  · intro T h f
    exact hval T.obj h (σ T) f

end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormFrameStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_frame : GlobalTheory.CompanionTheory.GrForm.StFrame := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stFrame | exact GlobalTheory.CompanionTheory.GrForm.stFrame | (intros; apply GlobalTheory.CompanionTheory.GrForm.stFrame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.WittLevel

theorem isNoetherianRing_Wm_one :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l],
      IsNoetherianRing (Wc.Wm l k 1) := by
  intro l _ k _ _ _
  unfold Wc.Wm
  infer_instance

end GlobalTheory.CompanionTheory.WittLevel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherianStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_witt_isNoetherian : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l], IsNoetherianRing (Wc.Wm l k 1) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | exact GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | (intros; apply GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueHom
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfLift

variable {l : ℕ} [Fact l.Prime] {R S : Type} [CommRing R] [CommRing S]

def powHom (hS : (l : S) = 0) (n : ℕ) : S →+* S where
  toFun x := x ^ l ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : l.Prime) x y n
    rw [hr, hS]; simp

theorem powHom_apply (hS : (l : S) = 0) (n : ℕ) (x : S) : powHom hS n x = x ^ l ^ n := rfl

def rootHom [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) : R ≃+* R :=
  RingEquiv.ofBijective (powHom hR n)
    (PerfectRing.bijective_frobenius : Function.Bijective fun x : R => x ^ l ^ n)

theorem rootHom_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (a : R) :
    ((rootHom hR n).symm a) ^ l ^ n = a :=
  (rootHom hR n).apply_symm_apply a

theorem rootHom_symm_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (b : R) :
    (rootHom hR n).symm (b ^ l ^ n) = b :=
  (rootHom hR n).symm_apply_apply b

def level [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) : R →+* S ⧸ Ideal.span {π} ^ l ^ n :=
  (Ideal.quotientMap (Ideal.span {π} ^ l ^ n) (powHom hS n)
    (fun _ hx => Ideal.mem_comap.2 (Ideal.pow_mem_pow hx _))).comp
      (g.comp ((rootHom hR n).symm : R →+* R))

theorem level_spec [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) (b : R) (x : S)
    (hx : Ideal.Quotient.mk _ x = g b) :
    level hR hS π g n (b ^ l ^ n) = Ideal.Quotient.mk _ (x ^ l ^ n) := by
  have h1 : ((rootHom hR n).symm : R →+* R) (b ^ l ^ n) = b := rootHom_symm_pow hR n b
  simp only [level, RingHom.comp_apply, h1, ← hx, Ideal.quotientMap_mk, powHom_apply]

theorem strictMono_pow : StrictMono fun n : ℕ => l ^ n :=
  strictMono_nat_of_lt_succ fun n => Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (Nat.lt_succ_self n)

theorem level_compat [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (m : ℕ) :
    (Ideal.Quotient.factorPow (Ideal.span {π}) ((strictMono_pow (l := l)).monotone m.le_succ)).comp
      (level hR hS π g (m + 1)) = level hR hS π g m := by
  ext a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ (m + 1) = a := ⟨_, rootHom_pow hR (m + 1) a⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g b)
  have hx' : Ideal.Quotient.mk (Ideal.span {π}) (x ^ l) = g (b ^ l) := by
    rw [map_pow, map_pow, hx]
  have e1 : b ^ l ^ (m + 1) = (b ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  have e2 : x ^ l ^ (m + 1) = (x ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  rw [RingHom.comp_apply, level_spec hR hS π g (m + 1) b x hx, e1, level_spec hR hS π g m _ _ hx', e2]
  rfl

theorem exists_lift [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsAdicComplete (Ideal.span {π}) S] (g : R →+* S ⧸ Ideal.span {π}) :
    ∃ f : R →+* S, (Ideal.Quotient.mk _).comp f = g := by
  refine ⟨IsAdicComplete.StrictMono.liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m), ?_⟩
  ext a
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g a)
  have h0 := IsAdicComplete.StrictMono.mk_liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m) (n := 0) a
  have h1 := level_spec hR hS π g 0 a x hx
  have ea : a ^ l ^ 0 = a := by simp
  have ex : x ^ l ^ 0 = x := by simp
  rw [ea, ex] at h1
  have h2 := Ideal.Quotient.eq.1 (h0.trans h1)
  have eI : Ideal.span {π} ^ l ^ 0 = Ideal.span {π} := by simp
  rw [eI] at h2
  rw [RingHom.comp_apply, ← hx]
  exact Ideal.Quotient.eq.2 h2

theorem lift_unique [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsHausdorff (Ideal.span {π}) S] (f f' : R →+* S)
    (h : (Ideal.Quotient.mk (Ideal.span {π})).comp f = (Ideal.Quotient.mk _).comp f') : f = f' := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' (Ideal.span {π}) (strictMono_pow (l := l))
  intro n a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ n = a := ⟨_, rootHom_pow hR n a⟩
  have hb : f b - f' b ∈ Ideal.span {π} :=
    Ideal.Quotient.eq.1 (RingHom.congr_fun h b)
  refine Ideal.Quotient.eq.2 ?_
  have e : f (b ^ l ^ n) - f' (b ^ l ^ n) = (f b - f' b) ^ l ^ n := by
    have := map_sub (powHom hS n) (f b) (f' b)
    simpa only [powHom_apply, map_pow] using this.symm
  rw [e]
  exact Ideal.pow_mem_pow hb _

theorem existsUnique_hom {l : ℕ} [Fact l.Prime] (A A' : PAlg l)
    (g : A.A →+* A'.A ⧸ Ideal.span {A'.pi})
    (hg : g.comp A.s = (Ideal.Quotient.mk _).comp A'.s) :
    ∃! φ : A ⟶ A', (Ideal.Quotient.mk _).comp (PAlg.Hom.f φ) = g := by
  have : IsAdicComplete (Ideal.span {A'.pi}) A'.A := A'.compl
  have hOb : ((l : ℕ) : Ob l) = 0 := CharP.cast_eq_zero _ l
  obtain ⟨f, hf⟩ := exists_lift A.natCast_l A'.natCast_l A'.pi g
  have hcomm : f.comp A.s = A'.s := by
    refine lift_unique hOb A'.natCast_l A'.pi _ _ ?_
    rw [← RingHom.comp_assoc, hf, hg]
  refine ⟨⟨f, hcomm⟩, hf, fun φ hφ => ?_⟩
  apply PAlg.Hom.ext
  exact lift_unique A.natCast_l A'.natCast_l A'.pi _ _ (hφ.trans hf.symm)

end GlobalTheory.CompanionTheory.PerfLift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChart
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ChartP

open GlobalTheory.CompanionTheory.ChartAlg

section Lift

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} {T : Fin d → Γ(X, V)}
  (𝓛 : CrystallineSemistableComparison.B.Lift (strV q V) T R I κ)

def barI : R ⧸ I →+* 𝓛.D ⧸ I.map 𝓛.i := Ideal.quotientMap (I.map 𝓛.i) 𝓛.i Ideal.le_comap_map

theorem barI_mk (r : R) : barI 𝓛 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (𝓛.i r) := rfl

theorem j_strV : 𝓛.j.comp (strV q V) = (barI 𝓛).comp κ := by
  refine RingHom.ext fun o => ?_
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
  rw [RingHom.comp_apply, RingHom.comp_apply, 𝓛.hj o x hx, ← hx, barI_mk]

def ptL (hV : IsAffineOpen V) : PtOver X q κ (𝓛.D ⧸ I.map 𝓛.i) :=
  ⟨(barI 𝓛, Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec), by
    change (Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec) ≫ q = Spec.map (CommRingCat.ofHom ((barI 𝓛).comp κ))
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← j_strV]
    rfl⟩

theorem rep_lift (hV : IsAffineOpen V) (B : CommRingCat.{0}) (y' : PtOver X q κ B) (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : 𝓛.D ⧸ I.map 𝓛.i →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) (ptL 𝓛 hV) = y' := by
  let e' : Γ(X, V) →+* B := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B := y'.1.1
  have hbase : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x := by
    intro o x hx
    rw [RingHom.comp_apply, hx]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' o
  obtain ⟨f, ⟨hf1, hf2⟩, hfu⟩ := 𝓛.univ B (ψ'.comp (Ideal.Quotient.mk I)) e'
    (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]) hbase
  have hk : ∀ a ∈ I.map 𝓛.i, f a = 0 := by
    have hle : I.map 𝓛.i ≤ RingHom.ker f := Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    exact fun a ha => hle ha
  let φ : 𝓛.D ⧸ I.map 𝓛.i →+* B := Ideal.Quotient.lift _ f hk
  have hφ : ∀ z, φ (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have hφj : φ.comp 𝓛.j = e' := by
    refine RingHom.ext fun r => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
    rw [RingHom.comp_apply, ← hz, hφ]
    exact hf2 r z hz
  have hφψ : φ.comp (barI 𝓛) = ψ' := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun r => ?_
    change φ (barI 𝓛 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
    rw [barI_mk, hφ]
    exact RingHom.congr_fun hf1 r
  refine ⟨φ, ?_, ?_⟩
  · refine Subtype.ext (Prod.ext hφψ ?_)
    change Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]
    exact eq_specMap hV y'.1.2 hy'
  · intro φ' h'
    have h1 : φ'.comp (barI 𝓛) = ψ' := congrArg (fun z => z.1.1) h'
    have h2 : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom 𝓛.j) ≫ hV.fromSpec = y'.1.2 :=
      congrArg (fun z => z.1.2) h'
    have h3 : e' = φ'.comp 𝓛.j := by
      refine evalAt_specMap hV (φ'.comp 𝓛.j) y'.1.2 ?_ hy'
      rw [← h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h4 : φ'.comp (Ideal.Quotient.mk _) = f := by
      refine hfu _ ⟨?_, fun r z hz => ?_⟩
      · refine RingHom.ext fun r => ?_
        exact RingHom.congr_fun h1 (Ideal.Quotient.mk I r)
      · rw [h3]
        exact congrArg φ' hz
    apply Ideal.Quotient.ringHom_ext
    exact h4

variable (γ : DividedPowers I) (p : ℕ) (δ : DividedPowers (I.map 𝓛.i)) (hδ : IsDPMorphism γ δ 𝓛.i)
  (hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i))) (hV : IsAffineOpen V)

def thL : Thick (nlFun γ p X q κ) := mkT 𝓛.D 𝓛.i (I.map 𝓛.i) δ hadm hδ (ptL 𝓛 hV) (fun _ => rfl)

theorem thL_inU : InU V (thL 𝓛 γ p δ hδ hadm hV) := top_le_specMap hV 𝓛.j

theorem ev_thL : ev (thL 𝓛 γ p δ hδ hadm hV) (thL_inU 𝓛 γ p δ hδ hadm hV) = 𝓛.j :=
  evalAt_specMap hV 𝓛.j _ rfl _

def chartL (het : (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t : MvPolynomial (Fin d) R →+* 𝓛.D).Etale) : Chart γ p q κ V d where
  D := thL 𝓛 γ p δ hδ hadm hV
  t := 𝓛.t
  etale := het
  J_eq := rfl
  inV := thL_inU 𝓛 γ p δ hδ hadm hV
  rep := rep_lift 𝓛 hV

end Lift

theorem exists_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  intro O R _ _ I γ p hp hn X q κ V d c
  obtain ⟨𝓛⟩ := GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift (strV q V) c.t I κ c.etale
  have hflat : 𝓛.i.Flat := (GlobalTheory.CompanionTheory.LiftFlat.lift_flat 𝓛.i 𝓛.t 𝓛.et).1
  obtain ⟨δ, hδ⟩ : ∃ δ : DividedPowers (I.map 𝓛.i), IsDPMorphism γ δ 𝓛.i := by
    letI := 𝓛.i.toAlgebra
    haveI : Module.Flat R 𝓛.D := hflat
    exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat R 𝓛.D I γ
  have hadm : (p ≠ 0 → IsNilpotent (p : 𝓛.D)) ∧ (p = 0 → IsNilpotent (I.map 𝓛.i)) :=
    ⟨fun _ => by simpa using hn.map 𝓛.i, fun h => absurd h hp⟩
  exact ⟨chartL 𝓛 γ p δ hδ hadm c.affine 𝓛.et, hflat, fun i =>
    (RingHom.congr_fun (ev_thL 𝓛 γ p δ hδ hadm c.affine) (c.t i)).trans (𝓛.hT i)⟩

end GlobalTheory.CompanionTheory.ChartP
end
end
