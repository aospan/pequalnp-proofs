import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_745

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

def dot {n : ℕ} (x y : Vec n) : F := ∑ i, x i*y i

lemma dot_comm {n : ℕ} (x y : Vec n) : dot x y=dot y x := by
  simp only [dot,mul_comm]

lemma dot_add {n : ℕ} (x y z : Vec n) : dot (x+y) z=dot x z+dot y z := by
  simp [dot,add_mul,Finset.sum_add_distrib]

lemma dot_smul {n : ℕ} (a : F) (x y : Vec n) : dot (a • x) y=a*dot x y := by
  simp [dot,Finset.mul_sum,mul_assoc]

lemma dot_single {n : ℕ} (x : Vec n) (i : Fin n) :
    dot x (Pi.single i 1)=x i := by
  simp [dot,Pi.single_apply,eq_comm]

lemma dot_separates {n : ℕ} (x : Vec n) (h : ∀ y,dot y x=0) : x=0 := by
  funext i
  have hi := h (Pi.single i 1)
  rw [dot_comm,dot_single] at hi
  exact hi

lemma vec_expand {n : ℕ} (x : Vec n) : ∑ i,x i • Pi.single i (1:F)=x := by
  funext j
  simp [Finset.sum_apply,Pi.single_apply]

lemma linear_eval {n : ℕ} (f : Vec n →ₗ[F] F) (x : Vec n) :
    f x=∑ i,x i*f (Pi.single i 1) := by
  conv_lhs => rw [←vec_expand x]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma separating {n m : ℕ} (L : Vec n →ₗ[F] Vec m)
    (h : ¬Function.Surjective L) :
    ∃ b : Vec m,b≠0 ∧ ∀ x,dot b (L x)=0 := by
  classical
  have hr : LinearMap.range L<⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    exact h (LinearMap.range_eq_top.mp he))
  obtain ⟨f,hf,hker⟩ := (LinearMap.range L).exists_le_ker_of_lt_top hr
  let b : Vec m := fun i => f (Pi.single i 1)
  have hb : b≠0 := by
    intro hz
    apply hf
    apply LinearMap.ext
    intro x
    rw [linear_eval]
    change (∑ i,x i*b i)=0
    rw [hz]
    simp
  refine ⟨b,hb,?_⟩
  intro x
  have hx : f (L x)=0 := hker (LinearMap.mem_range_self L x)
  rw [linear_eval] at hx
  simpa only [dot,mul_comm] using hx

variable {K : Type*} [Field K] [Algebra F K]

def basisBit {k s : ℕ} (coord : K ≃ₗ[F] Vec s) (j : Fin k) : K :=
  coord.symm (fun z => if z.val=j.val % s then 1 else 0)

def lift {k s : ℕ} (coord : K ≃ₗ[F] Vec s) (x : K) : Vec s →ₗ[F] Vec k where
  toFun y := fun j => dot y (coord (basisBit coord j*x^(j.val/s)))
  map_add' y z := by
    funext j
    exact dot_add _ _ _
  map_smul' a y := by
    funext j
    exact dot_smul _ _ _

noncomputable def packed {k s : ℕ} (coord : K ≃ₗ[F] Vec s) (a : Vec k) : Polynomial K :=
  ∑ j,Polynomial.monomial (j.val/s) (a j • basisBit coord j)

lemma packed_coordinate {k s : ℕ} (hs : 0<s) (coord : K ≃ₗ[F] Vec s)
    (a : Vec k) (i : Fin k) :
    coord ((packed coord a).coeff (i.val/s)) ⟨i.val % s,Nat.mod_lt _ hs⟩=a i := by
  classical
  simp only [packed,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,map_sum,Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [basisBit]
  · intro j hj hji
    by_cases hd : j.val/s=i.val/s
    · have hm : j.val % s≠i.val % s := by
        intro he
        apply hji
        apply Fin.ext
        have hi := Nat.mod_add_div i.val s
        have hj := Nat.mod_add_div j.val s
        rw [hd,he] at hj
        exact hj.symm.trans hi
      simp [hd,basisBit,hm,Ne.symm hm]
    · simp [hd,Ne.symm hd]
  · simp

lemma packed_ne_zero {k s : ℕ} (hs : 0<s) (coord : K ≃ₗ[F] Vec s)
    (a : Vec k) (ha : a≠0) : packed coord a≠0 := by
  intro hp
  apply ha
  funext i
  have hi := packed_coordinate hs coord a i
  rw [hp] at hi
  simpa using hi.symm

lemma packed_degree {k s : ℕ} (coord : K ≃ₗ[F] Vec s) (a : Vec k) :
    (packed coord a).natDegree≤(k-1)/s := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [packed,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  have hd : j.val/s≤(k-1)/s := Nat.div_le_div_right (by omega)
  have he : j.val/s≠n := by omega
  simp [he,Ne.symm he]

lemma root_count [DecidableEq K] {q : ℕ} (point : Fin q ≃ K) (p : Polynomial K) (hp : p≠0) :
    ((Finset.univ : Finset (Fin q)).filter (fun i => p.eval (point i)=0)).card≤p.natDegree := by
  classical
  let S := (Finset.univ : Finset (Fin q)).filter (fun i => p.eval (point i)=0)
  let Z := S.image point
  have hz : Z.val⊆p.roots := by
    intro x hx
    have hx' : x∈Z := hx
    change x∈S.image point at hx'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx'
    exact (Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp hi).2
  have hh := Polynomial.card_le_degree_of_subset_roots hz
  simpa only [Z,Finset.card_image_of_injective _ point.injective] using hh


lemma dot_add_right {n : ℕ} (x y z : Vec n) : dot x (y+z)=dot x y+dot x z := by
  simp [dot,mul_add,Finset.sum_add_distrib]

lemma dot_sub_right {n : ℕ} (x y z : Vec n) : dot x (y-z)=dot x y-dot x z := by
  simp [dot,mul_sub,Finset.sum_sub_distrib]

lemma dot_smul_right {n : ℕ} (a : F) (x y : Vec n) :
    dot x (a • y)=a*dot x y := by
  rw [dot_comm,dot_smul,dot_comm]

lemma basis_coord {s : ℕ} (coord : K ≃ₗ[F] Vec s) (i : Fin s) :
    coord (basisBit coord i)=Pi.single i 1 := by
  funext z
  simp [basisBit,Nat.mod_eq_of_lt i.isLt,Pi.single_apply,Fin.ext_iff,eq_comm]

lemma basis_expand {s : ℕ} (coord : K ≃ₗ[F] Vec s) (x : K) :
    ∑ i : Fin s,(coord x) i • basisBit coord i=x := by
  apply coord.injective
  rw [map_sum]
  simp_rw [map_smul,basis_coord]
  exact vec_expand (coord x)

lemma linear_zero_basis {s : ℕ} (coord : K ≃ₗ[F] Vec s) (f : K →ₗ[F] F)
    (h : ∀ i : Fin s,f (basisBit coord i)=0) : ∀ x,f x=0 := by
  intro x
  rw [←basis_expand coord x,map_sum]
  simp [h]

def pairMul {s : ℕ} (coord : K ≃ₗ[F] Vec s) (y : Vec s) (z : K) : K →ₗ[F] F where
  toFun x := dot y (coord (x*z))
  map_add' x w := by rw [add_mul,map_add,dot_add_right]
  map_smul' a x := by
    change dot y (coord ((a • x)*z))=a*dot y (coord (x*z))
    rw [smul_mul_assoc,map_smul,dot_smul_right]

lemma kill_basis {s : ℕ} (coord : K ≃ₗ[F] Vec s) (y : Vec s) (z : K) (hz : z≠0)
    (h : ∀ i : Fin s,pairMul coord y z (basisBit coord i)=0) : y=0 := by
  have hh := linear_zero_basis coord (pairMul coord y z) h
  apply dot_separates
  intro v
  have hv := hh (coord.symm v/z)
  change dot y (coord ((coord.symm v/z)*z))=0 at hv
  rw [div_mul_cancel₀ _ hz,LinearEquiv.apply_symm_apply] at hv
  simpa only [dot_comm] using hv

lemma lift_first {k s : ℕ} (hs : 0<s) (hks : s≤k) (coord : K ≃ₗ[F] Vec s)
    (x : K) (y : Vec s) (i : Fin s) :
    lift (k := k) coord x y ⟨i.val,lt_of_lt_of_le i.isLt hks⟩=y i := by
  change dot y (coord (basisBit coord (⟨i.val,_⟩ : Fin k)*x^(i.val/s)))=y i
  rw [Nat.div_eq_of_lt i.isLt,pow_zero,mul_one]
  have hb : basisBit coord (⟨i.val,lt_of_lt_of_le i.isLt hks⟩ : Fin k)=basisBit coord i := rfl
  rw [hb,basis_coord,dot_single]

lemma lift_second {k s : ℕ} (hs : 0<s) (hks : 2*s≤k) (coord : K ≃ₗ[F] Vec s)
    (x : K) (y : Vec s) (i : Fin s) :
    lift (k := k) coord x y ⟨s+i.val,by omega⟩=dot y (coord (basisBit coord i*x)) := by
  change dot y (coord (basisBit coord (⟨s+i.val,_⟩ : Fin k)*x^((s+i.val)/s)))=_
  have hb : basisBit coord (⟨s+i.val,by omega⟩ : Fin k)=basisBit coord i := by
    simp only [basisBit,Nat.add_mod_left]
  rw [hb,Nat.add_div_left _ hs,Nat.div_eq_of_lt i.isLt,zero_add,pow_one]

lemma masks_injective {k s q m : ℕ} (hs : 0<s) (hks : 2*s≤k)
    (point : Fin q ≃ K) (coord : K ≃ₗ[F] Vec s) (inner : Fin m ↪ Vec s)
    (hnz : ∀ i,inner i≠0) :
    Function.Injective (fun u : Fin q × Fin m => lift (k := k) coord (point u.1) (inner u.2)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ he
  have hy : inner a=inner b := by
    funext z
    have hh := congrFun he (⟨z.val,by omega⟩ : Fin k)
    simpa only [lift_first (k:=k) hs (by omega) coord] using hh
  have hab := inner.injective hy
  subst b
  have hp : point i=point j := by
    by_contra hne
    apply hnz a
    apply kill_basis coord (inner a) (point i-point j) (sub_ne_zero.mpr hne)
    intro z
    have hh := congrFun he (⟨s+z.val,by omega⟩ : Fin k)
    simp only [lift_second hs hks coord] at hh
    change dot (inner a) (coord (basisBit coord z*(point i-point j)))=0
    rw [mul_sub,map_sub,dot_sub_right,hh,sub_self]
  exact Prod.ext (point.injective hp) rfl


lemma dot_sum_right {n : ℕ} {ι : Type*} (S : Finset ι) (x : Vec n) (z : ι → Vec n) :
    dot x (∑ i ∈ S,z i)=∑ i ∈ S,dot x (z i) := by
  simp only [dot,Finset.sum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma packed_eval {k s : ℕ} (coord : K ≃ₗ[F] Vec s) (f : Vec k →ₗ[F] F)
    (x : K) (y : Vec s) :
    f (lift (k:=k) coord x y)=
      dot y (coord ((packed coord (fun j => f (Pi.single j 1))).eval x)) := by
  classical
  rw [linear_eval]
  simp only [packed,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    smul_mul_assoc,map_sum,map_smul,dot_sum_right,dot_smul_right]
  apply Finset.sum_congr rfl
  intro j hj
  change dot y (coord (basisBit coord j*x^(j.val/s)))*f (Pi.single j 1)=_
  exact mul_comm _ _

lemma linear_coeff_ne_zero {n : ℕ} (f : Vec n →ₗ[F] F) (hf : f≠0) :
    (fun i => f (Pi.single i 1))≠0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro x
  rw [linear_eval]
  change (∑ i,x i*(fun j => f (Pi.single j 1)) i)=0
  rw [h]
  simp

def rowTest {r : ℕ} (b : Vec r) : Vec r →ₗ[F] F where
  toFun x := dot b x
  map_add' x y := dot_add_right _ _ _
  map_smul' a x := dot_smul_right _ _ _

lemma test_comp_ne_zero {k r : ℕ} (A : Vec k →ₗ[F] Vec r) (hA : Function.Surjective A)
    (b : Vec r) (hb : b≠0) : (rowTest b).comp A≠0 := by
  intro hf
  apply hb
  apply dot_separates
  intro y
  obtain ⟨x,rfl⟩ := hA y
  have hx := congrArg (fun f : Vec k →ₗ[F] F => f x) hf
  simpa only [LinearMap.comp_apply,rowTest,LinearMap.coe_mk,AddHom.coe_mk,
    LinearMap.zero_apply,dot_comm] using hx


lemma lift_fibers {k s r q m : ℕ} (hs : 0<s)
    (point : Fin q ≃ K) (coord : K ≃ₗ[F] Vec s) (inner : Fin m ↪ Vec s)
    (d : ℕ)
    (hinner : ∀ L : Vec s →ₗ[F] Vec r,Function.Surjective L → ∀ t,
      d≤((Finset.univ : Finset (Fin m)).filter (fun i => L (inner i)=t)).card) :
    ∀ (A : Vec k →ₗ[F] Vec r),Function.Surjective A → ∀ t,
      (q-(2^r-1)*((k-1)/s))*d ≤
        ((Finset.univ : Finset (Fin q × Fin m)).filter
          (fun u => A (lift (k:=k) coord (point u.1) (inner u.2))=t)).card := by
  classical
  intro A hA t
  let D := (k-1)/s
  let f : Vec r → (Vec k →ₗ[F] F) := fun b => (rowTest b).comp A
  let P : Vec r → Polynomial K := fun b => packed coord (fun j => f b (Pi.single j 1))
  let B := (Finset.univ : Finset (Vec r)).erase 0
  let badFor : Vec r → Finset (Fin q) := fun b =>
    Finset.univ.filter (fun u => (P b).eval (point u)=0)
  let bad := B.biUnion badFor
  let good := (Finset.univ : Finset (Fin q)) \ bad
  have hBcard : B.card=2^r-1 := by simp [B,Vec,F]
  have hbad : bad.card≤(2^r-1)*D := by
    calc
      bad.card ≤ ∑ b ∈ B,(badFor b).card := Finset.card_biUnion_le
      _ ≤ ∑ b ∈ B,D := by
        apply Finset.sum_le_sum
        intro b hb
        have hbnz : b≠0 := (Finset.mem_erase.mp hb).1
        have hf : f b≠0 := test_comp_ne_zero A hA b hbnz
        have hp : P b≠0 := packed_ne_zero hs coord _ (linear_coeff_ne_zero (f b) hf)
        exact (root_count point (P b) hp).trans (packed_degree coord _)
      _ = (2^r-1)*D := by simp [hBcard]
  have hgood : q-(2^r-1)*D≤good.card := by
    have hc : good.card+bad.card=q := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
      simpa only [Finset.card_univ,Fintype.card_fin] using hh
    omega
  have hsurj : ∀ u∈good,Function.Surjective (A.comp (lift (k:=k) coord (point u))) := by
    intro u hu
    by_contra hn
    obtain ⟨b,hbnz,hkill⟩ := separating (A.comp (lift (k:=k) coord (point u))) hn
    have hroot : (P b).eval (point u)=0 := by
      have hv : coord ((P b).eval (point u))=0 := by
        apply dot_separates
        intro y
        change dot y (coord ((packed coord (fun j => f b (Pi.single j 1))).eval (point u)))=0
        rw [←packed_eval]
        exact hkill y
      apply coord.injective
      simpa only [map_zero] using hv
    have humem : u∈bad := Finset.mem_biUnion.mpr
      ⟨b,Finset.mem_erase.mpr ⟨hbnz,Finset.mem_univ _⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot⟩⟩
    exact (Finset.mem_sdiff.mp hu).2 humem
  let fibers : Fin q → Finset (Fin m) := fun u => Finset.univ.filter
    (fun i => A (lift (k:=k) coord (point u) (inner i))=t)
  let S := (Finset.univ : Finset (Fin q × Fin m)).filter
    (fun u => A (lift (k:=k) coord (point u.1) (inner u.2))=t)
  have hfib : ∀ u∈good,d≤(fibers u).card := by
    intro u hu
    exact hinner (A.comp (lift (k:=k) coord (point u))) (hsurj u hu) t
  have htotal : S.card=∑ u : Fin q,(fibers u).card := by
    simp only [S,fibers,Finset.card_filter]
    exact Fintype.sum_prod_type _
  change (q-(2^r-1)*D)*d≤S.card
  calc
    (q-(2^r-1)*D)*d ≤ good.card*d := Nat.mul_le_mul_right d hgood
    _ = ∑ u ∈ good,d := by simp
    _ ≤ ∑ u ∈ good,(fibers u).card := Finset.sum_le_sum hfib
    _ ≤ ∑ u : Fin q,(fibers u).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
      intro u hu hnu
      exact Nat.zero_le _
    _ = S.card := htotal.symm


lemma solve : ∀ (k s r m d : ℕ), 0 < s → 2*s ≤ k → 0 < r →
  let F := ZMod 2
  let K := GaloisField 2 s
  let q := 2^s
  let V := Fin k → F
  let W := Fin s → F
  let R := Fin r → F
  ∀ (point : Fin q ≃ K) (coord : K ≃ₗ[F] W) (inner : Fin m ↪ W),
    (∀ i, inner i ≠ 0) →
    (∀ (A : W →ₗ[F] R), Function.Surjective A → ∀ t : R,
      d ≤ ((Finset.univ : Finset (Fin m)).filter (fun i => A (inner i) = t)).card) →
    let basisBit := fun j : Fin k => coord.symm
      (fun z : Fin s => if z.val = j.val  %  s then (1 : F) else 0)
    let mask := fun (u : Fin q × Fin m) (j : Fin k) =>
      ∑ z : Fin s, inner u.2 z * coord (basisBit j * (point u.1)^(j.val/s)) z
    Function.Injective mask ∧
      ∀ (A : V →ₗ[F] R), Function.Surjective A → ∀ t : R,
        (q-(2^r-1)*((k-1)/s))*d ≤
          ((Finset.univ : Finset (Fin q × Fin m)).filter (fun u => A (mask u) = t)).card := by
  intro k s r m d hs hks hr
  dsimp only
  intro point coord inner hnz hinner
  constructor
  · exact masks_injective hs hks point coord inner hnz
  · exact lift_fibers hs point coord inner d hinner

end PEqualNP.Outside.L_lib_745





theorem PEqualNP.Outside.L_lib_745 : ∀ (k s r m d : ℕ), 0 < s → 2*s ≤ k → 0 < r →
  let F := ZMod 2
  let K := GaloisField 2 s
  let q := 2^s
  let V := Fin k → F
  let W := Fin s → F
  let R := Fin r → F
  ∀ (point : Fin q ≃ K) (coord : K ≃ₗ[F] W) (inner : Fin m ↪ W),
    (∀ i, inner i ≠ 0) →
    (∀ (A : W →ₗ[F] R), Function.Surjective A → ∀ t : R,
      d ≤ ((Finset.univ : Finset (Fin m)).filter (fun i => A (inner i) = t)).card) →
    let basisBit := fun j : Fin k => coord.symm
      (fun z : Fin s => if z.val = j.val  %  s then (1 : F) else 0)
    let mask := fun (u : Fin q × Fin m) (j : Fin k) =>
      ∑ z : Fin s, inner u.2 z * coord (basisBit j * (point u.1)^(j.val/s)) z
    Function.Injective mask ∧
      ∀ (A : V →ₗ[F] R), Function.Surjective A → ∀ t : R,
        (q-(2^r-1)*((k-1)/s))*d ≤
          ((Finset.univ : Finset (Fin q × Fin m)).filter (fun u => A (mask u) = t)).card :=
  PEqualNP.Outside.L_lib_745.solve
