import PEqualNP.Defs
namespace PEqualNP.Outside.G550

abbrev B := BitVec 230
abbrev Sig := B × B
def top : B := BitVec.allOnes 230
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private lemma cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private lemma cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private lemma add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private lemma cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n=k-t then
    base == top && !(v.contains g) && g != zero && g != one && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && !(v.contains g) && g != zero && g != one && r (g::(h++rest)))

def before (a b : Sig) : Bool :=
  if a.1 = b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)


def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (unaryAt k t r v (coverage (decide (0<t)) v))

def binarySlow (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a,b] v
     let keep := [[],[a],[b],[a,b]]
     let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
     tryGate k t r v rest (v.length-2) mask (bin false a b) keep || tryGate k t r v rest (v.length-2) mask (bin true a b) keep)

def tightBinary (r : List Sig → Bool) (v : List Sig) (u : B) (a b : Sig) : Bool :=
  let ua := u &&& sep false a
  let ub := u &&& sep false b
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => !(v.contains g) && g != zero && g != one && r (g::rest)
  ((((ua &&& ~~~b.1) ||| (ub &&& ~~~a.1)) == 0) && use (bin false a b)) ||
    ((((ua &&& b.2) ||| (ub &&& a.2)) == 0) && use (bin true a b))

def binaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  if t=0 ∧ v.length-2=k then before a b && tightBinary r v c.2.1 a b
  else binarySlow k t r v c a b

private lemma need_unique (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_accept {k t r v c a b}
    (h : binarySlow k t r v c a b=true) : binaryAt k t r v c a b=true := by
  unfold binaryAt
  split
  · rename_i cut
    obtain ⟨rfl,hn⟩ := cut
    obtain ⟨ho,hs⟩ := Bool.and_eq_true_iff.mp h
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ho,?_⟩
    simp only [tryGate,Nat.sub_zero,hn,ite_true,Nat.lt_irrefl,decide_false,Bool.or_eq_true,Bool.and_eq_true,
      beq_iff_eq] at hs
    simp only [tightBinary,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
    rcases hs with z | z
    · exact Or.inl ⟨need_unique c a b false z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
    · exact Or.inr ⟨need_unique c a b true z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
  · exact h

private lemma fast_mono {k t v c a b} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hslow : binarySlow k t r v c a b=true → binarySlow k t s v c a b=true)
    (hr : binaryAt k t r v c a b=true) : binaryAt k t s v c a b=true := by
  by_cases hcut : t=0 ∧ v.length-2=k
  · simp only [binaryAt,if_pos hcut,tightBinary,Bool.and_eq_true,Bool.or_eq_true] at hr ⊢
    obtain ⟨order,z⟩ := hr
    refine ⟨order,?_⟩
    rcases z with ⟨p,hp,hr⟩ | ⟨p,hp,hr⟩
    · exact Or.inl ⟨p,hp,h _ hr⟩
    · exact Or.inr ⟨p,hp,h _ hr⟩
  · simpa only [binaryAt,if_neg hcut] using hslow (by simpa only [binaryAt,if_neg hcut] using hr)

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (fun a => v.any (binaryAt k t r v (coverage (decide (0<t)) v) a))

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v.contains target
  | k+1,t,v =>
    if t>k+1 ∨ v.length>k+1-t+1 then false else
    v.contains target ||
    (decide (0<t) && unaryMoves k (t-1) (search k (t-1)) v) ||
    binaryMoves k t (search k t) v

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



-- Each bit pairs a positive assignment with a negative assignment.
-- Compare every edge with every maximal independent set, and include every
-- pair differing in one input that changes the output.
def raw0 : Sig := (115478457080954056037453394747668900890542079539367533054012644393087,342706871257084338189840789416151144919874978179)
def raw1 : Sig := (317569808060959783239825063170417032207079789632502095288426184065023,101889822543360142233147356812988092719644558096769690302363720292916)
def raw2 : Sig := (1631191810494664325030262969332294976400208271111731510983355508195200,1617599891378858756659175189908624068653834474907802794782947967935818)
def raw3 : Sig := (460844121800212270233637832257143301152136334388534657222802694717440,839207324233821044425717380100740111061329143261226292923842447505)
def raw4 : Sig := (920233736265033656604588963427743302465695625593183719939909372346368,6424625880146283982389419029985064400558880239012792353621516)
def raw5 : Sig := (1725041672031623777660798884916283445852241026584883307485857052622848,1724594094792032406437105169026508119694255948749531363068444294231918)
def raw6 : Sig := (1725436583697192854395512441922243159983118384373961765628313673400320,1725436580269888769823093238810740677939302885883342771419405539408371)
def raw7 : Sig := (1725436586697640946858506367155023694986335491781853707997515255644160,1725436586697640946858323590159923637383226321834417638391163220082300)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
private def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧
      Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

private lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩
private lemma Live.unary {k t U a} (ha : proper a) (hf : neg a ∉ insert a U)
    (tail : Live k t (insert (neg a) U)) : Live (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hf,tail⟩
private lemma Live.binary {k t U a b d} (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hf : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
    Live (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩

private lemma Live.induction {motive : ∀ {k t S}, Live k t S → Prop}
    (stop : motive Live.stop)
    (unary : ∀ {k t U a} (ha : proper a) (hf : neg a ∉ insert a U)
      (tail : Live k t (insert (neg a) U)), motive tail → motive (Live.unary ha hf tail))
    (binary : ∀ {k t U a b d} (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)),
      motive tail → motive (Live.binary ha hb hab hf tail))
    {k t S} (h : Live k t S) : motive h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induction with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.induction with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 230
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 230 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 230
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 230 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 230)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 230) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using Live.induction with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 230 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 230)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,ha,hp.1,hp.2,hr] at *
  · simp only [tryGate,if_neg tight,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,
      List.any_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨h,hh,⟨⟨⟨⟨hl,cov⟩,ha⟩,hp.1⟩,hp.2⟩,hr⟩

private lemma ordered {a b : Sig} (h : a≠b) : before a b = true ∨ before b a = true := by
  by_cases e : a.1=b.1
  · have h2 : a.2.toNat≠b.2.toNat := fun h2 => h (Prod.ext e (BitVec.eq_of_toNat_eq h2))
    simp [before,e]; omega
  · have h1 : a.1.toNat≠b.1.toNat := fun h1 => e (BitVec.eq_of_toNat_eq h1)
    simp [before,e,Ne.symm e]; omega

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → search k t v = true) :
    unaryMoves k t (search k t) v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (ord : before a b=true) (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → search k t v = true) :
    binaryMoves k t (search k t) v = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have ok := gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)
  apply List.any_eq_true.mpr
  refine ⟨a,ah,List.any_eq_true.mpr ⟨b,bh,fast_accept (Bool.and_eq_true_iff.mpr ⟨ord,?_⟩)⟩⟩
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  dsimp only
  rw [hlen,hmask]
  cases d
  · exact Bool.or_eq_true_iff.mpr (Or.inl ok)
  · exact Bool.or_eq_true_iff.mpr (Or.inr ok)

private lemma search_complete {m t S} (l : Live m t S) (K : Nat) (hle : m ≤ K)
    (v : List Sig) (hv : v.Nodup) (he : v.toFinset=S) : search K t v = true := by
  have size := live_size l
  rw [←he,List.toFinset_card_of_nodup hv] at size
  induction l using Live.induction generalizing K v with
  | stop =>
    have ht : v.contains target = true := List.contains_iff_mem.mpr (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    cases K with
    | zero => exact ht
    | succ k =>
      rw [search,if_neg (by omega),ht]
      rfl
  | @unary m t U a ha hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr; left
      apply Bool.or_eq_true_iff.mpr; right
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simp,unary_found hv he (by omega) hf tail ?_⟩
      intro w hn eq
      have sz := live_size tail
      rw [←eq,List.toFinset_card_of_nodup hn] at sz
      exact ih k (by omega) w hn eq sz
  | @binary m t U a b d ha hb hab hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr
      right
      have cont (w : List Sig) (hn : w.Nodup) (eq : w.toFinset=insert (bin d a b) U) : search k t w = true := by
        have sz := live_size tail
        rw [←eq,List.toFinset_card_of_nodup hn] at sz
        exact ih k (by omega) w hn eq sz
      rcases ordered hab with o | o
      · exact binary_found hv he (by omega) o hab hf tail cont
      · rw [Finset.insert_comm a b] at he hf
        rw [bin_comm d a b] at hf tail cont
        exact binary_found hv he (by omega) o hab.symm hf tail cont
open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 230) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 230).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]

def sample (s : Bool) (i : Fin 230) (j : Fin 8) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 0 && x 7)

private lemma sample_ok : ∀ (s : Bool) (i : Fin 230), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 10)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 10 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=8 := rfl
  change C.gates.length ≤ 10 at hc
  exact ⟨t,by omega,search_complete ht 10 (by omega) raw raw_nd eq⟩
-- A finite list of rejected successor states can be reused by the checker.
-- The closed Boolean check verifies that the list covers every enabled move.
def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
  v.contains target || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

private lemma try_mono {k t v rest n c g opts} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : tryGate k t r v rest n c g opts = true) : tryGate k t s v rest n c g opts = true := by
  by_cases tight : n=k-t
  · simp only [tryGate,if_pos tight,Bool.and_eq_true] at hr ⊢
    exact ⟨hr.1,h _ hr.2⟩
  · simp only [tryGate,if_neg tight,Bool.and_eq_true,List.any_eq_true] at hr ⊢
    obtain ⟨a,ha,hc,hit⟩ := hr
    exact ⟨a,ha,hc,h _ hit⟩

private lemma umove_mono {k t v} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : unaryMoves k t r v = true) : unaryMoves k t s v = true := by
  obtain ⟨a,ha,move⟩ := List.any_eq_true.mp hr
  exact List.any_eq_true.mpr ⟨a,ha,try_mono h move⟩

private lemma bmove_mono {k t v} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hr : binaryMoves k t r v = true) : binaryMoves k t s v = true := by
  obtain ⟨a,ha,m⟩ := List.any_eq_true.mp hr
  obtain ⟨b,hb,z⟩ := List.any_eq_true.mp m
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,fast_mono h ?_ z⟩⟩
  intro slow
  obtain ⟨o,w⟩ := Bool.and_eq_true_iff.mp slow
  apply Bool.and_eq_true_iff.mpr
  refine ⟨o,?_⟩
  rcases Bool.or_eq_true_iff.mp w with p | p
  · exact Bool.or_eq_true_iff.mpr (Or.inl (try_mono h p))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (try_mono h p))

private lemma reject_step (k t : Nat) (v : List Sig) (U A : List (List Sig))
    (hu : ∀ w ∈ U, search k (t-1) w = false)
    (hb : ∀ w ∈ A, search k t w = false)
    (hc : stepTest k t v (fun w => !(U.contains w)) (fun w => !(A.contains w)) = false) :
    search (k+1) t v = false := by
  cases ht : search (k+1) t v with
  | false => rfl
  | true =>
    exfalso
    have mono (n : Nat) (L : List (List Sig)) (hL : ∀ w ∈ L, search k n w=false) (w : List Sig)
        (hp : search k n w=true) : !(L.contains w) = true := by
      have hn : w ∉ L := fun hm => by have eq := hL _ hm; simp [hp] at eq
      simp [List.contains_eq_mem,hn]
    simp only [search] at ht
    unfold stepTest at hc
    split at ht
    · contradiction
    next hn =>
      rw [if_neg hn] at hc
      apply Bool.noConfusion (show false = true from hc.symm.trans ?_)
      rcases Bool.or_eq_true_iff.mp ht with a | b
      · rcases Bool.or_eq_true_iff.mp a with hit | u
        · exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hit)))
        · obtain ⟨hn,p⟩ := Bool.and_eq_true_iff.mp u
          exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr
            (Or.inr (Bool.and_eq_true_iff.mpr ⟨hn,umove_mono (mono _ U hu) p⟩))))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (bmove_mono (mono _ A hb) b))


private def w8 : Sig := bin false raw0 raw1

private def v1 : List Sig := [w8,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v1 : search 9 0 v1 = false := by decide +kernel

private def w9 : Sig := bin true raw0 raw1

private def v2 : List Sig := [w9,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v2 : search 9 0 v2 = false := by decide +kernel

private def w10 : Sig := bin false raw0 raw2

private def v3 : List Sig := [w10,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v3 : search 9 0 v3 = false := by decide +kernel

private def w11 : Sig := bin true raw0 raw2

private def v4 : List Sig := [w11,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v4 : search 9 0 v4 = false := by decide +kernel

private def w12 : Sig := bin false raw0 raw3

private def v5 : List Sig := [w12,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v5 : search 9 0 v5 = false := by decide +kernel

private def w13 : Sig := bin true raw0 raw3

private def v6 : List Sig := [w13,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v6 : search 9 0 v6 = false := by decide +kernel

private def w14 : Sig := bin false raw0 raw4

private def v7 : List Sig := [w14,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v7 : search 9 0 v7 = false := by decide +kernel

private def w15 : Sig := bin true raw0 raw4

private def v8 : List Sig := [w15,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v8 : search 9 0 v8 = false := by decide +kernel

private def w16 : Sig := bin false raw0 raw5

private def v9 : List Sig := [w16,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v9 : search 9 0 v9 = false := by decide +kernel

private def w17 : Sig := bin true raw0 raw5

private def v10 : List Sig := [w17,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v10 : search 9 0 v10 = false := by decide +kernel

private def w18 : Sig := bin false raw0 raw6

private def v11 : List Sig := [w18,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v11 : search 9 0 v11 = false := by decide +kernel

private def w19 : Sig := bin true raw0 raw6

private def v12 : List Sig := [w19,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

private def w20 : Sig := bin false w19 raw7

private def v13 : List Sig := [w20,w19,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v13 : search 8 0 v13 = false := by decide +kernel

private def v14 : List Sig := [w20,w19,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v14 : search 8 0 v14 = false := by decide +kernel

private def w21 : Sig := bin true w19 raw7

private def v15 : List Sig := [w21,w19,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v15 : search 8 0 v15 = false := by decide +kernel

private def v16 : List Sig := [w8,raw0,raw1,w19,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v16 : search 8 0 v16 = false := by decide +kernel

private def v17 : List Sig := [w9,raw0,raw1,w19,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v17 : search 8 0 v17 = false := by decide +kernel

private def v18 : List Sig := [w10,raw0,raw2,w19,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v18 : search 8 0 v18 = false := by decide +kernel

private def v19 : List Sig := [w11,raw0,raw2,w19,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v19 : search 8 0 v19 = false := by decide +kernel

private def v20 : List Sig := [w12,raw0,raw3,w19,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v20 : search 8 0 v20 = false := by decide +kernel

private def v21 : List Sig := [w13,raw0,raw3,w19,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v21 : search 8 0 v21 = false := by decide +kernel

private def v22 : List Sig := [w14,raw0,raw4,w19,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v22 : search 8 0 v22 = false := by decide +kernel

private def v23 : List Sig := [w15,raw4,w19,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v23 : search 8 0 v23 = false := by decide +kernel

private def v24 : List Sig := [w15,raw0,raw4,w19,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v24 : search 8 0 v24 = false := by decide +kernel

private def v25 : List Sig := [w16,raw0,raw5,w19,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v25 : search 8 0 v25 = false := by decide +kernel

private def v26 : List Sig := [w17,raw0,raw5,w19,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v26 : search 8 0 v26 = false := by decide +kernel

private def w22 : Sig := bin false raw0 raw7

private def v27 : List Sig := [w22,raw0,w19,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v27 : search 8 0 v27 = false := by decide +kernel

private def v28 : List Sig := [w22,raw0,raw7,w19,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v28 : search 8 0 v28 = false := by decide +kernel

private def w23 : Sig := bin true raw0 raw7

private def v29 : List Sig := [w23,raw0,raw7,w19,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v29 : search 8 0 v29 = false := by decide +kernel

private def w24 : Sig := bin false raw1 w19

private def v30 : List Sig := [w24,raw1,w19,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v30 : search 8 0 v30 = false := by decide +kernel

private def w25 : Sig := bin true raw1 w19

private def v31 : List Sig := [w25,raw1,w19,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v31 : search 8 0 v31 = false := by decide +kernel

private def w26 : Sig := bin false raw1 raw2

private def v32 : List Sig := [w26,raw1,raw2,w19,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v32 : search 8 0 v32 = false := by decide +kernel

private def w27 : Sig := bin true raw1 raw2

private def v33 : List Sig := [w27,raw1,raw2,w19,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v33 : search 8 0 v33 = false := by decide +kernel

private def w28 : Sig := bin false raw1 raw3

private def v34 : List Sig := [w28,raw1,raw3,w19,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v34 : search 8 0 v34 = false := by decide +kernel

private def w29 : Sig := bin true raw1 raw3

private def v35 : List Sig := [w29,raw1,raw3,w19,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v35 : search 8 0 v35 = false := by decide +kernel

private def w30 : Sig := bin false raw1 raw4

private def v36 : List Sig := [w30,raw1,raw4,w19,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v36 : search 8 0 v36 = false := by decide +kernel

private def w31 : Sig := bin true raw1 raw4

private def v37 : List Sig := [w31,raw1,raw4,w19,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v37 : search 8 0 v37 = false := by decide +kernel

private def w32 : Sig := bin false raw1 raw5

private def v38 : List Sig := [w32,raw1,raw5,w19,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v38 : search 8 0 v38 = false := by decide +kernel

private def w33 : Sig := bin true raw1 raw5

private def v39 : List Sig := [w33,raw1,raw5,w19,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v39 : search 8 0 v39 = false := by decide +kernel

private def w34 : Sig := bin false raw1 raw7

private def v40 : List Sig := [w34,raw1,raw7,w19,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v40 : search 8 0 v40 = false := by decide +kernel

private def w35 : Sig := bin true raw1 raw7

private def v41 : List Sig := [w35,raw1,w19,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v41 : search 8 0 v41 = false := by decide +kernel

private def v42 : List Sig := [w35,raw1,raw7,w19,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v42 : search 8 0 v42 = false := by decide +kernel

private def w36 : Sig := bin false raw2 w19

private def v43 : List Sig := [w36,raw2,w19,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v43 : search 8 0 v43 = false := by decide +kernel

private def w37 : Sig := bin true raw2 w19

private def v44 : List Sig := [w37,raw2,w19,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v44 : search 8 0 v44 = false := by decide +kernel

private def w38 : Sig := bin false raw2 raw5

private def v45 : List Sig := [w38,raw2,raw5,w19,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v45 : search 8 0 v45 = false := by decide +kernel

private def w39 : Sig := bin true raw2 raw5

private def v46 : List Sig := [w39,raw2,w19,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v46 : search 8 0 v46 = false := by decide +kernel

private def v47 : List Sig := [w39,raw2,raw5,w19,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v47 : search 8 0 v47 = false := by decide +kernel

private def w40 : Sig := bin false raw2 raw7

private def v48 : List Sig := [w40,raw2,raw7,w19,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v48 : search 8 0 v48 = false := by decide +kernel

private def w41 : Sig := bin true raw2 raw7

private def v49 : List Sig := [w41,raw2,raw7,w19,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v49 : search 8 0 v49 = false := by decide +kernel

private def w42 : Sig := bin false raw3 w19

private def v50 : List Sig := [w42,raw3,w19,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v50 : search 8 0 v50 = false := by decide +kernel

private def w43 : Sig := bin true raw3 w19

private def v51 : List Sig := [w43,raw3,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v51 : search 8 0 v51 = false := by decide +kernel

private def v52 : List Sig := [w43,raw3,w19,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v52 : search 8 0 v52 = false := by decide +kernel

private def w44 : Sig := bin false raw3 raw2

private def v53 : List Sig := [w44,raw3,raw2,w19,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v53 : search 8 0 v53 = false := by decide +kernel

private def w45 : Sig := bin true raw3 raw2

private def v54 : List Sig := [w45,raw3,raw2,w19,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v54 : search 8 0 v54 = false := by decide +kernel

private def w46 : Sig := bin false raw3 raw4

private def v55 : List Sig := [w46,raw3,raw4,w19,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v55 : search 8 0 v55 = false := by decide +kernel

private def w47 : Sig := bin true raw3 raw4

private def v56 : List Sig := [w47,raw3,raw4,w19,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v56 : search 8 0 v56 = false := by decide +kernel

private def w48 : Sig := bin false raw3 raw5

private def v57 : List Sig := [w48,raw3,w19,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v57 : search 8 0 v57 = false := by decide +kernel

private def v58 : List Sig := [w48,raw3,raw5,w19,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v58 : search 8 0 v58 = false := by decide +kernel

private def w49 : Sig := bin true raw3 raw5

private def v59 : List Sig := [w49,raw3,raw5,w19,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v59 : search 8 0 v59 = false := by decide +kernel

private def w50 : Sig := bin false raw3 raw7

private def v60 : List Sig := [w50,raw3,raw7,w19,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v60 : search 8 0 v60 = false := by decide +kernel

private def w51 : Sig := bin true raw3 raw7

private def v61 : List Sig := [w51,raw3,raw7,w19,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v61 : search 8 0 v61 = false := by decide +kernel

private def w52 : Sig := bin false raw4 w19

private def v62 : List Sig := [w52,raw4,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v62 : search 8 0 v62 = false := by decide +kernel

private def v63 : List Sig := [w52,raw4,w19,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v63 : search 8 0 v63 = false := by decide +kernel

private def w53 : Sig := bin true raw4 w19

private def v64 : List Sig := [w53,raw4,w19,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v64 : search 8 0 v64 = false := by decide +kernel

private def w54 : Sig := bin false raw4 raw2

private def v65 : List Sig := [w54,raw4,raw2,w19,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v65 : search 8 0 v65 = false := by decide +kernel

private def w55 : Sig := bin true raw4 raw2

private def v66 : List Sig := [w55,raw4,raw2,w19,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v66 : search 8 0 v66 = false := by decide +kernel

private def w56 : Sig := bin false raw4 raw5

private def v67 : List Sig := [w56,raw4,raw5,w19,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v67 : search 8 0 v67 = false := by decide +kernel

private def w57 : Sig := bin true raw4 raw5

private def v68 : List Sig := [w57,raw4,w19,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v68 : search 8 0 v68 = false := by decide +kernel

private def v69 : List Sig := [w57,raw4,raw5,w19,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v69 : search 8 0 v69 = false := by decide +kernel

private def w58 : Sig := bin false raw4 raw7

private def v70 : List Sig := [w58,raw4,raw7,w19,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v70 : search 8 0 v70 = false := by decide +kernel

private def w59 : Sig := bin true raw4 raw7

private def v71 : List Sig := [w59,raw4,w19,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v71 : search 8 0 v71 = false := by decide +kernel

private def v72 : List Sig := [w59,raw4,raw7,w19,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v72 : search 8 0 v72 = false := by decide +kernel

private def w60 : Sig := bin false raw5 w19

private def v73 : List Sig := [w60,raw5,w19,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v73 : search 8 0 v73 = false := by decide +kernel

private def w61 : Sig := bin true raw5 w19

private def v74 : List Sig := [w61,raw5,w19,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v74 : search 8 0 v74 = false := by decide +kernel

private def w62 : Sig := bin false raw5 raw7

private def v75 : List Sig := [w62,raw5,raw7,w19,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v75 : search 8 0 v75 = false := by decide +kernel

private def w63 : Sig := bin true raw5 raw7

private def v76 : List Sig := [w63,raw5,raw7,w19,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v76 : search 8 0 v76 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v12 : search 9 0 v12 = false := by
  apply reject_step 8 0 v12 [] [v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v33,v34,v35,v36,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v13
    · exact no_8_0_v14
    · exact no_8_0_v15
    · exact no_8_0_v16
    · exact no_8_0_v17
    · exact no_8_0_v18
    · exact no_8_0_v19
    · exact no_8_0_v20
    · exact no_8_0_v21
    · exact no_8_0_v22
    · exact no_8_0_v23
    · exact no_8_0_v24
    · exact no_8_0_v25
    · exact no_8_0_v26
    · exact no_8_0_v27
    · exact no_8_0_v28
    · exact no_8_0_v29
    · exact no_8_0_v30
    · exact no_8_0_v31
    · exact no_8_0_v32
    · exact no_8_0_v33
    · exact no_8_0_v34
    · exact no_8_0_v35
    · exact no_8_0_v36
    · exact no_8_0_v37
    · exact no_8_0_v38
    · exact no_8_0_v39
    · exact no_8_0_v40
    · exact no_8_0_v41
    · exact no_8_0_v42
    · exact no_8_0_v43
    · exact no_8_0_v44
    · exact no_8_0_v45
    · exact no_8_0_v46
    · exact no_8_0_v47
    · exact no_8_0_v48
    · exact no_8_0_v49
    · exact no_8_0_v50
    · exact no_8_0_v51
    · exact no_8_0_v52
    · exact no_8_0_v53
    · exact no_8_0_v54
    · exact no_8_0_v55
    · exact no_8_0_v56
    · exact no_8_0_v57
    · exact no_8_0_v58
    · exact no_8_0_v59
    · exact no_8_0_v60
    · exact no_8_0_v61
    · exact no_8_0_v62
    · exact no_8_0_v63
    · exact no_8_0_v64
    · exact no_8_0_v65
    · exact no_8_0_v66
    · exact no_8_0_v67
    · exact no_8_0_v68
    · exact no_8_0_v69
    · exact no_8_0_v70
    · exact no_8_0_v71
    · exact no_8_0_v72
    · exact no_8_0_v73
    · exact no_8_0_v74
    · exact no_8_0_v75
    · exact no_8_0_v76
  · decide +kernel

private def v77 : List Sig := [w19,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v77 : search 9 0 v77 = false := by decide +kernel

private def v78 : List Sig := [w22,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

private def w64 : Sig := bin false w22 raw1

private def v79 : List Sig := [w64,w22,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v79 : search 8 0 v79 = false := by decide +kernel

private def w65 : Sig := bin true w22 raw1

private def v80 : List Sig := [w65,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v80 : search 8 0 v80 = false := by decide +kernel

private def v81 : List Sig := [w65,w22,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v81 : search 8 0 v81 = false := by decide +kernel

private def v82 : List Sig := [w65,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v82 : search 8 0 v82 = false := by decide +kernel

private def v83 : List Sig := [w65,w22,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v83 : search 8 0 v83 = false := by decide +kernel

private def w66 : Sig := bin false w22 raw2

private def v84 : List Sig := [w66,w22,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v84 : search 8 0 v84 = false := by decide +kernel

private def w67 : Sig := bin true w22 raw2

private def v85 : List Sig := [w67,w22,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v85 : search 8 0 v85 = false := by decide +kernel

private def v86 : List Sig := [w67,w22,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v86 : search 8 0 v86 = false := by decide +kernel

private def w68 : Sig := bin false w22 raw3

private def v87 : List Sig := [w68,w22,raw3,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v87 : search 8 0 v87 = false := by decide +kernel

private def w69 : Sig := bin true w22 raw3

private def v88 : List Sig := [w69,w22,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v88 : search 8 0 v88 = false := by decide +kernel

private def v89 : List Sig := [w69,w22,raw3,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v89 : search 8 0 v89 = false := by decide +kernel

private def w70 : Sig := bin false w22 raw4

private def v90 : List Sig := [w70,w22,raw4,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v90 : search 8 0 v90 = false := by decide +kernel

private def w71 : Sig := bin true w22 raw4

private def v91 : List Sig := [w71,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v91 : search 8 0 v91 = false := by decide +kernel

private def v92 : List Sig := [w71,w22,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v92 : search 8 0 v92 = false := by decide +kernel

private def v93 : List Sig := [w71,raw4,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v93 : search 8 0 v93 = false := by decide +kernel

private def v94 : List Sig := [w71,w22,raw4,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v94 : search 8 0 v94 = false := by decide +kernel

private def w72 : Sig := bin false w22 raw5

private def v95 : List Sig := [w72,w22,raw5,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v95 : search 8 0 v95 = false := by decide +kernel

private def w73 : Sig := bin true w22 raw5

private def v96 : List Sig := [w73,w22,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v96 : search 8 0 v96 = false := by decide +kernel

private def v97 : List Sig := [w73,w22,raw5,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v97 : search 8 0 v97 = false := by decide +kernel

private def w74 : Sig := bin false w22 raw6

private def v98 : List Sig := [w74,w22,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v98 : search 8 0 v98 = false := by decide +kernel

private def w75 : Sig := bin true w22 raw6

private def v99 : List Sig := [w75,w22,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v99 : search 8 0 v99 = false := by decide +kernel

private def v100 : List Sig := [w75,w22,raw6,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v100 : search 8 0 v100 = false := by decide +kernel

private def v101 : List Sig := [w8,raw0,raw1,w22,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v101 : search 8 0 v101 = false := by decide +kernel

private def v102 : List Sig := [w9,raw0,raw1,w22,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v102 : search 8 0 v102 = false := by decide +kernel

private def v103 : List Sig := [w10,raw0,raw2,w22,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v103 : search 8 0 v103 = false := by decide +kernel

private def v104 : List Sig := [w11,raw0,raw2,w22,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v104 : search 8 0 v104 = false := by decide +kernel

private def v105 : List Sig := [w12,raw0,raw3,w22,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v105 : search 8 0 v105 = false := by decide +kernel

private def v106 : List Sig := [w13,raw0,raw3,w22,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v106 : search 8 0 v106 = false := by decide +kernel

private def v107 : List Sig := [w14,raw0,raw4,w22,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v107 : search 8 0 v107 = false := by decide +kernel

private def v108 : List Sig := [w15,raw0,raw4,w22,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v108 : search 8 0 v108 = false := by decide +kernel

private def v109 : List Sig := [w16,raw0,raw5,w22,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v109 : search 8 0 v109 = false := by decide +kernel

private def v110 : List Sig := [w17,raw0,raw5,w22,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v110 : search 8 0 v110 = false := by decide +kernel

private def v111 : List Sig := [w18,raw0,raw6,w22,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v111 : search 8 0 v111 = false := by decide +kernel

private def v112 : List Sig := [w19,raw0,w22,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v112 : search 8 0 v112 = false := by decide +kernel

private def v113 : List Sig := [w19,raw0,raw6,w22,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v113 : search 8 0 v113 = false := by decide +kernel

private def v114 : List Sig := [w26,raw1,raw2,w22,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v114 : search 8 0 v114 = false := by decide +kernel

private def v115 : List Sig := [w27,raw1,raw2,w22,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v115 : search 8 0 v115 = false := by decide +kernel

private def v116 : List Sig := [w28,raw1,raw3,w22,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v116 : search 8 0 v116 = false := by decide +kernel

private def v117 : List Sig := [w29,raw1,raw3,w22,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v117 : search 8 0 v117 = false := by decide +kernel

private def v118 : List Sig := [w30,raw1,raw4,w22,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v118 : search 8 0 v118 = false := by decide +kernel

private def v119 : List Sig := [w31,raw1,raw4,w22,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v119 : search 8 0 v119 = false := by decide +kernel

private def v120 : List Sig := [w32,raw1,raw5,w22,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v120 : search 8 0 v120 = false := by decide +kernel

private def v121 : List Sig := [w33,raw1,raw5,w22,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v121 : search 8 0 v121 = false := by decide +kernel

private def w76 : Sig := bin false raw1 raw6

private def v122 : List Sig := [w76,raw1,raw6,w22,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v122 : search 8 0 v122 = false := by decide +kernel

private def w77 : Sig := bin true raw1 raw6

private def v123 : List Sig := [w77,raw1,raw6,w22,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v123 : search 8 0 v123 = false := by decide +kernel

private def v124 : List Sig := [w38,raw2,raw5,w22,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v124 : search 8 0 v124 = false := by decide +kernel

private def v125 : List Sig := [w39,raw2,w22,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v125 : search 8 0 v125 = false := by decide +kernel

private def v126 : List Sig := [w39,raw2,raw5,w22,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v126 : search 8 0 v126 = false := by decide +kernel

private def w78 : Sig := bin false raw2 raw6

private def v127 : List Sig := [w78,raw2,raw6,w22,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v127 : search 8 0 v127 = false := by decide +kernel

private def w79 : Sig := bin true raw2 raw6

private def v128 : List Sig := [w79,raw2,raw6,w22,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v128 : search 8 0 v128 = false := by decide +kernel

private def v129 : List Sig := [w44,raw3,raw2,w22,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v129 : search 8 0 v129 = false := by decide +kernel

private def v130 : List Sig := [w45,raw3,raw2,w22,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v130 : search 8 0 v130 = false := by decide +kernel

private def v131 : List Sig := [w46,raw3,raw4,w22,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v131 : search 8 0 v131 = false := by decide +kernel

private def v132 : List Sig := [w47,raw3,raw4,w22,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v132 : search 8 0 v132 = false := by decide +kernel

private def v133 : List Sig := [w48,raw3,w22,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v133 : search 8 0 v133 = false := by decide +kernel

private def v134 : List Sig := [w48,raw3,raw5,w22,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v134 : search 8 0 v134 = false := by decide +kernel

private def v135 : List Sig := [w49,raw3,raw5,w22,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v135 : search 8 0 v135 = false := by decide +kernel

private def w80 : Sig := bin false raw3 raw6

private def v136 : List Sig := [w80,raw3,raw6,w22,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v136 : search 8 0 v136 = false := by decide +kernel

private def w81 : Sig := bin true raw3 raw6

private def v137 : List Sig := [w81,raw3,w22,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v137 : search 8 0 v137 = false := by decide +kernel

private def v138 : List Sig := [w81,raw3,raw6,w22,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v138 : search 8 0 v138 = false := by decide +kernel

private def v139 : List Sig := [w54,raw4,raw2,w22,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v139 : search 8 0 v139 = false := by decide +kernel

private def v140 : List Sig := [w55,raw4,raw2,w22,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v140 : search 8 0 v140 = false := by decide +kernel

private def v141 : List Sig := [w56,raw4,raw5,w22,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v141 : search 8 0 v141 = false := by decide +kernel

private def v142 : List Sig := [w57,raw4,w22,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v142 : search 8 0 v142 = false := by decide +kernel

private def v143 : List Sig := [w57,raw4,raw5,w22,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v143 : search 8 0 v143 = false := by decide +kernel

private def w82 : Sig := bin false raw4 raw6

private def v144 : List Sig := [w82,raw4,w22,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v144 : search 8 0 v144 = false := by decide +kernel

private def v145 : List Sig := [w82,raw4,raw6,w22,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v145 : search 8 0 v145 = false := by decide +kernel

private def w83 : Sig := bin true raw4 raw6

private def v146 : List Sig := [w83,raw4,raw6,w22,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v146 : search 8 0 v146 = false := by decide +kernel

private def w84 : Sig := bin false raw5 raw6

private def v147 : List Sig := [w84,raw5,raw6,w22,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v147 : search 8 0 v147 = false := by decide +kernel

private def w85 : Sig := bin true raw5 raw6

private def v148 : List Sig := [w85,raw5,raw6,w22,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v148 : search 8 0 v148 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v78 : search 9 0 v78 = false := by
  apply reject_step 8 0 v78 [] [v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v79
    · exact no_8_0_v80
    · exact no_8_0_v81
    · exact no_8_0_v82
    · exact no_8_0_v83
    · exact no_8_0_v84
    · exact no_8_0_v85
    · exact no_8_0_v86
    · exact no_8_0_v87
    · exact no_8_0_v88
    · exact no_8_0_v89
    · exact no_8_0_v90
    · exact no_8_0_v91
    · exact no_8_0_v92
    · exact no_8_0_v93
    · exact no_8_0_v94
    · exact no_8_0_v95
    · exact no_8_0_v96
    · exact no_8_0_v97
    · exact no_8_0_v98
    · exact no_8_0_v99
    · exact no_8_0_v100
    · exact no_8_0_v101
    · exact no_8_0_v102
    · exact no_8_0_v103
    · exact no_8_0_v104
    · exact no_8_0_v105
    · exact no_8_0_v106
    · exact no_8_0_v107
    · exact no_8_0_v108
    · exact no_8_0_v109
    · exact no_8_0_v110
    · exact no_8_0_v111
    · exact no_8_0_v112
    · exact no_8_0_v113
    · exact no_8_0_v114
    · exact no_8_0_v115
    · exact no_8_0_v116
    · exact no_8_0_v117
    · exact no_8_0_v118
    · exact no_8_0_v119
    · exact no_8_0_v120
    · exact no_8_0_v121
    · exact no_8_0_v122
    · exact no_8_0_v123
    · exact no_8_0_v124
    · exact no_8_0_v125
    · exact no_8_0_v126
    · exact no_8_0_v127
    · exact no_8_0_v128
    · exact no_8_0_v129
    · exact no_8_0_v130
    · exact no_8_0_v131
    · exact no_8_0_v132
    · exact no_8_0_v133
    · exact no_8_0_v134
    · exact no_8_0_v135
    · exact no_8_0_v136
    · exact no_8_0_v137
    · exact no_8_0_v138
    · exact no_8_0_v139
    · exact no_8_0_v140
    · exact no_8_0_v141
    · exact no_8_0_v142
    · exact no_8_0_v143
    · exact no_8_0_v144
    · exact no_8_0_v145
    · exact no_8_0_v146
    · exact no_8_0_v147
    · exact no_8_0_v148
  · decide +kernel

private def v149 : List Sig := [w22,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v149 : search 9 0 v149 = false := by decide +kernel

private def v150 : List Sig := [w23,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v150 : search 9 0 v150 = false := by decide +kernel

private def v151 : List Sig := [w26,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v151 : search 9 0 v151 = false := by decide +kernel

private def v152 : List Sig := [w27,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v152 : search 9 0 v152 = false := by decide +kernel

private def v153 : List Sig := [w28,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v153 : search 9 0 v153 = false := by decide +kernel

private def v154 : List Sig := [w29,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v154 : search 9 0 v154 = false := by decide +kernel

private def v155 : List Sig := [w30,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v155 : search 9 0 v155 = false := by decide +kernel

private def v156 : List Sig := [w31,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v156 : search 9 0 v156 = false := by decide +kernel

private def v157 : List Sig := [w32,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v157 : search 9 0 v157 = false := by decide +kernel

private def v158 : List Sig := [w33,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v158 : search 9 0 v158 = false := by decide +kernel

private def v159 : List Sig := [w76,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v159 : search 9 0 v159 = false := by decide +kernel

private def v160 : List Sig := [w77,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v160 : search 9 0 v160 = false := by decide +kernel

private def v161 : List Sig := [w34,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v161 : search 9 0 v161 = false := by decide +kernel

private def v162 : List Sig := [w35,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

private def v163 : List Sig := [w26,raw2,w35,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v163 : search 8 0 v163 = false := by decide +kernel

private def v164 : List Sig := [w26,raw1,raw2,w35,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v164 : search 8 0 v164 = false := by decide +kernel

private def v165 : List Sig := [w27,raw1,raw2,w35,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v165 : search 8 0 v165 = false := by decide +kernel

private def v166 : List Sig := [w28,raw1,raw3,w35,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v166 : search 8 0 v166 = false := by decide +kernel

private def v167 : List Sig := [w29,raw3,w35,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v167 : search 8 0 v167 = false := by decide +kernel

private def v168 : List Sig := [w29,raw1,raw3,w35,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v168 : search 8 0 v168 = false := by decide +kernel

private def v169 : List Sig := [w30,raw1,raw4,w35,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v169 : search 8 0 v169 = false := by decide +kernel

private def v170 : List Sig := [w31,raw1,raw4,w35,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v170 : search 8 0 v170 = false := by decide +kernel

private def v171 : List Sig := [w32,raw1,raw5,w35,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v171 : search 8 0 v171 = false := by decide +kernel

private def v172 : List Sig := [w33,raw1,raw5,w35,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v172 : search 8 0 v172 = false := by decide +kernel

private def v173 : List Sig := [w76,raw1,raw6,w35,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v173 : search 8 0 v173 = false := by decide +kernel

private def v174 : List Sig := [w77,raw1,raw6,w35,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v174 : search 8 0 v174 = false := by decide +kernel

private def w86 : Sig := bin false raw0 w35

private def v175 : List Sig := [w86,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v175 : search 8 0 v175 = false := by decide +kernel

private def v176 : List Sig := [w86,raw0,w35,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v176 : search 8 0 v176 = false := by decide +kernel

private def w87 : Sig := bin true raw0 w35

private def v177 : List Sig := [w87,raw0,w35,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v177 : search 8 0 v177 = false := by decide +kernel

private def v178 : List Sig := [w8,raw0,raw1,w35,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v178 : search 8 0 v178 = false := by decide +kernel

private def v179 : List Sig := [w9,raw0,w35,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v179 : search 8 0 v179 = false := by decide +kernel

private def v180 : List Sig := [w9,raw0,raw1,w35,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v180 : search 8 0 v180 = false := by decide +kernel

private def v181 : List Sig := [w10,raw0,raw2,w35,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v181 : search 8 0 v181 = false := by decide +kernel

private def v182 : List Sig := [w11,raw0,raw2,w35,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v182 : search 8 0 v182 = false := by decide +kernel

private def v183 : List Sig := [w12,raw0,raw3,w35,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v183 : search 8 0 v183 = false := by decide +kernel

private def v184 : List Sig := [w13,raw0,raw3,w35,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v184 : search 8 0 v184 = false := by decide +kernel

private def v185 : List Sig := [w14,raw0,raw4,w35,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v185 : search 8 0 v185 = false := by decide +kernel

private def v186 : List Sig := [w15,raw0,raw4,w35,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v186 : search 8 0 v186 = false := by decide +kernel

private def v187 : List Sig := [w16,raw0,raw5,w35,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v187 : search 8 0 v187 = false := by decide +kernel

private def v188 : List Sig := [w17,raw0,raw5,w35,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v188 : search 8 0 v188 = false := by decide +kernel

private def v189 : List Sig := [w18,raw0,raw6,w35,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v189 : search 8 0 v189 = false := by decide +kernel

private def v190 : List Sig := [w19,raw0,w35,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v190 : search 8 0 v190 = false := by decide +kernel

private def v191 : List Sig := [w19,raw0,raw6,w35,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v191 : search 8 0 v191 = false := by decide +kernel

private def w88 : Sig := bin false raw2 w35

private def v192 : List Sig := [w88,raw2,w35,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v192 : search 8 0 v192 = false := by decide +kernel

private def w89 : Sig := bin true raw2 w35

private def v193 : List Sig := [w89,raw2,w35,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v193 : search 8 0 v193 = false := by decide +kernel

private def v194 : List Sig := [w38,raw2,raw5,w35,raw1,raw0,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v194 : search 8 0 v194 = false := by decide +kernel

private def v195 : List Sig := [w39,raw2,w35,raw1,raw0,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v195 : search 8 0 v195 = false := by decide +kernel

private def v196 : List Sig := [w39,raw2,raw5,w35,raw1,raw0,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v196 : search 8 0 v196 = false := by decide +kernel

private def v197 : List Sig := [w78,raw2,raw6,w35,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v197 : search 8 0 v197 = false := by decide +kernel

private def v198 : List Sig := [w79,raw2,raw6,w35,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v198 : search 8 0 v198 = false := by decide +kernel

private def w90 : Sig := bin false raw3 w35

private def v199 : List Sig := [w90,raw3,w35,raw1,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v199 : search 8 0 v199 = false := by decide +kernel

private def w91 : Sig := bin true raw3 w35

private def v200 : List Sig := [w91,raw3,w35,raw1,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v200 : search 8 0 v200 = false := by decide +kernel

private def v201 : List Sig := [w44,raw3,raw2,w35,raw1,raw0,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v201 : search 8 0 v201 = false := by decide +kernel

private def v202 : List Sig := [w45,raw3,raw2,w35,raw1,raw0,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v202 : search 8 0 v202 = false := by decide +kernel

private def v203 : List Sig := [w46,raw3,raw4,w35,raw1,raw0,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v203 : search 8 0 v203 = false := by decide +kernel

private def v204 : List Sig := [w47,raw3,raw4,w35,raw1,raw0,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v204 : search 8 0 v204 = false := by decide +kernel

private def v205 : List Sig := [w48,raw3,w35,raw1,raw0,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v205 : search 8 0 v205 = false := by decide +kernel

private def v206 : List Sig := [w48,raw3,raw5,w35,raw1,raw0,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v206 : search 8 0 v206 = false := by decide +kernel

private def v207 : List Sig := [w49,raw3,raw5,w35,raw1,raw0,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v207 : search 8 0 v207 = false := by decide +kernel

private def v208 : List Sig := [w80,raw3,raw6,w35,raw1,raw0,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v208 : search 8 0 v208 = false := by decide +kernel

private def v209 : List Sig := [w81,raw3,w35,raw1,raw0,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v209 : search 8 0 v209 = false := by decide +kernel

private def v210 : List Sig := [w81,raw3,raw6,w35,raw1,raw0,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v210 : search 8 0 v210 = false := by decide +kernel

private def w92 : Sig := bin false raw4 w35

private def v211 : List Sig := [w92,raw4,w35,raw1,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v211 : search 8 0 v211 = false := by decide +kernel

private def w93 : Sig := bin true raw4 w35

private def v212 : List Sig := [w93,raw4,raw1,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v212 : search 8 0 v212 = false := by decide +kernel

private def v213 : List Sig := [w93,raw4,w35,raw1,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v213 : search 8 0 v213 = false := by decide +kernel

private def v214 : List Sig := [w54,raw4,raw2,w35,raw1,raw0,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v214 : search 8 0 v214 = false := by decide +kernel

private def v215 : List Sig := [w55,raw4,raw2,w35,raw1,raw0,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v215 : search 8 0 v215 = false := by decide +kernel

private def v216 : List Sig := [w56,raw4,raw5,w35,raw1,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v216 : search 8 0 v216 = false := by decide +kernel

private def v217 : List Sig := [w57,raw4,w35,raw1,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v217 : search 8 0 v217 = false := by decide +kernel

private def v218 : List Sig := [w57,raw4,raw5,w35,raw1,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v218 : search 8 0 v218 = false := by decide +kernel

private def v219 : List Sig := [w82,raw4,w35,raw1,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v219 : search 8 0 v219 = false := by decide +kernel

private def v220 : List Sig := [w82,raw4,raw6,w35,raw1,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v220 : search 8 0 v220 = false := by decide +kernel

private def v221 : List Sig := [w83,raw4,raw6,w35,raw1,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v221 : search 8 0 v221 = false := by decide +kernel

private def w94 : Sig := bin false raw5 w35

private def v222 : List Sig := [w94,raw5,w35,raw1,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v222 : search 8 0 v222 = false := by decide +kernel

private def w95 : Sig := bin true raw5 w35

private def v223 : List Sig := [w95,raw5,w35,raw1,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v223 : search 8 0 v223 = false := by decide +kernel

private def v224 : List Sig := [w84,raw5,raw6,w35,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v224 : search 8 0 v224 = false := by decide +kernel

private def v225 : List Sig := [w85,raw5,raw6,w35,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v225 : search 8 0 v225 = false := by decide +kernel

private def w96 : Sig := bin false raw6 w35

private def v226 : List Sig := [w96,raw6,w35,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v226 : search 8 0 v226 = false := by decide +kernel

private def w97 : Sig := bin true raw6 w35

private def v227 : List Sig := [w97,raw6,w35,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v227 : search 8 0 v227 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v162 : search 9 0 v162 = false := by
  apply reject_step 8 0 v162 [] [v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202,v203,v204,v205,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v226,v227]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v163
    · exact no_8_0_v164
    · exact no_8_0_v165
    · exact no_8_0_v166
    · exact no_8_0_v167
    · exact no_8_0_v168
    · exact no_8_0_v169
    · exact no_8_0_v170
    · exact no_8_0_v171
    · exact no_8_0_v172
    · exact no_8_0_v173
    · exact no_8_0_v174
    · exact no_8_0_v175
    · exact no_8_0_v176
    · exact no_8_0_v177
    · exact no_8_0_v178
    · exact no_8_0_v179
    · exact no_8_0_v180
    · exact no_8_0_v181
    · exact no_8_0_v182
    · exact no_8_0_v183
    · exact no_8_0_v184
    · exact no_8_0_v185
    · exact no_8_0_v186
    · exact no_8_0_v187
    · exact no_8_0_v188
    · exact no_8_0_v189
    · exact no_8_0_v190
    · exact no_8_0_v191
    · exact no_8_0_v192
    · exact no_8_0_v193
    · exact no_8_0_v194
    · exact no_8_0_v195
    · exact no_8_0_v196
    · exact no_8_0_v197
    · exact no_8_0_v198
    · exact no_8_0_v199
    · exact no_8_0_v200
    · exact no_8_0_v201
    · exact no_8_0_v202
    · exact no_8_0_v203
    · exact no_8_0_v204
    · exact no_8_0_v205
    · exact no_8_0_v206
    · exact no_8_0_v207
    · exact no_8_0_v208
    · exact no_8_0_v209
    · exact no_8_0_v210
    · exact no_8_0_v211
    · exact no_8_0_v212
    · exact no_8_0_v213
    · exact no_8_0_v214
    · exact no_8_0_v215
    · exact no_8_0_v216
    · exact no_8_0_v217
    · exact no_8_0_v218
    · exact no_8_0_v219
    · exact no_8_0_v220
    · exact no_8_0_v221
    · exact no_8_0_v222
    · exact no_8_0_v223
    · exact no_8_0_v224
    · exact no_8_0_v225
    · exact no_8_0_v226
    · exact no_8_0_v227
  · decide +kernel

private def v228 : List Sig := [w35,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v228 : search 9 0 v228 = false := by decide +kernel

private def v229 : List Sig := [w38,raw2,raw5,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v229 : search 9 0 v229 = false := by decide +kernel

private def v230 : List Sig := [w39,raw2,raw0,raw1,raw3,raw4,raw6,raw7]

private def w98 : Sig := bin false w39 raw6

private def v231 : List Sig := [w98,w39,raw6,raw2,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v231 : search 8 0 v231 = false := by decide +kernel

private def w99 : Sig := bin true w39 raw6

private def v232 : List Sig := [w99,w39,raw6,raw2,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v232 : search 8 0 v232 = false := by decide +kernel

private def w100 : Sig := bin false w39 raw7

private def v233 : List Sig := [w100,w39,raw7,raw2,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v233 : search 8 0 v233 = false := by decide +kernel

private def w101 : Sig := bin true w39 raw7

private def v234 : List Sig := [w101,w39,raw7,raw2,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v234 : search 8 0 v234 = false := by decide +kernel

private def v235 : List Sig := [w78,raw2,raw6,w39,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v235 : search 8 0 v235 = false := by decide +kernel

private def v236 : List Sig := [w79,raw2,raw6,w39,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v236 : search 8 0 v236 = false := by decide +kernel

private def v237 : List Sig := [w40,raw2,raw7,w39,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v237 : search 8 0 v237 = false := by decide +kernel

private def v238 : List Sig := [w41,raw2,raw7,w39,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v238 : search 8 0 v238 = false := by decide +kernel

private def w102 : Sig := bin false raw0 w39

private def v239 : List Sig := [w102,raw0,w39,raw2,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v239 : search 8 0 v239 = false := by decide +kernel

private def w103 : Sig := bin true raw0 w39

private def v240 : List Sig := [w103,raw0,w39,raw2,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v240 : search 8 0 v240 = false := by decide +kernel

private def v241 : List Sig := [w10,raw0,raw2,w39,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v241 : search 8 0 v241 = false := by decide +kernel

private def v242 : List Sig := [w11,raw0,w39,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v242 : search 8 0 v242 = false := by decide +kernel

private def v243 : List Sig := [w11,raw0,raw2,w39,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v243 : search 8 0 v243 = false := by decide +kernel

private def v244 : List Sig := [w8,raw0,raw1,w39,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v244 : search 8 0 v244 = false := by decide +kernel

private def v245 : List Sig := [w9,raw0,raw1,w39,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v245 : search 8 0 v245 = false := by decide +kernel

private def v246 : List Sig := [w12,raw0,raw3,w39,raw2,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v246 : search 8 0 v246 = false := by decide +kernel

private def v247 : List Sig := [w13,raw0,raw3,w39,raw2,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v247 : search 8 0 v247 = false := by decide +kernel

private def v248 : List Sig := [w14,raw0,raw4,w39,raw2,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v248 : search 8 0 v248 = false := by decide +kernel

private def v249 : List Sig := [w15,raw0,raw4,w39,raw2,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v249 : search 8 0 v249 = false := by decide +kernel

private def v250 : List Sig := [w18,raw0,raw6,w39,raw2,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v250 : search 8 0 v250 = false := by decide +kernel

private def v251 : List Sig := [w19,raw0,w39,raw2,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v251 : search 8 0 v251 = false := by decide +kernel

private def v252 : List Sig := [w19,raw0,raw6,w39,raw2,raw1,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v252 : search 8 0 v252 = false := by decide +kernel

private def v253 : List Sig := [w22,raw0,w39,raw2,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v253 : search 8 0 v253 = false := by decide +kernel

private def v254 : List Sig := [w22,raw0,raw7,w39,raw2,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v254 : search 8 0 v254 = false := by decide +kernel

private def v255 : List Sig := [w23,raw0,raw7,w39,raw2,raw1,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v255 : search 8 0 v255 = false := by decide +kernel

private def w104 : Sig := bin false raw1 w39

private def v256 : List Sig := [w104,raw1,w39,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v256 : search 8 0 v256 = false := by decide +kernel

private def w105 : Sig := bin true raw1 w39

private def v257 : List Sig := [w105,raw1,w39,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v257 : search 8 0 v257 = false := by decide +kernel

private def v258 : List Sig := [w26,raw1,w39,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v258 : search 8 0 v258 = false := by decide +kernel

private def v259 : List Sig := [w26,raw1,raw2,w39,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v259 : search 8 0 v259 = false := by decide +kernel

private def v260 : List Sig := [w27,raw1,raw2,w39,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v260 : search 8 0 v260 = false := by decide +kernel

private def v261 : List Sig := [w28,raw1,raw3,w39,raw2,raw0,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v261 : search 8 0 v261 = false := by decide +kernel

private def v262 : List Sig := [w29,raw1,raw3,w39,raw2,raw0,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v262 : search 8 0 v262 = false := by decide +kernel

private def v263 : List Sig := [w30,raw1,raw4,w39,raw2,raw0,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v263 : search 8 0 v263 = false := by decide +kernel

private def v264 : List Sig := [w31,raw1,raw4,w39,raw2,raw0,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v264 : search 8 0 v264 = false := by decide +kernel

private def v265 : List Sig := [w76,raw1,raw6,w39,raw2,raw0,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v265 : search 8 0 v265 = false := by decide +kernel

private def v266 : List Sig := [w77,raw1,raw6,w39,raw2,raw0,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v266 : search 8 0 v266 = false := by decide +kernel

private def v267 : List Sig := [w34,raw1,raw7,w39,raw2,raw0,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v267 : search 8 0 v267 = false := by decide +kernel

private def v268 : List Sig := [w35,raw1,w39,raw2,raw0,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v268 : search 8 0 v268 = false := by decide +kernel

private def v269 : List Sig := [w35,raw1,raw7,w39,raw2,raw0,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v269 : search 8 0 v269 = false := by decide +kernel

private def w106 : Sig := bin false raw3 w39

private def v270 : List Sig := [w106,raw3,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v270 : search 8 0 v270 = false := by decide +kernel

private def v271 : List Sig := [w106,raw3,w39,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v271 : search 8 0 v271 = false := by decide +kernel

private def w107 : Sig := bin true raw3 w39

private def v272 : List Sig := [w107,raw3,w39,raw2,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v272 : search 8 0 v272 = false := by decide +kernel

private def v273 : List Sig := [w44,raw3,raw2,w39,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v273 : search 8 0 v273 = false := by decide +kernel

private def v274 : List Sig := [w45,raw3,w39,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v274 : search 8 0 v274 = false := by decide +kernel

private def v275 : List Sig := [w45,raw3,raw2,w39,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v275 : search 8 0 v275 = false := by decide +kernel

private def v276 : List Sig := [w46,raw3,raw4,w39,raw2,raw0,raw1,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v276 : search 8 0 v276 = false := by decide +kernel

private def v277 : List Sig := [w47,raw3,raw4,w39,raw2,raw0,raw1,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v277 : search 8 0 v277 = false := by decide +kernel

private def v278 : List Sig := [w80,raw3,raw6,w39,raw2,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v278 : search 8 0 v278 = false := by decide +kernel

private def v279 : List Sig := [w81,raw3,w39,raw2,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v279 : search 8 0 v279 = false := by decide +kernel

private def v280 : List Sig := [w81,raw3,raw6,w39,raw2,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v280 : search 8 0 v280 = false := by decide +kernel

private def v281 : List Sig := [w50,raw3,raw7,w39,raw2,raw0,raw1,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v281 : search 8 0 v281 = false := by decide +kernel

private def v282 : List Sig := [w51,raw3,raw7,w39,raw2,raw0,raw1,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v282 : search 8 0 v282 = false := by decide +kernel

private def w108 : Sig := bin false raw4 w39

private def v283 : List Sig := [w108,raw4,w39,raw2,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v283 : search 8 0 v283 = false := by decide +kernel

private def w109 : Sig := bin true raw4 w39

private def v284 : List Sig := [w109,raw4,raw2,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v284 : search 8 0 v284 = false := by decide +kernel

private def v285 : List Sig := [w109,raw4,w39,raw2,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v285 : search 8 0 v285 = false := by decide +kernel

private def v286 : List Sig := [w54,raw4,raw2,w39,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v286 : search 8 0 v286 = false := by decide +kernel

private def v287 : List Sig := [w55,raw4,raw2,w39,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v287 : search 8 0 v287 = false := by decide +kernel

private def v288 : List Sig := [w82,raw4,w39,raw2,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v288 : search 8 0 v288 = false := by decide +kernel

private def v289 : List Sig := [w82,raw4,raw6,w39,raw2,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v289 : search 8 0 v289 = false := by decide +kernel

private def v290 : List Sig := [w83,raw4,raw6,w39,raw2,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v290 : search 8 0 v290 = false := by decide +kernel

private def v291 : List Sig := [w58,raw4,raw7,w39,raw2,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v291 : search 8 0 v291 = false := by decide +kernel

private def v292 : List Sig := [w59,raw4,w39,raw2,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v292 : search 8 0 v292 = false := by decide +kernel

private def v293 : List Sig := [w59,raw4,raw7,w39,raw2,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v293 : search 8 0 v293 = false := by decide +kernel

private def w110 : Sig := bin false raw6 raw7

private def v294 : List Sig := [w110,raw6,raw7,w39,raw2,raw0,raw1,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v294 : search 8 0 v294 = false := by decide +kernel

private def w111 : Sig := bin true raw6 raw7

private def v295 : List Sig := [w111,raw6,raw7,w39,raw2,raw0,raw1,raw3,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v295 : search 8 0 v295 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v230 : search 9 0 v230 = false := by
  apply reject_step 8 0 v230 [] [v231,v232,v233,v234,v235,v236,v237,v238,v239,v240,v241,v242,v243,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v231
    · exact no_8_0_v232
    · exact no_8_0_v233
    · exact no_8_0_v234
    · exact no_8_0_v235
    · exact no_8_0_v236
    · exact no_8_0_v237
    · exact no_8_0_v238
    · exact no_8_0_v239
    · exact no_8_0_v240
    · exact no_8_0_v241
    · exact no_8_0_v242
    · exact no_8_0_v243
    · exact no_8_0_v244
    · exact no_8_0_v245
    · exact no_8_0_v246
    · exact no_8_0_v247
    · exact no_8_0_v248
    · exact no_8_0_v249
    · exact no_8_0_v250
    · exact no_8_0_v251
    · exact no_8_0_v252
    · exact no_8_0_v253
    · exact no_8_0_v254
    · exact no_8_0_v255
    · exact no_8_0_v256
    · exact no_8_0_v257
    · exact no_8_0_v258
    · exact no_8_0_v259
    · exact no_8_0_v260
    · exact no_8_0_v261
    · exact no_8_0_v262
    · exact no_8_0_v263
    · exact no_8_0_v264
    · exact no_8_0_v265
    · exact no_8_0_v266
    · exact no_8_0_v267
    · exact no_8_0_v268
    · exact no_8_0_v269
    · exact no_8_0_v270
    · exact no_8_0_v271
    · exact no_8_0_v272
    · exact no_8_0_v273
    · exact no_8_0_v274
    · exact no_8_0_v275
    · exact no_8_0_v276
    · exact no_8_0_v277
    · exact no_8_0_v278
    · exact no_8_0_v279
    · exact no_8_0_v280
    · exact no_8_0_v281
    · exact no_8_0_v282
    · exact no_8_0_v283
    · exact no_8_0_v284
    · exact no_8_0_v285
    · exact no_8_0_v286
    · exact no_8_0_v287
    · exact no_8_0_v288
    · exact no_8_0_v289
    · exact no_8_0_v290
    · exact no_8_0_v291
    · exact no_8_0_v292
    · exact no_8_0_v293
    · exact no_8_0_v294
    · exact no_8_0_v295
  · decide +kernel

private def v296 : List Sig := [w39,raw2,raw5,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v296 : search 9 0 v296 = false := by decide +kernel

private def v297 : List Sig := [w78,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v297 : search 9 0 v297 = false := by decide +kernel

private def v298 : List Sig := [w79,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v298 : search 9 0 v298 = false := by decide +kernel

private def v299 : List Sig := [w40,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v299 : search 9 0 v299 = false := by decide +kernel

private def v300 : List Sig := [w41,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v300 : search 9 0 v300 = false := by decide +kernel

private def v301 : List Sig := [w44,raw3,raw2,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v301 : search 9 0 v301 = false := by decide +kernel

private def v302 : List Sig := [w45,raw3,raw2,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v302 : search 9 0 v302 = false := by decide +kernel

private def v303 : List Sig := [w46,raw3,raw4,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v303 : search 9 0 v303 = false := by decide +kernel

private def v304 : List Sig := [w47,raw3,raw4,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v304 : search 9 0 v304 = false := by decide +kernel

private def v305 : List Sig := [w48,raw3,raw0,raw1,raw2,raw4,raw6,raw7]

private def w112 : Sig := bin false w48 raw2

private def v306 : List Sig := [w112,w48,raw2,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v306 : search 8 0 v306 = false := by decide +kernel

private def w113 : Sig := bin true w48 raw2

private def v307 : List Sig := [w113,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v307 : search 8 0 v307 = false := by decide +kernel

private def v308 : List Sig := [w113,w48,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v308 : search 8 0 v308 = false := by decide +kernel

private def v309 : List Sig := [w113,raw2,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v309 : search 8 0 v309 = false := by decide +kernel

private def v310 : List Sig := [w113,w48,raw2,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v310 : search 8 0 v310 = false := by decide +kernel

private def w114 : Sig := bin false w48 raw4

private def v311 : List Sig := [w114,w48,raw4,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v311 : search 8 0 v311 = false := by decide +kernel

private def w115 : Sig := bin true w48 raw4

private def v312 : List Sig := [w115,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v312 : search 8 0 v312 = false := by decide +kernel

private def v313 : List Sig := [w115,w48,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v313 : search 8 0 v313 = false := by decide +kernel

private def v314 : List Sig := [w115,raw4,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v314 : search 8 0 v314 = false := by decide +kernel

private def v315 : List Sig := [w115,w48,raw4,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v315 : search 8 0 v315 = false := by decide +kernel

private def w116 : Sig := bin false w48 raw6

private def v316 : List Sig := [w116,w48,raw6,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v316 : search 8 0 v316 = false := by decide +kernel

private def w117 : Sig := bin true w48 raw6

private def v317 : List Sig := [w117,w48,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v317 : search 8 0 v317 = false := by decide +kernel

private def v318 : List Sig := [w117,w48,raw6,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v318 : search 8 0 v318 = false := by decide +kernel

private def w118 : Sig := bin false w48 raw7

private def v319 : List Sig := [w118,w48,raw7,raw3,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v319 : search 8 0 v319 = false := by decide +kernel

private def w119 : Sig := bin true w48 raw7

private def v320 : List Sig := [w119,w48,raw3,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v320 : search 8 0 v320 = false := by decide +kernel

private def v321 : List Sig := [w119,w48,raw7,raw3,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v321 : search 8 0 v321 = false := by decide +kernel

private def v322 : List Sig := [w44,raw3,raw2,w48,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v322 : search 8 0 v322 = false := by decide +kernel

private def v323 : List Sig := [w45,raw3,raw2,w48,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v323 : search 8 0 v323 = false := by decide +kernel

private def v324 : List Sig := [w46,raw3,raw4,w48,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v324 : search 8 0 v324 = false := by decide +kernel

private def v325 : List Sig := [w47,raw3,raw4,w48,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v325 : search 8 0 v325 = false := by decide +kernel

private def v326 : List Sig := [w80,raw3,raw6,w48,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v326 : search 8 0 v326 = false := by decide +kernel

private def v327 : List Sig := [w81,raw3,w48,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v327 : search 8 0 v327 = false := by decide +kernel

private def v328 : List Sig := [w81,raw3,raw6,w48,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v328 : search 8 0 v328 = false := by decide +kernel

private def v329 : List Sig := [w50,raw3,raw7,w48,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v329 : search 8 0 v329 = false := by decide +kernel

private def v330 : List Sig := [w51,raw3,raw7,w48,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v330 : search 8 0 v330 = false := by decide +kernel

private def w120 : Sig := bin false raw0 w48

private def v331 : List Sig := [w120,raw0,w48,raw3,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v331 : search 8 0 v331 = false := by decide +kernel

private def w121 : Sig := bin true raw0 w48

private def v332 : List Sig := [w121,w48,raw3,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v332 : search 8 0 v332 = false := by decide +kernel

private def v333 : List Sig := [w121,raw0,w48,raw3,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v333 : search 8 0 v333 = false := by decide +kernel

private def v334 : List Sig := [w12,raw0,raw3,w48,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v334 : search 8 0 v334 = false := by decide +kernel

private def v335 : List Sig := [w13,raw0,raw3,w48,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v335 : search 8 0 v335 = false := by decide +kernel

private def v336 : List Sig := [w8,raw0,raw1,w48,raw3,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v336 : search 8 0 v336 = false := by decide +kernel

private def v337 : List Sig := [w9,raw0,raw1,w48,raw3,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v337 : search 8 0 v337 = false := by decide +kernel

private def v338 : List Sig := [w10,raw0,raw2,w48,raw3,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v338 : search 8 0 v338 = false := by decide +kernel

private def v339 : List Sig := [w11,raw0,raw2,w48,raw3,raw1,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v339 : search 8 0 v339 = false := by decide +kernel

private def v340 : List Sig := [w14,raw0,raw4,w48,raw3,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v340 : search 8 0 v340 = false := by decide +kernel

private def v341 : List Sig := [w15,raw0,raw4,w48,raw3,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v341 : search 8 0 v341 = false := by decide +kernel

private def v342 : List Sig := [w18,raw0,raw6,w48,raw3,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v342 : search 8 0 v342 = false := by decide +kernel

private def v343 : List Sig := [w19,raw0,w48,raw3,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v343 : search 8 0 v343 = false := by decide +kernel

private def v344 : List Sig := [w19,raw0,raw6,w48,raw3,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v344 : search 8 0 v344 = false := by decide +kernel

private def v345 : List Sig := [w22,raw0,w48,raw3,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v345 : search 8 0 v345 = false := by decide +kernel

private def v346 : List Sig := [w22,raw0,raw7,w48,raw3,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v346 : search 8 0 v346 = false := by decide +kernel

private def v347 : List Sig := [w23,raw0,raw7,w48,raw3,raw1,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v347 : search 8 0 v347 = false := by decide +kernel

private def w122 : Sig := bin false raw1 w48

private def v348 : List Sig := [w122,raw1,w48,raw3,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v348 : search 8 0 v348 = false := by decide +kernel

private def w123 : Sig := bin true raw1 w48

private def v349 : List Sig := [w123,w48,raw3,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v349 : search 8 0 v349 = false := by decide +kernel

private def v350 : List Sig := [w123,raw1,w48,raw3,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v350 : search 8 0 v350 = false := by decide +kernel

private def v351 : List Sig := [w28,raw1,raw3,w48,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v351 : search 8 0 v351 = false := by decide +kernel

private def v352 : List Sig := [w29,raw1,raw3,w48,raw0,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v352 : search 8 0 v352 = false := by decide +kernel

private def v353 : List Sig := [w26,raw1,raw2,w48,raw3,raw0,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v353 : search 8 0 v353 = false := by decide +kernel

private def v354 : List Sig := [w27,raw1,raw2,w48,raw3,raw0,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v354 : search 8 0 v354 = false := by decide +kernel

private def v355 : List Sig := [w30,raw1,raw4,w48,raw3,raw0,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v355 : search 8 0 v355 = false := by decide +kernel

private def v356 : List Sig := [w31,raw1,raw4,w48,raw3,raw0,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v356 : search 8 0 v356 = false := by decide +kernel

private def v357 : List Sig := [w76,raw1,raw6,w48,raw3,raw0,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v357 : search 8 0 v357 = false := by decide +kernel

private def v358 : List Sig := [w77,raw1,raw6,w48,raw3,raw0,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v358 : search 8 0 v358 = false := by decide +kernel

private def v359 : List Sig := [w34,raw1,raw7,w48,raw3,raw0,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v359 : search 8 0 v359 = false := by decide +kernel

private def v360 : List Sig := [w35,raw1,w48,raw3,raw0,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v360 : search 8 0 v360 = false := by decide +kernel

private def v361 : List Sig := [w35,raw1,raw7,w48,raw3,raw0,raw2,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v361 : search 8 0 v361 = false := by decide +kernel

private def v362 : List Sig := [w78,raw2,raw6,w48,raw3,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v362 : search 8 0 v362 = false := by decide +kernel

private def v363 : List Sig := [w79,raw2,raw6,w48,raw3,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v363 : search 8 0 v363 = false := by decide +kernel

private def v364 : List Sig := [w40,raw2,raw7,w48,raw3,raw0,raw1,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v364 : search 8 0 v364 = false := by decide +kernel

private def v365 : List Sig := [w41,raw2,raw7,w48,raw3,raw0,raw1,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v365 : search 8 0 v365 = false := by decide +kernel

private def v366 : List Sig := [w54,raw4,raw2,w48,raw3,raw0,raw1,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v366 : search 8 0 v366 = false := by decide +kernel

private def v367 : List Sig := [w55,raw4,raw2,w48,raw3,raw0,raw1,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v367 : search 8 0 v367 = false := by decide +kernel

private def v368 : List Sig := [w82,raw4,w48,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v368 : search 8 0 v368 = false := by decide +kernel

private def v369 : List Sig := [w82,raw4,raw6,w48,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v369 : search 8 0 v369 = false := by decide +kernel

private def v370 : List Sig := [w83,raw4,raw6,w48,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v370 : search 8 0 v370 = false := by decide +kernel

private def v371 : List Sig := [w58,raw4,raw7,w48,raw3,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v371 : search 8 0 v371 = false := by decide +kernel

private def v372 : List Sig := [w59,raw4,w48,raw3,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v372 : search 8 0 v372 = false := by decide +kernel

private def v373 : List Sig := [w59,raw4,raw7,w48,raw3,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v373 : search 8 0 v373 = false := by decide +kernel

private def v374 : List Sig := [w110,raw6,raw7,w48,raw3,raw0,raw1,raw2,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v374 : search 8 0 v374 = false := by decide +kernel

private def v375 : List Sig := [w111,raw6,raw7,w48,raw3,raw0,raw1,raw2,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v375 : search 8 0 v375 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v305 : search 9 0 v305 = false := by
  apply reject_step 8 0 v305 [] [v306,v307,v308,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v319,v320,v321,v322,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340,v341,v342,v343,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365,v366,v367,v368,v369,v370,v371,v372,v373,v374,v375]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v306
    · exact no_8_0_v307
    · exact no_8_0_v308
    · exact no_8_0_v309
    · exact no_8_0_v310
    · exact no_8_0_v311
    · exact no_8_0_v312
    · exact no_8_0_v313
    · exact no_8_0_v314
    · exact no_8_0_v315
    · exact no_8_0_v316
    · exact no_8_0_v317
    · exact no_8_0_v318
    · exact no_8_0_v319
    · exact no_8_0_v320
    · exact no_8_0_v321
    · exact no_8_0_v322
    · exact no_8_0_v323
    · exact no_8_0_v324
    · exact no_8_0_v325
    · exact no_8_0_v326
    · exact no_8_0_v327
    · exact no_8_0_v328
    · exact no_8_0_v329
    · exact no_8_0_v330
    · exact no_8_0_v331
    · exact no_8_0_v332
    · exact no_8_0_v333
    · exact no_8_0_v334
    · exact no_8_0_v335
    · exact no_8_0_v336
    · exact no_8_0_v337
    · exact no_8_0_v338
    · exact no_8_0_v339
    · exact no_8_0_v340
    · exact no_8_0_v341
    · exact no_8_0_v342
    · exact no_8_0_v343
    · exact no_8_0_v344
    · exact no_8_0_v345
    · exact no_8_0_v346
    · exact no_8_0_v347
    · exact no_8_0_v348
    · exact no_8_0_v349
    · exact no_8_0_v350
    · exact no_8_0_v351
    · exact no_8_0_v352
    · exact no_8_0_v353
    · exact no_8_0_v354
    · exact no_8_0_v355
    · exact no_8_0_v356
    · exact no_8_0_v357
    · exact no_8_0_v358
    · exact no_8_0_v359
    · exact no_8_0_v360
    · exact no_8_0_v361
    · exact no_8_0_v362
    · exact no_8_0_v363
    · exact no_8_0_v364
    · exact no_8_0_v365
    · exact no_8_0_v366
    · exact no_8_0_v367
    · exact no_8_0_v368
    · exact no_8_0_v369
    · exact no_8_0_v370
    · exact no_8_0_v371
    · exact no_8_0_v372
    · exact no_8_0_v373
    · exact no_8_0_v374
    · exact no_8_0_v375
  · decide +kernel

private def v376 : List Sig := [w48,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v376 : search 9 0 v376 = false := by decide +kernel

private def v377 : List Sig := [w49,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v377 : search 9 0 v377 = false := by decide +kernel

private def v378 : List Sig := [w80,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v378 : search 9 0 v378 = false := by decide +kernel

private def v379 : List Sig := [w81,raw3,raw0,raw1,raw2,raw4,raw5,raw7]

private def w124 : Sig := bin false w81 raw7

private def v380 : List Sig := [w124,w81,raw7,raw3,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v380 : search 8 0 v380 = false := by decide +kernel

private def w125 : Sig := bin true w81 raw7

private def v381 : List Sig := [w125,w81,raw7,raw3,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v381 : search 8 0 v381 = false := by decide +kernel

private def v382 : List Sig := [w44,raw3,raw2,w81,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v382 : search 8 0 v382 = false := by decide +kernel

private def v383 : List Sig := [w45,raw3,raw2,w81,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v383 : search 8 0 v383 = false := by decide +kernel

private def v384 : List Sig := [w46,raw3,raw4,w81,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v384 : search 8 0 v384 = false := by decide +kernel

private def v385 : List Sig := [w47,raw4,w81,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v385 : search 8 0 v385 = false := by decide +kernel

private def v386 : List Sig := [w47,raw3,raw4,w81,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v386 : search 8 0 v386 = false := by decide +kernel

private def v387 : List Sig := [w48,raw3,w81,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v387 : search 8 0 v387 = false := by decide +kernel

private def v388 : List Sig := [w48,raw3,raw5,w81,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v388 : search 8 0 v388 = false := by decide +kernel

private def v389 : List Sig := [w49,raw3,raw5,w81,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v389 : search 8 0 v389 = false := by decide +kernel

private def v390 : List Sig := [w50,raw3,raw7,w81,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v390 : search 8 0 v390 = false := by decide +kernel

private def v391 : List Sig := [w51,raw3,raw7,w81,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v391 : search 8 0 v391 = false := by decide +kernel

private def w126 : Sig := bin false raw0 w81

private def v392 : List Sig := [w126,raw0,w81,raw3,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v392 : search 8 0 v392 = false := by decide +kernel

private def v393 : List Sig := [w43,raw0,raw3,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v393 : search 8 0 v393 = false := by decide +kernel

private def v394 : List Sig := [w43,raw0,w81,raw3,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v394 : search 8 0 v394 = false := by decide +kernel

private def v395 : List Sig := [w12,raw0,raw3,w81,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v395 : search 8 0 v395 = false := by decide +kernel

private def v396 : List Sig := [w13,raw0,raw3,w81,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v396 : search 8 0 v396 = false := by decide +kernel

private def v397 : List Sig := [w8,raw0,raw1,w81,raw3,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v397 : search 8 0 v397 = false := by decide +kernel

private def v398 : List Sig := [w9,raw0,raw1,w81,raw3,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v398 : search 8 0 v398 = false := by decide +kernel

private def v399 : List Sig := [w10,raw0,raw2,w81,raw3,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v399 : search 8 0 v399 = false := by decide +kernel

private def v400 : List Sig := [w11,raw0,raw2,w81,raw3,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v400 : search 8 0 v400 = false := by decide +kernel

private def v401 : List Sig := [w14,raw0,raw4,w81,raw3,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v401 : search 8 0 v401 = false := by decide +kernel

private def v402 : List Sig := [w15,raw0,raw4,w81,raw3,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v402 : search 8 0 v402 = false := by decide +kernel

private def v403 : List Sig := [w16,raw0,raw5,w81,raw3,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v403 : search 8 0 v403 = false := by decide +kernel

private def v404 : List Sig := [w17,raw0,raw5,w81,raw3,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v404 : search 8 0 v404 = false := by decide +kernel

private def v405 : List Sig := [w22,raw0,w81,raw3,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v405 : search 8 0 v405 = false := by decide +kernel

private def v406 : List Sig := [w22,raw0,raw7,w81,raw3,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v406 : search 8 0 v406 = false := by decide +kernel

private def v407 : List Sig := [w23,raw0,raw7,w81,raw3,raw1,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v407 : search 8 0 v407 = false := by decide +kernel

private def w127 : Sig := bin false raw1 w81

private def v408 : List Sig := [w127,raw1,w81,raw3,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v408 : search 8 0 v408 = false := by decide +kernel

private def w128 : Sig := bin true raw1 w81

private def v409 : List Sig := [w128,raw1,w81,raw3,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v409 : search 8 0 v409 = false := by decide +kernel

private def v410 : List Sig := [w28,raw1,raw3,w81,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v410 : search 8 0 v410 = false := by decide +kernel

private def v411 : List Sig := [w29,raw1,raw3,w81,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v411 : search 8 0 v411 = false := by decide +kernel

private def v412 : List Sig := [w26,raw1,raw2,w81,raw3,raw0,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v412 : search 8 0 v412 = false := by decide +kernel

private def v413 : List Sig := [w27,raw1,raw2,w81,raw3,raw0,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v413 : search 8 0 v413 = false := by decide +kernel

private def v414 : List Sig := [w30,raw1,raw4,w81,raw3,raw0,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v414 : search 8 0 v414 = false := by decide +kernel

private def v415 : List Sig := [w31,raw1,raw4,w81,raw3,raw0,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v415 : search 8 0 v415 = false := by decide +kernel

private def v416 : List Sig := [w32,raw1,raw5,w81,raw3,raw0,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v416 : search 8 0 v416 = false := by decide +kernel

private def v417 : List Sig := [w33,raw1,raw5,w81,raw3,raw0,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v417 : search 8 0 v417 = false := by decide +kernel

private def v418 : List Sig := [w34,raw1,raw7,w81,raw3,raw0,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v418 : search 8 0 v418 = false := by decide +kernel

private def v419 : List Sig := [w35,raw1,w81,raw3,raw0,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v419 : search 8 0 v419 = false := by decide +kernel

private def v420 : List Sig := [w35,raw1,raw7,w81,raw3,raw0,raw2,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v420 : search 8 0 v420 = false := by decide +kernel

private def w129 : Sig := bin false raw2 w81

private def v421 : List Sig := [w129,raw2,w81,raw3,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v421 : search 8 0 v421 = false := by decide +kernel

private def w130 : Sig := bin true raw2 w81

private def v422 : List Sig := [w130,raw2,w81,raw3,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v422 : search 8 0 v422 = false := by decide +kernel

private def v423 : List Sig := [w38,raw2,raw5,w81,raw3,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v423 : search 8 0 v423 = false := by decide +kernel

private def v424 : List Sig := [w39,raw2,w81,raw3,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v424 : search 8 0 v424 = false := by decide +kernel

private def v425 : List Sig := [w39,raw2,raw5,w81,raw3,raw0,raw1,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v425 : search 8 0 v425 = false := by decide +kernel

private def v426 : List Sig := [w40,raw2,raw7,w81,raw3,raw0,raw1,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v426 : search 8 0 v426 = false := by decide +kernel

private def v427 : List Sig := [w41,raw2,raw7,w81,raw3,raw0,raw1,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v427 : search 8 0 v427 = false := by decide +kernel

private def w131 : Sig := bin false raw4 w81

private def v428 : List Sig := [w131,raw4,raw3,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v428 : search 8 0 v428 = false := by decide +kernel

private def v429 : List Sig := [w131,raw4,w81,raw3,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v429 : search 8 0 v429 = false := by decide +kernel

private def w132 : Sig := bin true raw4 w81

private def v430 : List Sig := [w132,raw4,w81,raw3,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v430 : search 8 0 v430 = false := by decide +kernel

private def v431 : List Sig := [w54,raw4,raw2,w81,raw3,raw0,raw1,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v431 : search 8 0 v431 = false := by decide +kernel

private def v432 : List Sig := [w55,raw4,raw2,w81,raw3,raw0,raw1,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v432 : search 8 0 v432 = false := by decide +kernel

private def v433 : List Sig := [w56,raw4,raw5,w81,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v433 : search 8 0 v433 = false := by decide +kernel

private def v434 : List Sig := [w57,raw4,w81,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v434 : search 8 0 v434 = false := by decide +kernel

private def v435 : List Sig := [w57,raw4,raw5,w81,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v435 : search 8 0 v435 = false := by decide +kernel

private def v436 : List Sig := [w58,raw4,raw7,w81,raw3,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v436 : search 8 0 v436 = false := by decide +kernel

private def v437 : List Sig := [w59,raw4,w81,raw3,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v437 : search 8 0 v437 = false := by decide +kernel

private def v438 : List Sig := [w59,raw4,raw7,w81,raw3,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v438 : search 8 0 v438 = false := by decide +kernel

private def w133 : Sig := bin false raw5 w81

private def v439 : List Sig := [w133,w81,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v439 : search 8 0 v439 = false := by decide +kernel

private def v440 : List Sig := [w133,raw5,w81,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v440 : search 8 0 v440 = false := by decide +kernel

private def w134 : Sig := bin true raw5 w81

private def v441 : List Sig := [w134,raw5,w81,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v441 : search 8 0 v441 = false := by decide +kernel

private def v442 : List Sig := [w62,raw5,raw7,w81,raw3,raw0,raw1,raw2,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v442 : search 8 0 v442 = false := by decide +kernel

private def v443 : List Sig := [w63,raw5,raw7,w81,raw3,raw0,raw1,raw2,raw4]

set_option maxRecDepth 32768 in
private lemma no_8_0_v443 : search 8 0 v443 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v379 : search 9 0 v379 = false := by
  apply reject_step 8 0 v379 [] [v380,v381,v382,v383,v384,v385,v386,v387,v388,v389,v390,v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v406,v407,v408,v409,v410,v411,v412,v413,v414,v415,v416,v417,v418,v419,v420,v421,v422,v423,v424,v425,v426,v427,v428,v429,v430,v431,v432,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v380
    · exact no_8_0_v381
    · exact no_8_0_v382
    · exact no_8_0_v383
    · exact no_8_0_v384
    · exact no_8_0_v385
    · exact no_8_0_v386
    · exact no_8_0_v387
    · exact no_8_0_v388
    · exact no_8_0_v389
    · exact no_8_0_v390
    · exact no_8_0_v391
    · exact no_8_0_v392
    · exact no_8_0_v393
    · exact no_8_0_v394
    · exact no_8_0_v395
    · exact no_8_0_v396
    · exact no_8_0_v397
    · exact no_8_0_v398
    · exact no_8_0_v399
    · exact no_8_0_v400
    · exact no_8_0_v401
    · exact no_8_0_v402
    · exact no_8_0_v403
    · exact no_8_0_v404
    · exact no_8_0_v405
    · exact no_8_0_v406
    · exact no_8_0_v407
    · exact no_8_0_v408
    · exact no_8_0_v409
    · exact no_8_0_v410
    · exact no_8_0_v411
    · exact no_8_0_v412
    · exact no_8_0_v413
    · exact no_8_0_v414
    · exact no_8_0_v415
    · exact no_8_0_v416
    · exact no_8_0_v417
    · exact no_8_0_v418
    · exact no_8_0_v419
    · exact no_8_0_v420
    · exact no_8_0_v421
    · exact no_8_0_v422
    · exact no_8_0_v423
    · exact no_8_0_v424
    · exact no_8_0_v425
    · exact no_8_0_v426
    · exact no_8_0_v427
    · exact no_8_0_v428
    · exact no_8_0_v429
    · exact no_8_0_v430
    · exact no_8_0_v431
    · exact no_8_0_v432
    · exact no_8_0_v433
    · exact no_8_0_v434
    · exact no_8_0_v435
    · exact no_8_0_v436
    · exact no_8_0_v437
    · exact no_8_0_v438
    · exact no_8_0_v439
    · exact no_8_0_v440
    · exact no_8_0_v441
    · exact no_8_0_v442
    · exact no_8_0_v443
  · decide +kernel

private def v444 : List Sig := [w81,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v444 : search 9 0 v444 = false := by decide +kernel

private def v445 : List Sig := [w50,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v445 : search 9 0 v445 = false := by decide +kernel

private def v446 : List Sig := [w51,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v446 : search 9 0 v446 = false := by decide +kernel

private def v447 : List Sig := [w54,raw4,raw2,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v447 : search 9 0 v447 = false := by decide +kernel

private def v448 : List Sig := [w55,raw4,raw2,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v448 : search 9 0 v448 = false := by decide +kernel

private def v449 : List Sig := [w56,raw4,raw5,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v449 : search 9 0 v449 = false := by decide +kernel

private def v450 : List Sig := [w57,raw4,raw0,raw1,raw2,raw3,raw6,raw7]

private def w135 : Sig := bin false w57 raw6

private def v451 : List Sig := [w135,w57,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v451 : search 8 0 v451 = false := by decide +kernel

private def v452 : List Sig := [w135,w57,raw6,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v452 : search 8 0 v452 = false := by decide +kernel

private def w136 : Sig := bin true w57 raw6

private def v453 : List Sig := [w136,w57,raw6,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v453 : search 8 0 v453 = false := by decide +kernel

private def w137 : Sig := bin false w57 raw7

private def v454 : List Sig := [w137,w57,raw7,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v454 : search 8 0 v454 = false := by decide +kernel

private def w138 : Sig := bin true w57 raw7

private def v455 : List Sig := [w138,w57,raw7,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v455 : search 8 0 v455 = false := by decide +kernel

private def v456 : List Sig := [w54,raw4,raw2,w57,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v456 : search 8 0 v456 = false := by decide +kernel

private def v457 : List Sig := [w55,raw4,raw2,w57,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v457 : search 8 0 v457 = false := by decide +kernel

private def v458 : List Sig := [w82,raw4,w57,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v458 : search 8 0 v458 = false := by decide +kernel

private def v459 : List Sig := [w82,raw4,raw6,w57,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v459 : search 8 0 v459 = false := by decide +kernel

private def v460 : List Sig := [w83,raw4,raw6,w57,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v460 : search 8 0 v460 = false := by decide +kernel

private def v461 : List Sig := [w58,raw4,raw7,w57,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v461 : search 8 0 v461 = false := by decide +kernel

private def v462 : List Sig := [w59,raw4,w57,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v462 : search 8 0 v462 = false := by decide +kernel

private def v463 : List Sig := [w59,raw4,raw7,w57,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v463 : search 8 0 v463 = false := by decide +kernel

private def w139 : Sig := bin false raw0 w57

private def v464 : List Sig := [w139,raw0,w57,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v464 : search 8 0 v464 = false := by decide +kernel

private def w140 : Sig := bin true raw0 w57

private def v465 : List Sig := [w140,raw0,w57,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v465 : search 8 0 v465 = false := by decide +kernel

private def v466 : List Sig := [w14,raw0,raw4,w57,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v466 : search 8 0 v466 = false := by decide +kernel

private def v467 : List Sig := [w15,raw0,raw4,w57,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v467 : search 8 0 v467 = false := by decide +kernel

private def v468 : List Sig := [w8,raw0,raw1,w57,raw4,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v468 : search 8 0 v468 = false := by decide +kernel

private def v469 : List Sig := [w9,raw0,raw1,w57,raw4,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v469 : search 8 0 v469 = false := by decide +kernel

private def v470 : List Sig := [w10,raw0,raw2,w57,raw4,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v470 : search 8 0 v470 = false := by decide +kernel

private def v471 : List Sig := [w11,raw0,raw2,w57,raw4,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v471 : search 8 0 v471 = false := by decide +kernel

private def v472 : List Sig := [w12,raw0,raw3,w57,raw4,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v472 : search 8 0 v472 = false := by decide +kernel

private def v473 : List Sig := [w13,raw0,raw3,w57,raw4,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v473 : search 8 0 v473 = false := by decide +kernel

private def v474 : List Sig := [w18,raw0,raw6,w57,raw4,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v474 : search 8 0 v474 = false := by decide +kernel

private def v475 : List Sig := [w19,raw0,w57,raw4,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v475 : search 8 0 v475 = false := by decide +kernel

private def v476 : List Sig := [w19,raw0,raw6,w57,raw4,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v476 : search 8 0 v476 = false := by decide +kernel

private def v477 : List Sig := [w22,raw0,w57,raw4,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v477 : search 8 0 v477 = false := by decide +kernel

private def v478 : List Sig := [w22,raw0,raw7,w57,raw4,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v478 : search 8 0 v478 = false := by decide +kernel

private def v479 : List Sig := [w23,raw0,raw7,w57,raw4,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v479 : search 8 0 v479 = false := by decide +kernel

private def w141 : Sig := bin false raw1 w57

private def v480 : List Sig := [w141,raw1,w57,raw4,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v480 : search 8 0 v480 = false := by decide +kernel

private def w142 : Sig := bin true raw1 w57

private def v481 : List Sig := [w142,raw1,w57,raw4,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v481 : search 8 0 v481 = false := by decide +kernel

private def v482 : List Sig := [w30,raw1,raw4,w57,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v482 : search 8 0 v482 = false := by decide +kernel

private def v483 : List Sig := [w31,raw1,raw4,w57,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v483 : search 8 0 v483 = false := by decide +kernel

private def v484 : List Sig := [w26,raw1,raw2,w57,raw4,raw0,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v484 : search 8 0 v484 = false := by decide +kernel

private def v485 : List Sig := [w27,raw1,raw2,w57,raw4,raw0,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v485 : search 8 0 v485 = false := by decide +kernel

private def v486 : List Sig := [w28,raw1,raw3,w57,raw4,raw0,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v486 : search 8 0 v486 = false := by decide +kernel

private def v487 : List Sig := [w29,raw1,raw3,w57,raw4,raw0,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v487 : search 8 0 v487 = false := by decide +kernel

private def v488 : List Sig := [w76,raw1,raw6,w57,raw4,raw0,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v488 : search 8 0 v488 = false := by decide +kernel

private def v489 : List Sig := [w77,raw1,raw6,w57,raw4,raw0,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v489 : search 8 0 v489 = false := by decide +kernel

private def v490 : List Sig := [w34,raw1,raw7,w57,raw4,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v490 : search 8 0 v490 = false := by decide +kernel

private def v491 : List Sig := [w35,raw1,w57,raw4,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v491 : search 8 0 v491 = false := by decide +kernel

private def v492 : List Sig := [w35,raw1,raw7,w57,raw4,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v492 : search 8 0 v492 = false := by decide +kernel

private def w143 : Sig := bin false raw2 w57

private def v493 : List Sig := [w143,raw2,w57,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v493 : search 8 0 v493 = false := by decide +kernel

private def v494 : List Sig := [w109,raw2,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v494 : search 8 0 v494 = false := by decide +kernel

private def v495 : List Sig := [w109,raw2,w57,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v495 : search 8 0 v495 = false := by decide +kernel

private def v496 : List Sig := [w78,raw2,raw6,w57,raw4,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v496 : search 8 0 v496 = false := by decide +kernel

private def v497 : List Sig := [w79,raw2,raw6,w57,raw4,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v497 : search 8 0 v497 = false := by decide +kernel

private def v498 : List Sig := [w40,raw2,raw7,w57,raw4,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v498 : search 8 0 v498 = false := by decide +kernel

private def v499 : List Sig := [w41,raw2,raw7,w57,raw4,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v499 : search 8 0 v499 = false := by decide +kernel

private def w144 : Sig := bin false raw3 w57

private def v500 : List Sig := [w144,raw3,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v500 : search 8 0 v500 = false := by decide +kernel

private def v501 : List Sig := [w144,raw3,w57,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v501 : search 8 0 v501 = false := by decide +kernel

private def w145 : Sig := bin true raw3 w57

private def v502 : List Sig := [w145,raw3,w57,raw4,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v502 : search 8 0 v502 = false := by decide +kernel

private def v503 : List Sig := [w46,raw3,raw4,w57,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v503 : search 8 0 v503 = false := by decide +kernel

private def v504 : List Sig := [w47,raw3,w57,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v504 : search 8 0 v504 = false := by decide +kernel

private def v505 : List Sig := [w47,raw3,raw4,w57,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v505 : search 8 0 v505 = false := by decide +kernel

private def v506 : List Sig := [w44,raw3,raw2,w57,raw4,raw0,raw1,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v506 : search 8 0 v506 = false := by decide +kernel

private def v507 : List Sig := [w45,raw3,raw2,w57,raw4,raw0,raw1,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v507 : search 8 0 v507 = false := by decide +kernel

private def v508 : List Sig := [w80,raw3,raw6,w57,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v508 : search 8 0 v508 = false := by decide +kernel

private def v509 : List Sig := [w81,raw3,w57,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v509 : search 8 0 v509 = false := by decide +kernel

private def v510 : List Sig := [w81,raw3,raw6,w57,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v510 : search 8 0 v510 = false := by decide +kernel

private def v511 : List Sig := [w50,raw3,raw7,w57,raw4,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v511 : search 8 0 v511 = false := by decide +kernel

private def v512 : List Sig := [w51,raw3,raw7,w57,raw4,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v512 : search 8 0 v512 = false := by decide +kernel

private def v513 : List Sig := [w110,raw6,raw7,w57,raw4,raw0,raw1,raw2,raw3]

set_option maxRecDepth 32768 in
private lemma no_8_0_v513 : search 8 0 v513 = false := by decide +kernel

private def v514 : List Sig := [w111,raw6,raw7,w57,raw4,raw0,raw1,raw2,raw3]

set_option maxRecDepth 32768 in
private lemma no_8_0_v514 : search 8 0 v514 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v450 : search 9 0 v450 = false := by
  apply reject_step 8 0 v450 [] [v451,v452,v453,v454,v455,v456,v457,v458,v459,v460,v461,v462,v463,v464,v465,v466,v467,v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,v483,v484,v485,v486,v487,v488,v489,v490,v491,v492,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v451
    · exact no_8_0_v452
    · exact no_8_0_v453
    · exact no_8_0_v454
    · exact no_8_0_v455
    · exact no_8_0_v456
    · exact no_8_0_v457
    · exact no_8_0_v458
    · exact no_8_0_v459
    · exact no_8_0_v460
    · exact no_8_0_v461
    · exact no_8_0_v462
    · exact no_8_0_v463
    · exact no_8_0_v464
    · exact no_8_0_v465
    · exact no_8_0_v466
    · exact no_8_0_v467
    · exact no_8_0_v468
    · exact no_8_0_v469
    · exact no_8_0_v470
    · exact no_8_0_v471
    · exact no_8_0_v472
    · exact no_8_0_v473
    · exact no_8_0_v474
    · exact no_8_0_v475
    · exact no_8_0_v476
    · exact no_8_0_v477
    · exact no_8_0_v478
    · exact no_8_0_v479
    · exact no_8_0_v480
    · exact no_8_0_v481
    · exact no_8_0_v482
    · exact no_8_0_v483
    · exact no_8_0_v484
    · exact no_8_0_v485
    · exact no_8_0_v486
    · exact no_8_0_v487
    · exact no_8_0_v488
    · exact no_8_0_v489
    · exact no_8_0_v490
    · exact no_8_0_v491
    · exact no_8_0_v492
    · exact no_8_0_v493
    · exact no_8_0_v494
    · exact no_8_0_v495
    · exact no_8_0_v496
    · exact no_8_0_v497
    · exact no_8_0_v498
    · exact no_8_0_v499
    · exact no_8_0_v500
    · exact no_8_0_v501
    · exact no_8_0_v502
    · exact no_8_0_v503
    · exact no_8_0_v504
    · exact no_8_0_v505
    · exact no_8_0_v506
    · exact no_8_0_v507
    · exact no_8_0_v508
    · exact no_8_0_v509
    · exact no_8_0_v510
    · exact no_8_0_v511
    · exact no_8_0_v512
    · exact no_8_0_v513
    · exact no_8_0_v514
  · decide +kernel

private def v515 : List Sig := [w57,raw4,raw5,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v515 : search 9 0 v515 = false := by decide +kernel

private def v516 : List Sig := [w82,raw4,raw0,raw1,raw2,raw3,raw5,raw7]

private def w146 : Sig := bin false w82 raw2

private def v517 : List Sig := [w146,w82,raw2,raw4,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v517 : search 8 0 v517 = false := by decide +kernel

private def w147 : Sig := bin true w82 raw2

private def v518 : List Sig := [w147,w82,raw4,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v518 : search 8 0 v518 = false := by decide +kernel

private def v519 : List Sig := [w147,w82,raw2,raw4,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v519 : search 8 0 v519 = false := by decide +kernel

private def w148 : Sig := bin false w82 raw5

private def v520 : List Sig := [w148,w82,raw5,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v520 : search 8 0 v520 = false := by decide +kernel

private def w149 : Sig := bin true w82 raw5

private def v521 : List Sig := [w149,w82,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v521 : search 8 0 v521 = false := by decide +kernel

private def v522 : List Sig := [w149,w82,raw5,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v522 : search 8 0 v522 = false := by decide +kernel

private def w150 : Sig := bin false w82 raw7

private def v523 : List Sig := [w150,w82,raw7,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v523 : search 8 0 v523 = false := by decide +kernel

private def w151 : Sig := bin true w82 raw7

private def v524 : List Sig := [w151,w82,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v524 : search 8 0 v524 = false := by decide +kernel

private def v525 : List Sig := [w151,w82,raw7,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v525 : search 8 0 v525 = false := by decide +kernel

private def v526 : List Sig := [w54,raw4,raw2,w82,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v526 : search 8 0 v526 = false := by decide +kernel

private def v527 : List Sig := [w55,raw4,raw2,w82,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v527 : search 8 0 v527 = false := by decide +kernel

private def v528 : List Sig := [w56,raw4,raw5,w82,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v528 : search 8 0 v528 = false := by decide +kernel

private def v529 : List Sig := [w57,raw4,w82,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v529 : search 8 0 v529 = false := by decide +kernel

private def v530 : List Sig := [w57,raw4,raw5,w82,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v530 : search 8 0 v530 = false := by decide +kernel

private def v531 : List Sig := [w58,raw4,raw7,w82,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v531 : search 8 0 v531 = false := by decide +kernel

private def v532 : List Sig := [w59,raw4,w82,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v532 : search 8 0 v532 = false := by decide +kernel

private def v533 : List Sig := [w59,raw4,raw7,w82,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v533 : search 8 0 v533 = false := by decide +kernel

private def w152 : Sig := bin false raw0 w82

private def v534 : List Sig := [w152,raw0,w82,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v534 : search 8 0 v534 = false := by decide +kernel

private def w153 : Sig := bin true raw0 w82

private def v535 : List Sig := [w153,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v535 : search 8 0 v535 = false := by decide +kernel

private def v536 : List Sig := [w153,raw0,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v536 : search 8 0 v536 = false := by decide +kernel

private def v537 : List Sig := [w153,w82,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v537 : search 8 0 v537 = false := by decide +kernel

private def v538 : List Sig := [w153,raw0,w82,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v538 : search 8 0 v538 = false := by decide +kernel

private def v539 : List Sig := [w14,raw0,raw4,w82,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v539 : search 8 0 v539 = false := by decide +kernel

private def v540 : List Sig := [w15,raw0,raw4,w82,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v540 : search 8 0 v540 = false := by decide +kernel

private def v541 : List Sig := [w8,raw0,raw1,w82,raw4,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v541 : search 8 0 v541 = false := by decide +kernel

private def v542 : List Sig := [w9,raw0,raw1,w82,raw4,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v542 : search 8 0 v542 = false := by decide +kernel

private def v543 : List Sig := [w10,raw0,raw2,w82,raw4,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v543 : search 8 0 v543 = false := by decide +kernel

private def v544 : List Sig := [w11,raw0,raw2,w82,raw4,raw1,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v544 : search 8 0 v544 = false := by decide +kernel

private def v545 : List Sig := [w12,raw0,raw3,w82,raw4,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v545 : search 8 0 v545 = false := by decide +kernel

private def v546 : List Sig := [w13,raw0,raw3,w82,raw4,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v546 : search 8 0 v546 = false := by decide +kernel

private def v547 : List Sig := [w16,raw0,raw5,w82,raw4,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v547 : search 8 0 v547 = false := by decide +kernel

private def v548 : List Sig := [w17,raw0,raw5,w82,raw4,raw1,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v548 : search 8 0 v548 = false := by decide +kernel

private def v549 : List Sig := [w22,raw0,w82,raw4,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v549 : search 8 0 v549 = false := by decide +kernel

private def v550 : List Sig := [w22,raw0,raw7,w82,raw4,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v550 : search 8 0 v550 = false := by decide +kernel

private def v551 : List Sig := [w23,raw0,raw7,w82,raw4,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v551 : search 8 0 v551 = false := by decide +kernel

private def w154 : Sig := bin false raw1 w82

private def v552 : List Sig := [w154,raw1,w82,raw4,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v552 : search 8 0 v552 = false := by decide +kernel

private def w155 : Sig := bin true raw1 w82

private def v553 : List Sig := [w155,w82,raw4,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v553 : search 8 0 v553 = false := by decide +kernel

private def v554 : List Sig := [w155,raw1,w82,raw4,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v554 : search 8 0 v554 = false := by decide +kernel

private def v555 : List Sig := [w30,raw1,raw4,w82,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v555 : search 8 0 v555 = false := by decide +kernel

private def v556 : List Sig := [w31,raw1,raw4,w82,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v556 : search 8 0 v556 = false := by decide +kernel

private def v557 : List Sig := [w26,raw1,raw2,w82,raw4,raw0,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v557 : search 8 0 v557 = false := by decide +kernel

private def v558 : List Sig := [w27,raw1,raw2,w82,raw4,raw0,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v558 : search 8 0 v558 = false := by decide +kernel

private def v559 : List Sig := [w28,raw1,raw3,w82,raw4,raw0,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v559 : search 8 0 v559 = false := by decide +kernel

private def v560 : List Sig := [w29,raw1,raw3,w82,raw4,raw0,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v560 : search 8 0 v560 = false := by decide +kernel

private def v561 : List Sig := [w32,raw1,raw5,w82,raw4,raw0,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v561 : search 8 0 v561 = false := by decide +kernel

private def v562 : List Sig := [w33,raw1,raw5,w82,raw4,raw0,raw2,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v562 : search 8 0 v562 = false := by decide +kernel

private def v563 : List Sig := [w34,raw1,raw7,w82,raw4,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v563 : search 8 0 v563 = false := by decide +kernel

private def v564 : List Sig := [w35,raw1,w82,raw4,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v564 : search 8 0 v564 = false := by decide +kernel

private def v565 : List Sig := [w35,raw1,raw7,w82,raw4,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v565 : search 8 0 v565 = false := by decide +kernel

private def v566 : List Sig := [w38,raw2,raw5,w82,raw4,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v566 : search 8 0 v566 = false := by decide +kernel

private def v567 : List Sig := [w39,raw2,w82,raw4,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v567 : search 8 0 v567 = false := by decide +kernel

private def v568 : List Sig := [w39,raw2,raw5,w82,raw4,raw0,raw1,raw3,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v568 : search 8 0 v568 = false := by decide +kernel

private def v569 : List Sig := [w40,raw2,raw7,w82,raw4,raw0,raw1,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v569 : search 8 0 v569 = false := by decide +kernel

private def v570 : List Sig := [w41,raw2,raw7,w82,raw4,raw0,raw1,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v570 : search 8 0 v570 = false := by decide +kernel

private def w156 : Sig := bin false raw3 w82

private def v571 : List Sig := [w156,raw3,w82,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v571 : search 8 0 v571 = false := by decide +kernel

private def w157 : Sig := bin true raw3 w82

private def v572 : List Sig := [w157,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v572 : search 8 0 v572 = false := by decide +kernel

private def v573 : List Sig := [w157,raw3,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v573 : search 8 0 v573 = false := by decide +kernel

private def v574 : List Sig := [w157,w82,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v574 : search 8 0 v574 = false := by decide +kernel

private def v575 : List Sig := [w157,raw3,w82,raw4,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v575 : search 8 0 v575 = false := by decide +kernel

private def v576 : List Sig := [w46,raw3,raw4,w82,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v576 : search 8 0 v576 = false := by decide +kernel

private def v577 : List Sig := [w47,raw3,raw4,w82,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v577 : search 8 0 v577 = false := by decide +kernel

private def v578 : List Sig := [w44,raw3,raw2,w82,raw4,raw0,raw1,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v578 : search 8 0 v578 = false := by decide +kernel

private def v579 : List Sig := [w45,raw3,raw2,w82,raw4,raw0,raw1,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v579 : search 8 0 v579 = false := by decide +kernel

private def v580 : List Sig := [w48,raw3,w82,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v580 : search 8 0 v580 = false := by decide +kernel

private def v581 : List Sig := [w48,raw3,raw5,w82,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v581 : search 8 0 v581 = false := by decide +kernel

private def v582 : List Sig := [w49,raw3,raw5,w82,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 32768 in
private lemma no_8_0_v582 : search 8 0 v582 = false := by decide +kernel

private def v583 : List Sig := [w50,raw3,raw7,w82,raw4,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v583 : search 8 0 v583 = false := by decide +kernel

private def v584 : List Sig := [w51,raw3,raw7,w82,raw4,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v584 : search 8 0 v584 = false := by decide +kernel

private def v585 : List Sig := [w62,raw5,raw7,w82,raw4,raw0,raw1,raw2,raw3]

set_option maxRecDepth 32768 in
private lemma no_8_0_v585 : search 8 0 v585 = false := by decide +kernel

private def v586 : List Sig := [w63,raw5,raw7,w82,raw4,raw0,raw1,raw2,raw3]

set_option maxRecDepth 32768 in
private lemma no_8_0_v586 : search 8 0 v586 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v516 : search 9 0 v516 = false := by
  apply reject_step 8 0 v516 [] [v517,v518,v519,v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,v536,v537,v538,v539,v540,v541,v542,v543,v544,v545,v546,v547,v548,v549,v550,v551,v552,v553,v554,v555,v556,v557,v558,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568,v569,v570,v571,v572,v573,v574,v575,v576,v577,v578,v579,v580,v581,v582,v583,v584,v585,v586]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v517
    · exact no_8_0_v518
    · exact no_8_0_v519
    · exact no_8_0_v520
    · exact no_8_0_v521
    · exact no_8_0_v522
    · exact no_8_0_v523
    · exact no_8_0_v524
    · exact no_8_0_v525
    · exact no_8_0_v526
    · exact no_8_0_v527
    · exact no_8_0_v528
    · exact no_8_0_v529
    · exact no_8_0_v530
    · exact no_8_0_v531
    · exact no_8_0_v532
    · exact no_8_0_v533
    · exact no_8_0_v534
    · exact no_8_0_v535
    · exact no_8_0_v536
    · exact no_8_0_v537
    · exact no_8_0_v538
    · exact no_8_0_v539
    · exact no_8_0_v540
    · exact no_8_0_v541
    · exact no_8_0_v542
    · exact no_8_0_v543
    · exact no_8_0_v544
    · exact no_8_0_v545
    · exact no_8_0_v546
    · exact no_8_0_v547
    · exact no_8_0_v548
    · exact no_8_0_v549
    · exact no_8_0_v550
    · exact no_8_0_v551
    · exact no_8_0_v552
    · exact no_8_0_v553
    · exact no_8_0_v554
    · exact no_8_0_v555
    · exact no_8_0_v556
    · exact no_8_0_v557
    · exact no_8_0_v558
    · exact no_8_0_v559
    · exact no_8_0_v560
    · exact no_8_0_v561
    · exact no_8_0_v562
    · exact no_8_0_v563
    · exact no_8_0_v564
    · exact no_8_0_v565
    · exact no_8_0_v566
    · exact no_8_0_v567
    · exact no_8_0_v568
    · exact no_8_0_v569
    · exact no_8_0_v570
    · exact no_8_0_v571
    · exact no_8_0_v572
    · exact no_8_0_v573
    · exact no_8_0_v574
    · exact no_8_0_v575
    · exact no_8_0_v576
    · exact no_8_0_v577
    · exact no_8_0_v578
    · exact no_8_0_v579
    · exact no_8_0_v580
    · exact no_8_0_v581
    · exact no_8_0_v582
    · exact no_8_0_v583
    · exact no_8_0_v584
    · exact no_8_0_v585
    · exact no_8_0_v586
  · decide +kernel

private def v587 : List Sig := [w82,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v587 : search 9 0 v587 = false := by decide +kernel

private def v588 : List Sig := [w83,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v588 : search 9 0 v588 = false := by decide +kernel

private def v589 : List Sig := [w58,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v589 : search 9 0 v589 = false := by decide +kernel

private def v590 : List Sig := [w59,raw4,raw0,raw1,raw2,raw3,raw5,raw6]

private def v591 : List Sig := [w54,raw4,raw2,w59,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v591 : search 8 0 v591 = false := by decide +kernel

private def v592 : List Sig := [w55,raw4,raw2,w59,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v592 : search 8 0 v592 = false := by decide +kernel

private def v593 : List Sig := [w56,raw4,raw5,w59,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v593 : search 8 0 v593 = false := by decide +kernel

private def v594 : List Sig := [w57,raw4,w59,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v594 : search 8 0 v594 = false := by decide +kernel

private def v595 : List Sig := [w57,raw4,raw5,w59,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v595 : search 8 0 v595 = false := by decide +kernel

private def v596 : List Sig := [w82,raw4,w59,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v596 : search 8 0 v596 = false := by decide +kernel

private def v597 : List Sig := [w82,raw4,raw6,w59,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v597 : search 8 0 v597 = false := by decide +kernel

private def v598 : List Sig := [w83,raw4,raw6,w59,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v598 : search 8 0 v598 = false := by decide +kernel

private def w158 : Sig := bin false raw0 w59

private def v599 : List Sig := [w158,raw0,raw4,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v599 : search 8 0 v599 = false := by decide +kernel

private def v600 : List Sig := [w158,raw0,w59,raw4,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v600 : search 8 0 v600 = false := by decide +kernel

private def w159 : Sig := bin true raw0 w59

private def v601 : List Sig := [w159,raw0,w59,raw4,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v601 : search 8 0 v601 = false := by decide +kernel

private def v602 : List Sig := [w14,raw0,raw4,w59,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v602 : search 8 0 v602 = false := by decide +kernel

private def v603 : List Sig := [w15,raw0,w59,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v603 : search 8 0 v603 = false := by decide +kernel

private def v604 : List Sig := [w15,raw0,raw4,w59,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v604 : search 8 0 v604 = false := by decide +kernel

private def v605 : List Sig := [w8,raw0,raw1,w59,raw4,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v605 : search 8 0 v605 = false := by decide +kernel

private def v606 : List Sig := [w9,raw0,raw1,w59,raw4,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v606 : search 8 0 v606 = false := by decide +kernel

private def v607 : List Sig := [w10,raw0,raw2,w59,raw4,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v607 : search 8 0 v607 = false := by decide +kernel

private def v608 : List Sig := [w11,raw0,raw2,w59,raw4,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v608 : search 8 0 v608 = false := by decide +kernel

private def v609 : List Sig := [w12,raw0,raw3,w59,raw4,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v609 : search 8 0 v609 = false := by decide +kernel

private def v610 : List Sig := [w13,raw0,raw3,w59,raw4,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v610 : search 8 0 v610 = false := by decide +kernel

private def v611 : List Sig := [w16,raw0,raw5,w59,raw4,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v611 : search 8 0 v611 = false := by decide +kernel

private def v612 : List Sig := [w17,raw0,raw5,w59,raw4,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v612 : search 8 0 v612 = false := by decide +kernel

private def v613 : List Sig := [w18,raw0,raw6,w59,raw4,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v613 : search 8 0 v613 = false := by decide +kernel

private def v614 : List Sig := [w19,raw0,w59,raw4,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v614 : search 8 0 v614 = false := by decide +kernel

private def v615 : List Sig := [w19,raw0,raw6,w59,raw4,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v615 : search 8 0 v615 = false := by decide +kernel

private def w160 : Sig := bin false raw1 w59

private def v616 : List Sig := [w160,raw1,w59,raw4,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v616 : search 8 0 v616 = false := by decide +kernel

private def v617 : List Sig := [w93,raw1,raw4,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v617 : search 8 0 v617 = false := by decide +kernel

private def v618 : List Sig := [w93,raw1,w59,raw4,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v618 : search 8 0 v618 = false := by decide +kernel

private def v619 : List Sig := [w30,raw1,raw4,w59,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v619 : search 8 0 v619 = false := by decide +kernel

private def v620 : List Sig := [w31,raw1,raw4,w59,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v620 : search 8 0 v620 = false := by decide +kernel

private def v621 : List Sig := [w26,raw1,raw2,w59,raw4,raw0,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v621 : search 8 0 v621 = false := by decide +kernel

private def v622 : List Sig := [w27,raw1,raw2,w59,raw4,raw0,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v622 : search 8 0 v622 = false := by decide +kernel

private def v623 : List Sig := [w28,raw1,raw3,w59,raw4,raw0,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v623 : search 8 0 v623 = false := by decide +kernel

private def v624 : List Sig := [w29,raw1,raw3,w59,raw4,raw0,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v624 : search 8 0 v624 = false := by decide +kernel

private def v625 : List Sig := [w32,raw1,raw5,w59,raw4,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v625 : search 8 0 v625 = false := by decide +kernel

private def v626 : List Sig := [w33,raw1,raw5,w59,raw4,raw0,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v626 : search 8 0 v626 = false := by decide +kernel

private def v627 : List Sig := [w76,raw1,raw6,w59,raw4,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v627 : search 8 0 v627 = false := by decide +kernel

private def v628 : List Sig := [w77,raw1,raw6,w59,raw4,raw0,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v628 : search 8 0 v628 = false := by decide +kernel

private def w161 : Sig := bin false raw2 w59

private def v629 : List Sig := [w161,raw2,w59,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v629 : search 8 0 v629 = false := by decide +kernel

private def w162 : Sig := bin true raw2 w59

private def v630 : List Sig := [w162,raw2,w59,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v630 : search 8 0 v630 = false := by decide +kernel

private def v631 : List Sig := [w38,raw2,raw5,w59,raw4,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v631 : search 8 0 v631 = false := by decide +kernel

private def v632 : List Sig := [w39,raw2,w59,raw4,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v632 : search 8 0 v632 = false := by decide +kernel

private def v633 : List Sig := [w39,raw2,raw5,w59,raw4,raw0,raw1,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v633 : search 8 0 v633 = false := by decide +kernel

private def v634 : List Sig := [w78,raw2,raw6,w59,raw4,raw0,raw1,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v634 : search 8 0 v634 = false := by decide +kernel

private def v635 : List Sig := [w79,raw2,raw6,w59,raw4,raw0,raw1,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v635 : search 8 0 v635 = false := by decide +kernel

private def w163 : Sig := bin false raw3 w59

private def v636 : List Sig := [w163,raw3,w59,raw4,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v636 : search 8 0 v636 = false := by decide +kernel

private def w164 : Sig := bin true raw3 w59

private def v637 : List Sig := [w164,raw3,w59,raw4,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v637 : search 8 0 v637 = false := by decide +kernel

private def v638 : List Sig := [w46,raw3,raw4,w59,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v638 : search 8 0 v638 = false := by decide +kernel

private def v639 : List Sig := [w47,raw3,raw4,w59,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v639 : search 8 0 v639 = false := by decide +kernel

private def v640 : List Sig := [w44,raw3,raw2,w59,raw4,raw0,raw1,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v640 : search 8 0 v640 = false := by decide +kernel

private def v641 : List Sig := [w45,raw3,raw2,w59,raw4,raw0,raw1,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v641 : search 8 0 v641 = false := by decide +kernel

private def v642 : List Sig := [w48,raw3,w59,raw4,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v642 : search 8 0 v642 = false := by decide +kernel

private def v643 : List Sig := [w48,raw3,raw5,w59,raw4,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v643 : search 8 0 v643 = false := by decide +kernel

private def v644 : List Sig := [w49,raw3,raw5,w59,raw4,raw0,raw1,raw2,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v644 : search 8 0 v644 = false := by decide +kernel

private def v645 : List Sig := [w80,raw3,raw6,w59,raw4,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v645 : search 8 0 v645 = false := by decide +kernel

private def v646 : List Sig := [w81,raw3,w59,raw4,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v646 : search 8 0 v646 = false := by decide +kernel

private def v647 : List Sig := [w81,raw3,raw6,w59,raw4,raw0,raw1,raw2,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v647 : search 8 0 v647 = false := by decide +kernel

private def w165 : Sig := bin false raw5 w59

private def v648 : List Sig := [w165,raw5,w59,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v648 : search 8 0 v648 = false := by decide +kernel

private def v649 : List Sig := [w138,raw5,w59,raw4,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 32768 in
private lemma no_8_0_v649 : search 8 0 v649 = false := by decide +kernel

private def v650 : List Sig := [w84,raw5,raw6,w59,raw4,raw0,raw1,raw2,raw3]

set_option maxRecDepth 32768 in
private lemma no_8_0_v650 : search 8 0 v650 = false := by decide +kernel

private def v651 : List Sig := [w85,raw5,raw6,w59,raw4,raw0,raw1,raw2,raw3]

set_option maxRecDepth 32768 in
private lemma no_8_0_v651 : search 8 0 v651 = false := by decide +kernel

private def w166 : Sig := bin false raw6 w59

private def v652 : List Sig := [w166,w59,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v652 : search 8 0 v652 = false := by decide +kernel

private def v653 : List Sig := [w166,raw6,w59,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v653 : search 8 0 v653 = false := by decide +kernel

private def w167 : Sig := bin true raw6 w59

private def v654 : List Sig := [w167,raw6,w59,raw4,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 32768 in
private lemma no_8_0_v654 : search 8 0 v654 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_0_v590 : search 9 0 v590 = false := by
  apply reject_step 8 0 v590 [] [v591,v592,v593,v594,v595,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v650,v651,v652,v653,v654]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_8_0_v591
    · exact no_8_0_v592
    · exact no_8_0_v593
    · exact no_8_0_v594
    · exact no_8_0_v595
    · exact no_8_0_v596
    · exact no_8_0_v597
    · exact no_8_0_v598
    · exact no_8_0_v599
    · exact no_8_0_v600
    · exact no_8_0_v601
    · exact no_8_0_v602
    · exact no_8_0_v603
    · exact no_8_0_v604
    · exact no_8_0_v605
    · exact no_8_0_v606
    · exact no_8_0_v607
    · exact no_8_0_v608
    · exact no_8_0_v609
    · exact no_8_0_v610
    · exact no_8_0_v611
    · exact no_8_0_v612
    · exact no_8_0_v613
    · exact no_8_0_v614
    · exact no_8_0_v615
    · exact no_8_0_v616
    · exact no_8_0_v617
    · exact no_8_0_v618
    · exact no_8_0_v619
    · exact no_8_0_v620
    · exact no_8_0_v621
    · exact no_8_0_v622
    · exact no_8_0_v623
    · exact no_8_0_v624
    · exact no_8_0_v625
    · exact no_8_0_v626
    · exact no_8_0_v627
    · exact no_8_0_v628
    · exact no_8_0_v629
    · exact no_8_0_v630
    · exact no_8_0_v631
    · exact no_8_0_v632
    · exact no_8_0_v633
    · exact no_8_0_v634
    · exact no_8_0_v635
    · exact no_8_0_v636
    · exact no_8_0_v637
    · exact no_8_0_v638
    · exact no_8_0_v639
    · exact no_8_0_v640
    · exact no_8_0_v641
    · exact no_8_0_v642
    · exact no_8_0_v643
    · exact no_8_0_v644
    · exact no_8_0_v645
    · exact no_8_0_v646
    · exact no_8_0_v647
    · exact no_8_0_v648
    · exact no_8_0_v649
    · exact no_8_0_v650
    · exact no_8_0_v651
    · exact no_8_0_v652
    · exact no_8_0_v653
    · exact no_8_0_v654
  · decide +kernel

private def v655 : List Sig := [w59,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v655 : search 9 0 v655 = false := by decide +kernel

private def v656 : List Sig := [w84,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v656 : search 9 0 v656 = false := by decide +kernel

private def v657 : List Sig := [w85,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v657 : search 9 0 v657 = false := by decide +kernel

private def v658 : List Sig := [w62,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v658 : search 9 0 v658 = false := by decide +kernel

private def v659 : List Sig := [w63,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v659 : search 9 0 v659 = false := by decide +kernel

private def v660 : List Sig := [w110,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_9_0_v660 : search 9 0 v660 = false := by decide +kernel

private def v661 : List Sig := [w111,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 32768 in
private lemma no_9_0_v661 : search 9 0 v661 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma excluded0 : search 10 0 raw = false := by
  apply reject_step 9 0 raw [] [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v77,v78,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v228,v229,v230,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v376,v377,v378,v379,v444,v445,v446,v447,v448,v449,v450,v515,v516,v587,v588,v589,v590,v655,v656,v657,v658,v659,v660,v661]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_9_0_v1
    · exact no_9_0_v2
    · exact no_9_0_v3
    · exact no_9_0_v4
    · exact no_9_0_v5
    · exact no_9_0_v6
    · exact no_9_0_v7
    · exact no_9_0_v8
    · exact no_9_0_v9
    · exact no_9_0_v10
    · exact no_9_0_v11
    · exact no_9_0_v12
    · exact no_9_0_v77
    · exact no_9_0_v78
    · exact no_9_0_v149
    · exact no_9_0_v150
    · exact no_9_0_v151
    · exact no_9_0_v152
    · exact no_9_0_v153
    · exact no_9_0_v154
    · exact no_9_0_v155
    · exact no_9_0_v156
    · exact no_9_0_v157
    · exact no_9_0_v158
    · exact no_9_0_v159
    · exact no_9_0_v160
    · exact no_9_0_v161
    · exact no_9_0_v162
    · exact no_9_0_v228
    · exact no_9_0_v229
    · exact no_9_0_v230
    · exact no_9_0_v296
    · exact no_9_0_v297
    · exact no_9_0_v298
    · exact no_9_0_v299
    · exact no_9_0_v300
    · exact no_9_0_v301
    · exact no_9_0_v302
    · exact no_9_0_v303
    · exact no_9_0_v304
    · exact no_9_0_v305
    · exact no_9_0_v376
    · exact no_9_0_v377
    · exact no_9_0_v378
    · exact no_9_0_v379
    · exact no_9_0_v444
    · exact no_9_0_v445
    · exact no_9_0_v446
    · exact no_9_0_v447
    · exact no_9_0_v448
    · exact no_9_0_v449
    · exact no_9_0_v450
    · exact no_9_0_v515
    · exact no_9_0_v516
    · exact no_9_0_v587
    · exact no_9_0_v588
    · exact no_9_0_v589
    · exact no_9_0_v590
    · exact no_9_0_v655
    · exact no_9_0_v656
    · exact no_9_0_v657
    · exact no_9_0_v658
    · exact no_9_0_v659
    · exact no_9_0_v660
    · exact no_9_0_v661
  · decide +kernel

private def w168 : Sig := neg raw0

private def v662 : List Sig := [w168,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v662 : search 9 0 v662 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v1 : search 9 1 v1 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v2 : search 9 1 v2 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v3 : search 9 1 v3 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v4 : search 9 1 v4 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v5 : search 9 1 v5 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v6 : search 9 1 v6 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v7 : search 9 1 v7 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v8 : search 9 1 v8 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v9 : search 9 1 v9 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v10 : search 9 1 v10 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v11 : search 9 1 v11 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v12 : search 9 1 v12 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v77 : search 9 1 v77 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v78 : search 9 1 v78 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v149 : search 9 1 v149 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v150 : search 9 1 v150 = false := by decide +kernel

private def w169 : Sig := neg raw1

private def v663 : List Sig := [w169,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v663 : search 9 0 v663 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v151 : search 9 1 v151 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v152 : search 9 1 v152 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v153 : search 9 1 v153 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v154 : search 9 1 v154 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v155 : search 9 1 v155 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v156 : search 9 1 v156 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v157 : search 9 1 v157 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v158 : search 9 1 v158 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v159 : search 9 1 v159 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v160 : search 9 1 v160 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v161 : search 9 1 v161 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v162 : search 9 1 v162 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v228 : search 9 1 v228 = false := by decide +kernel

private def w170 : Sig := neg raw2

private def v664 : List Sig := [w170,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v664 : search 9 0 v664 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v229 : search 9 1 v229 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v230 : search 9 1 v230 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v296 : search 9 1 v296 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v297 : search 9 1 v297 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v298 : search 9 1 v298 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v299 : search 9 1 v299 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v300 : search 9 1 v300 = false := by decide +kernel

private def w171 : Sig := neg raw3

private def v665 : List Sig := [w171,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v665 : search 9 0 v665 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v301 : search 9 1 v301 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v302 : search 9 1 v302 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v303 : search 9 1 v303 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v304 : search 9 1 v304 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v305 : search 9 1 v305 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v376 : search 9 1 v376 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v377 : search 9 1 v377 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v378 : search 9 1 v378 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v379 : search 9 1 v379 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v444 : search 9 1 v444 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v445 : search 9 1 v445 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v446 : search 9 1 v446 = false := by decide +kernel

private def w172 : Sig := neg raw4

private def v666 : List Sig := [w172,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v666 : search 9 0 v666 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v447 : search 9 1 v447 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v448 : search 9 1 v448 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v449 : search 9 1 v449 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v450 : search 9 1 v450 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v515 : search 9 1 v515 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v516 : search 9 1 v516 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v587 : search 9 1 v587 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v588 : search 9 1 v588 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v589 : search 9 1 v589 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v590 : search 9 1 v590 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v655 : search 9 1 v655 = false := by decide +kernel

private def w173 : Sig := neg raw5

private def v667 : List Sig := [w173,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v667 : search 9 0 v667 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v656 : search 9 1 v656 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v657 : search 9 1 v657 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v658 : search 9 1 v658 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v659 : search 9 1 v659 = false := by decide +kernel

private def w174 : Sig := neg raw6

private def v668 : List Sig := [w174,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_0_v668 : search 9 0 v668 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v660 : search 9 1 v660 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v661 : search 9 1 v661 = false := by decide +kernel

private def w175 : Sig := neg raw7

private def v669 : List Sig := [w175,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_0_v669 : search 9 0 v669 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma excluded1 : search 10 1 raw = false := by
  apply reject_step 9 1 raw [v662,v663,v664,v665,v666,v667,v668,v669] [v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v77,v78,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161,v162,v228,v229,v230,v296,v297,v298,v299,v300,v301,v302,v303,v304,v305,v376,v377,v378,v379,v444,v445,v446,v447,v448,v449,v450,v515,v516,v587,v588,v589,v590,v655,v656,v657,v658,v659,v660,v661]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_9_0_v662
    · exact no_9_0_v663
    · exact no_9_0_v664
    · exact no_9_0_v665
    · exact no_9_0_v666
    · exact no_9_0_v667
    · exact no_9_0_v668
    · exact no_9_0_v669
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_9_1_v1
    · exact no_9_1_v2
    · exact no_9_1_v3
    · exact no_9_1_v4
    · exact no_9_1_v5
    · exact no_9_1_v6
    · exact no_9_1_v7
    · exact no_9_1_v8
    · exact no_9_1_v9
    · exact no_9_1_v10
    · exact no_9_1_v11
    · exact no_9_1_v12
    · exact no_9_1_v77
    · exact no_9_1_v78
    · exact no_9_1_v149
    · exact no_9_1_v150
    · exact no_9_1_v151
    · exact no_9_1_v152
    · exact no_9_1_v153
    · exact no_9_1_v154
    · exact no_9_1_v155
    · exact no_9_1_v156
    · exact no_9_1_v157
    · exact no_9_1_v158
    · exact no_9_1_v159
    · exact no_9_1_v160
    · exact no_9_1_v161
    · exact no_9_1_v162
    · exact no_9_1_v228
    · exact no_9_1_v229
    · exact no_9_1_v230
    · exact no_9_1_v296
    · exact no_9_1_v297
    · exact no_9_1_v298
    · exact no_9_1_v299
    · exact no_9_1_v300
    · exact no_9_1_v301
    · exact no_9_1_v302
    · exact no_9_1_v303
    · exact no_9_1_v304
    · exact no_9_1_v305
    · exact no_9_1_v376
    · exact no_9_1_v377
    · exact no_9_1_v378
    · exact no_9_1_v379
    · exact no_9_1_v444
    · exact no_9_1_v445
    · exact no_9_1_v446
    · exact no_9_1_v447
    · exact no_9_1_v448
    · exact no_9_1_v449
    · exact no_9_1_v450
    · exact no_9_1_v515
    · exact no_9_1_v516
    · exact no_9_1_v587
    · exact no_9_1_v588
    · exact no_9_1_v589
    · exact no_9_1_v590
    · exact no_9_1_v655
    · exact no_9_1_v656
    · exact no_9_1_v657
    · exact no_9_1_v658
    · exact no_9_1_v659
    · exact no_9_1_v660
    · exact no_9_1_v661
  · decide +kernel

private def v670 : List Sig := [w168,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_1_v670 : search 9 1 v670 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v662 : search 9 1 v662 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v12 : search 9 2 v12 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v78 : search 9 2 v78 = false := by decide +kernel

private def v671 : List Sig := [w169,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_1_v671 : search 9 1 v671 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v663 : search 9 1 v663 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v162 : search 9 2 v162 = false := by decide +kernel

private def v672 : List Sig := [w170,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_1_v672 : search 9 1 v672 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v664 : search 9 1 v664 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v230 : search 9 2 v230 = false := by decide +kernel

private def v673 : List Sig := [w171,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_1_v673 : search 9 1 v673 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v665 : search 9 1 v665 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v305 : search 9 2 v305 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v379 : search 9 2 v379 = false := by decide +kernel

private def v674 : List Sig := [w172,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_1_v674 : search 9 1 v674 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v666 : search 9 1 v666 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v450 : search 9 2 v450 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v516 : search 9 2 v516 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_2_v590 : search 9 2 v590 = false := by decide +kernel

private def v675 : List Sig := [w173,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_1_v675 : search 9 1 v675 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v667 : search 9 1 v667 = false := by decide +kernel

private def v676 : List Sig := [w174,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 32768 in
private lemma no_9_1_v676 : search 9 1 v676 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v668 : search 9 1 v668 = false := by decide +kernel

private def v677 : List Sig := [w175,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 32768 in
private lemma no_9_1_v677 : search 9 1 v677 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma no_9_1_v669 : search 9 1 v669 = false := by decide +kernel

set_option maxRecDepth 32768 in
private lemma excluded2 : search 10 2 raw = false := by
  apply reject_step 9 2 raw [v670,v662,v671,v663,v672,v664,v673,v665,v674,v666,v675,v667,v676,v668,v677,v669] [v12,v78,v162,v230,v305,v379,v450,v516,v590]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_9_1_v670
    · exact no_9_1_v662
    · exact no_9_1_v671
    · exact no_9_1_v663
    · exact no_9_1_v672
    · exact no_9_1_v664
    · exact no_9_1_v673
    · exact no_9_1_v665
    · exact no_9_1_v674
    · exact no_9_1_v666
    · exact no_9_1_v675
    · exact no_9_1_v667
    · exact no_9_1_v676
    · exact no_9_1_v668
    · exact no_9_1_v677
    · exact no_9_1_v669
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_9_2_v12
    · exact no_9_2_v78
    · exact no_9_2_v162
    · exact no_9_2_v230
    · exact no_9_2_v305
    · exact no_9_2_v379
    · exact no_9_2_v450
    · exact no_9_2_v516
    · exact no_9_2_v590
  · decide +kernel

set_option maxRecDepth 32768 in
private lemma excluded3 : search 10 3 raw = false := by decide +kernel

end PEqualNP.Outside.G550

open PEqualNP.Outside.G550

theorem PEqualNP.Outside.L_meta_550 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 0 && x 7)) s → 11 ≤ s := by
  intro s hs
  by_contra h
  obtain ⟨C,hg,hc,he⟩ := hs
  obtain ⟨t,ht,found⟩ := circuit_search C (by omega) hg he
  interval_cases t <;> simp_all only [excluded0,excluded1,excluded2,excluded3,Bool.false_eq_true]
