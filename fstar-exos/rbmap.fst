module RBMap
// build via: del *.fs && fstar map.fst --codegen FSharp

type as_order (a:eqtype) (f: a->a->Tot bool) =
    (forall a1 a2. (f a1 a2) /\ (f a2 a1) ==> a1 == a2)

type total_order (a:eqtype) (f: a->a->Tot bool) =
    (forall a1  a2. (f a1 a2) /\ (f a2 a1) ==> a1 == a2)     // anti-symmetry
    /\ (forall a1 a2 a3. (f a1 a2) /\ (f a2 a3) ==> f a1 a3) // transitivity
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                    // totality
type cmp (a: eqtype) = f:(a -> a -> Tot bool){ total_order a f }
// adaptation of RBTree in examples
// ?? is this usable (the one liner below, that is)
// type key x f = x:eqtype{ f: cmp x }
// todo: add conditions on k<->v link

val cmpPair: #a1:eqtype -> #a2:eqtype
    -> f1:cmp a1
    -> f2:cmp a2
    -> (a1*a2) -> (a1*a2) -> Tot bool
let cmpPair (#a1:eqtype) (#a2:eqtype) af1 af2 (x1, x2) (y1, y2) =
    if (af1 x1 y1)
        then if x1 = y1
           then af2 x2 y2
           else true
        else false

val cmpAS: #a1:eqtype -> #a2:eqtype
    -> f1:cmp a1
    -> f2:cmp a2
    -> x1:a1
    -> x2:a2
    -> y1:a1
    -> y2:a2
    -> c1: ((cmpPair f1 f2 (x1,x2) (y1,y2)) == true)
    -> c2: ((cmpPair f1 f2 (y1,y2) (x1,x2)) == true)
    -> Lemma ((x1, x2) = (y1, y2))
let cmpAS (#a1:eqtype) (#a2:eqtype) af1 af2 x1 x2 y1 y2 c1 c2 =
    let _ = assert (af1 x1 y1) in
    let _ = assert (af1 y1 x1) in
    let _ = assert (x1 = y1) in
    let _ = assert (cmpPair af1 af2 (x1,x2) (y1,y2) = af2 x2 y2) in
    let _ = assert (cmpPair af1 af2 (y1,y2) (x1,x2) = af2 y2 x2) in
    ()

#set-options "--z3rlimit 20"
val cmpTRANS:  #a1:eqtype -> #a2:eqtype
    -> f1:cmp a1
    -> f2:cmp a2
    -> x1:a1
    -> x2:a2
    -> y1:a1
    -> y2:a2
    -> z1:a1
    -> z2:a2
    -> c1: ((cmpPair f1 f2 (x1,x2) (y1,y2)) == true)
    -> c2: ((cmpPair f1 f2 (y1,y2) (z1,z2)) == true)
    -> Lemma ((cmpPair f1 f2 (x1,x2) (z1,z2)) = true)
  let cmpTRANS (#a1:eqtype) (#a2:eqtype) af1 af2 x1 x2 y1 y2 z1 z2 c1 c2 =
      let _ = assert (af1 x1 y1) in
      let _ = assert (af1 y1 z1) in
      let _ = assert ((af1 x1 y1) /\ (af1 y1 z1) /\ (af1 x1 z1)) in
      let _ = assert ((not (x1 = y1)) \/ (af2 x2 y2)) in
      let _ = assert ((not (y1 = z1)) \/ (af2 y2 z2)) in
      let _ = assert ( (not (x1 = z1))
                \/ ((x1 = z1) /\ (af2 x2 y2) /\ (af2 y2 z2) /\ (af2 x2 z2))
              ) in
      ()

#set-options "--z3rlimit 20"
val cmpTOT: #a1:eqtype -> #a2:eqtype
   -> f1:cmp a1
   -> f2:cmp a2
   -> x1:a1
   -> x2:a2
   -> y1:a1
   -> y2:a2
   -> Lemma (((cmpPair f1 f2 (x1,x2) (y1,y2)) = true) \/
              ((cmpPair f1 f2 (y1,y2) (x1,x2)) = true))
let cmpTOT (#a1:eqtype) (#a2:eqtype) af1 af2 x1 x2 y1 y2 =
   let _ = assert (((not (af1 x1 y1)) /\ (af1 y1 x1))
         \/ ((not (af1 y1 x1)) /\ (af1 x1 y1))
         \/ ((af1 x1 y1) /\ (af1 y1 x1)) ) in
   let _ = assert ((af2 x2 y2) \/ (af2 y2 x2)) in
   let _ = assert( ((x1 = y1) /\
                     (((cmpPair af1 af2 (x1,x2) (y1,y2)) = true) \/
                      ((cmpPair af1 af2 (y1,y2) (x1,x2)) = true)))
                    \/ (not (x1 = y1))) in
   let _ = assert ( (x1 = y1)
                    \/ (((cmpPair af1 af2 (x1,x2) (y1,y2)) =
                        true) \/
                        ((cmpPair af1 af2 (y1,y2) (x1,x2)) =
                        true)) ) in
   ()

val toPairEqPattern: #a1:eqtype -> #a2:eqtype
   -> f1:cmp a1
   -> f2:cmp a2
   -> x: (a1*a2)
   -> y: (a1*a2)
   -> c1: ((cmpPair f1 f2 x y) == true)
   -> c2: ((cmpPair f1 f2 y x) == true)
   -> (x == y)
let toPairEqPattern (#t1:eqtype) (#t2:eqtype) af1 af2 a1 a2 c1 c2 =
   let f = (cmpPair af1 af2) in
   let (x1,x2) = a1 in
   let (y1,y2) = a2 in
   let _ = cmpAS af1 af2 x1 x2 y1 y2 c1 c2 in
   let _ = assert ((x1,x2) = (y1,y2)) in
   let _ = assert (a1 = a2) in
   admit()

#set-options "--z3rlimit 20"
val toPair: #a1:eqtype -> #a2:eqtype
   -> f1:cmp a1
   -> f2:cmp a2
   //-> f: ((a1*a2) -> (a1*a2) -> Tot bool){ total_order (a1*a2) f } // as_order
   -> f: cmp (a1 * a2)
let toPair (#t1:eqtype) (#t2:eqtype) af1 af2 =
   cmpPair af1 af2

// RB tree from exmaples
type color =
  | R
  | B

type rbtree (k: eqtype) v =
  | E
  | T: col:color
       -> left: rbtree k v
       -> key: k
       -> value: v
       -> right: rbtree k v
       -> rbtree k v
noeq type map k v =
  | M: f: cmp k -> rbt: rbtree k v -> map k v

val color_of: #k:eqtype -> #v:Type -> t:rbtree k v -> Tot color
let color_of (#k:eqtype) (#v:Type) t = match t with
    | E -> B
    | T c _ _ _ _ -> c

// black height of the tree - if all the leaves have same black height,
// else return None
val black_height: #k:eqtype -> #v:Type -> t:rbtree k v -> Tot (option nat)
let rec black_height (#k:eqtype) (#v:Type) t = match t with
    | E -> Some 0
    | T c a _ _ b  ->
        let hha = black_height a in
        let hhb = black_height b in
        match (hha, hhb) with
            | Some ha, Some hb ->
                if ha = hb then
                    if c = R then Some ha else Some (ha+1)
                else
                    None
            | _, _ -> None

// return the minimum element (key) in a T tree
val min_elt: #k:eqtype -> #v:Type -> t:rbtree k v -> Pure k
    (requires (b2t (T? t)))
    (ensures (fun r -> True))
let rec min_elt (#k:eqtype) (#v:Type) (T _ a x _ _) = match a with
    | E -> x
    | _ -> min_elt a

val max_elt: #k:eqtype -> #v:Type -> t:rbtree k v -> Pure k
    (requires (b2t (T? t)))
    (ensures (fun r -> True))
let rec max_elt (#k:eqtype) (#v:Type) (T _ _ x _ b) = match b with
    | E -> x
    | _ -> max_elt b

// root must be black
val r_inv: #k:eqtype -> #v:Type -> t:rbtree k v -> Tot bool
let r_inv (#k:eqtype) (#v:Type) t = color_of t = B

// evey red node must have black children
val c_inv: #k:eqtype -> #v:Type -> t:rbtree k v -> Tot bool
let rec c_inv (#k:eqtype) (#v:Type) t = match t with
    | E -> true
    | T R a _ _ b -> color_of a = B && color_of b = B && c_inv a && c_inv b
    | T B a _ _ b -> c_inv a && c_inv b

// black height of every leaf must be the same
val h_inv:  #k:eqtype -> #v:Type -> t:rbtree k v -> Tot bool
let h_inv (#k:eqtype) (#v:Type) t = Some? (black_height t)

// binary search tree invariant
// elts in left subtree > root > elements in right subtree
val k_inv: #k:eqtype -> #v:Type -> cmp k -> t:rbtree k v -> Tot bool
let rec k_inv (#k:eqtype) (#v:Type) c t  = match t with
  | E -> true
  | T _ E x w E -> true
  | T _ E x w b ->
      let b_min = min_elt b in
      (k_inv c b) && (c b_min x) && (not (b_min = x))
  | T _ a x w E ->
      let a_max = max_elt a in
      (k_inv c a) && (c x a_max) && (not (x = a_max))
  | T _ a x w b ->
      let a_max = max_elt a in
      let b_min = min_elt b in
      ((k_inv c a) && (k_inv c b)
          && (c x a_max) && (c b_min x)
          && (not (x = a_max)) && (not (b_min = x)))

val in_tree: #k:eqtype -> #v:Type -> t:rbtree k v -> kk:k -> Tot bool
let rec in_tree (#k:eqtype) (#v:Type) t kk = match t with
  | E -> false
  | T _ a x _ b -> in_tree a kk || kk = x || in_tree b kk

// Okasaki: insert the element at its best [red node] place
// then re-establish the red-black tree invariants
// not_c_inv : violation of c_inv
type not_c_inv (#k:eqtype) (#v:Type) (t:rbtree k v) =
  (T? t) /\ (T?.col t = R) /\ (((T? (T?.left t) /\ T?.col (T?.left t) = R))
                            \/ ((T? (T?.right t) /\ T?.col (T?.right t) = R)))

// Okasaki: bottom up
type lr_c_inv (#k:eqtype) (#v:Type) (t:rbtree k v) =
  T? t /\ c_inv (T?.left t) /\ c_inv (T?.right t)

// predicate satisfied by a tree before call to balance
// "c ~ >="" i.e. c x a_max
type pre_balance (#k:eqtype) (#v:Type) (c: cmp k)
  (col: color) (lt: rbtree k v) (ky:k) (rt: rbtree k v) =
    // lt/rt satisfy k_inv
    // ky is a candidate root
    (
        k_inv c lt /\ k_inv c rt /\
        (E? lt \/ (T? lt /\ (c ky (max_elt lt)) /\ (not ( ky = (max_elt lt) ))))
        /\
        (E? rt \/ (T? rt /\ (c (min_elt rt) ky) /\ (not ( ky = (min_elt rt) ))))
    )
    /\
    // lt and rt satisfy h_inv, and thier black heights is same
    //
    (
        h_inv lt /\ h_inv rt /\
        Some?.v (black_height lt) = Some?.v (black_height rt)
    )
    /\
    // either lt or rt satisfy c_inv (in which case c can be R or B)
    // or... c has to be B.
    (
        (col = B /\ not_c_inv lt /\ lr_c_inv lt /\ c_inv rt) \/
        (col = B /\ not_c_inv rt /\ lr_c_inv rt /\ c_inv lt) \/
        (c_inv lt /\ c_inv rt)
    )

// predicate satisfied by a tree after call to balance
type post_balance (#k:eqtype) (#v:Type) (c: cmp k)
  (col: color) (lt: rbtree k v) (ky:k) (rt: rbtree k v) (r:rbtree k v) =
  Some? (black_height lt)
  /\
  (T? r)
  /\
  (
    k_inv c r /\
    ((E? lt /\ min_elt r = ky) \/ (T? lt /\ min_elt r = min_elt lt)) /\
    ((E? rt /\ max_elt r = ky) \/ (T? rt /\ max_elt r = max_elt rt))
  )
  /\
  // returned tree satisfies h_inv
  // black height is same or +=1
  (
      (h_inv r)
    // TODO how to prove that
    //  /\
    //  ((col = B /\ Some?.v (black_height r) = Some?.v (black_height lt) + 1) \/
    //   (col = B /\ Some?.v (black_height r) = Some?.v (black_height lt)))
  )
  /\
  // r satisfies c_inv OR col = R
  (
      (c_inv r) \/
      (T?.col r = R /\ col = R /\ not_c_inv r /\ lr_c_inv r)
  )
  /\
  // resulting tree contains all elements from lt ky and rt, and nothing else
  (forall kk. in_tree r kk <==> (in_tree lt kk \/ kk = ky \/ in_tree rt kk))


val balance: (#k:eqtype) -> (#v:Type) -> (c: cmp k)
  -> (col: color) -> (lt: rbtree k v) -> (ky:k) -> (vv:v) -> (rt: rbtree k v)
  -> Pure (rbtree k v)
     (requires (pre_balance c col lt ky rt))
     (ensures (fun r -> post_balance c col lt ky rt r))
#reset-options "--z3rlimit 40"
let balance (#k:eqtype) (#v:Type) cm col lt ky vv rt =
  match (col, lt, ky, rt) with
    | (B, (T R (T R a x v1 b) y v2 c), z, d)
    | (B, (T R a x v1 (T R b y v2 c)), z, d)
    // here we split in two to insert vv at the right place
        -> T R (T B a x v1 b) y v2 (T B c z vv d)
    | (B, a, x, (T R (T R b y v2 c) z v3 d))
    | (B, a, x, (T R b y v2 (T R c z v3 d)))
        -> T R (T B a x vv b) y v2 (T B c z v3 d)
    | _ -> T col lt ky vv rt
#reset-options "--z3rlimit 20"

val ins: (#k:eqtype) -> (#v:Type) -> (c: cmp k)
 -> (t:rbtree k v) -> (kk:k) -> (vv:v) ->
 Pure (rbtree k v)
 (requires (c_inv t /\ h_inv t /\ k_inv c t))
 (ensures (fun r ->
    (T? r) /\
    (
       k_inv c r /\
       (min_elt r = kk \/ (T? t /\ min_elt r = min_elt t)) /\
       (max_elt r = kk \/ (T? t /\ max_elt r = max_elt t))
    ) /\
    // new node is introduced at color R/ no node is recolored
    (h_inv r /\ black_height r = black_height t) /\
    // balance post conditions
    (
        (c_inv r) \/
        (T? t /\ T?.col r = R /\ T?.col t = R /\ not_c_inv r /\ lr_c_inv r)
    )
    /\
    // resulting tree contains all elements from lt ky and rt, and nothing else
    (forall kkk. (in_tree t kkk ==> in_tree r kkk) /\
                (in_tree r kkk ==> (in_tree t kkk \/ kkk = kk)))
  ))
let rec ins (#k:eqtype) (#v:Type) c t x vv =
  match t with
    | E -> T R E x vv E
    | T col a y v2 b ->
      if ((c y x) && (not (x = y))) then
          let lt = ins c a x vv in
          balance c col lt y v2 b
      else if x = y then
          T col a y vv b
      else
          let rt = ins c b x vv in
          balance c col a y v2 rt

type balanced_rbtree (#k:eqtype) (#v:Type) (c: cmp k) (t: rbtree k v) =
  r_inv t /\ h_inv t /\ c_inv t /\ k_inv c t

// make black blackens the root of a tree
val make_black: (#k:eqtype) -> (#v:Type) -> (c: cmp k)
   -> (t: rbtree k v) -> Pure (rbtree k v)
                          (requires (T? t /\ c_inv t /\ h_inv t /\ k_inv c t))
                          (ensures (fun r ->
        (balanced_rbtree c r) /\ (forall kk. (in_tree t kk <==> in_tree r kk))))
let make_black (#k:eqtype) (#v:Type) (c: cmp k) (T _ a x vv b) = T B a x vv b

val insert: (#k:eqtype) -> (#v:Type) -> (c: cmp k)
   -> (t: rbtree k v) -> (x:k) -> (y:v) -> Pure (rbtree k v)
                                  (requires (balanced_rbtree c t))
                                  (ensures (fun r ->
                                    (balanced_rbtree c r) /\
                                    (forall kk.
                                      (in_tree t kk ==> in_tree r kk) /\
                                      (in_tree r kk ==> (in_tree t kk \/ kk = x))
                                      )))
let insert (#k:eqtype) (#v:Type) (c: cmp k) t x y =
  let r = ins c t x y in
  let r2 = make_black c r in
  r2

val get: (#k:eqtype) -> (#v:Type) -> (c: cmp k)
    -> (t: rbtree k v) -> (x:k) -> Tot (option v)
let rec get (#k:eqtype) (#v:Type) (c: cmp k) t x = match t with
  | T _ a y v b ->
    if (y = x) then Some v
    else if (c x y) then get c b x
    else get c a x
  | E -> None

val fold: (#a:Type) -> (#k:eqtype) -> (#v:Type) ->
               (f: a -> k -> v -> Tot a) -> (acc: a) -> (t: rbtree k v)
               -> Tot a (decreases t)
let rec fold (#a) (#k) (#v) f acc t = match t with
      | E -> acc
      | T _ l ky va r ->
        let (acc1:a) = fold f acc l in
        let (acc2:a) = f acc1 ky va in
        let (acc3:a) = fold f acc2 r in
        acc3

(* why ???
noeq type redblacktree (k: eqtype) v (c: cmp k) =
  | Mk: (cm:c) -> (tr: (rbtree k v){balanced_rbtree c tr}) -> redblacktree k v c

val proj: (#k:eqtype) -> (#v:Type) -> (#c: cmp k) ->
  redblacktree k v c -> Pure (rbtree k v)
  (requires True) (ensures (fun r -> balanced_rbtree c r))
let proj tr = Mk?.tr tr
*)

// still todo: get operation + check k->v mapping
// in practice this means: get operation

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
type u32 = FStar.UInt32.t
type u16 = FStar.UInt16.t
type u8 = FStar.UInt8.t

//////////////////////////////////////////////////
// crappy test that all compiles/let itself be used well
val compare: #a:eqtype -> f:cmp a -> a -> a -> Tot bool
let compare (#a:eqtype) f k1 k2 = f k1 k2
val compare2: (#a:eqtype) -> (#b:eqtype) -> f1:cmp a -> f2:cmp b ->
   a -> b -> a -> b -> Tot bool
let compare2 (#a:eqtype) (#b:eqtype) f1 f2 x1 x2 y1 y2 =
   compare (toPair f1 f2) (x1,x2) (y1,y2)

val test_map_01: unit -> Tot bool
let test_map_01 () =
  let (dict : rbtree u32 u16) = E in
  let c = fun (x:u32) (y:u32) -> (U32.v x) >= (U32.v y) in
  let dict = insert c dict (12ul) (34us) in
  let dict = insert c dict (35ul) (45us) in
  let dict = insert c dict (45ul) (55us) in
  let r12 = get c dict (12ul) in
  let r35 = get c dict (35ul) in
  let r45 = get c dict (45ul) in
  let r56 = get c dict (56ul) in
  (r12 = Some (34us)) && (r35 = Some (45us)
    && (r45 = Some (55us)) && (r56 = None))

// ??
//val mkKey: #a1:eqtype -> #a2:eqtype
//   -> f: cmp (a1*a2)
//   -> x1:a1
//   -> x2:a2
//   -> key (a1*a2) f
//let mkKey (#a1:eqtype) (#a2:eqtype) f x1 x2 =
//    (x1, x2)
