module MT
open FStar.FunctionalExtensionality

type fin (n : nat) =
  (x:nat{x < n})

type pos (n : nat) = 
  (x:nat{x <= n})

type ctx (n : nat) (t : Type u#a) = (fin n ^-> t)

let ctx_ext #n #t (g h : ctx n t) : Lemma (g == h <==> (forall i. g i == h i)) = 
  extensionality _ _ g h

let insert_ctx (#n : nat) (#t : Type u#a) (a : pos n) (x : t) (g : ctx n t) : ctx (n + 1) t = 
  on (fin (n + 1)) (fun i -> 
    if i = a then x else 
    if i < a then g i else
    g (i - 1))

let cons_ctx (#n : nat) (#t : Type u#a) (x : t) (g : ctx n t) : ctx (n + 1) t = 
  insert_ctx 0 x g

let zero_ctx (t : Type u#a) : ctx 0 t = 
  let f (x : fin 0) : t = () in
  on _ f

let lift_pos #n #t (a : pos n) (x : t) (g : ctx n t) (y : fin n) : Pure (fin (n + 1)) (requires True) (ensures fun z -> insert_ctx a x g z == g y) = 
   if y < a then y else y + 1

noeq
type rxn #n (g : ctx n Type0) : Type -> Type =
  | Ret : (#a : Type) -> a -> rxn g a
  | Read : (x:fin n) -> rxn g (g x)
  | Bind : (#a : Type) -> (#b : Type) -> 
    rxn g a -> (a -> rxn g b) -> rxn g b

noeq
type ipdl (#n : nat) (g : ctx n Type0) : Type = 
   | Zero : ipdl g
   | Out :  (x:fin n) -> rxn g (g x) -> ipdl g
   | Par : ipdl g -> ipdl g -> ipdl g
   | New : (t : Type0) -> ipdl (cons_ctx t g) -> ipdl g 

let disjoint #a (f g : a -> bool) = 
  forall x. ~ (f x && g x)

type cset n = (fin n ^-> bool)
let cset0 #n : cset n = on _ (fun _ -> false)
let cset1 #n (x : fin n) : cset n = on _ (fun i -> i = x)
let csetU #n (f g : cset n) : cset n = 
  on _ (fun i -> f i || g i)


noeq type ipdl_t #n (g : ctx n Type0) : ipdl g -> cset n -> Type =
  | Zero_t : ipdl_t g Zero cset0
  | Out_t : (x : fin n) -> (r : rxn g (g x)) -> ipdl_t g (Out x r) (cset1 x)
  | Par_t : (p : ipdl g) -> (q : ipdl g) -> (o1 : cset n) -> (o2 : cset n) ->
     (h : squash (disjoint o1 o2)) -> squash (ipdl_t g p o1) -> squash (ipdl_t g q o2) -> ipdl_t g (Par p q) (csetU o1 o2)
  | New_t : (t : Type0) -> (p : ipdl (cons_ctx t g)) -> (o : cset (n + 1)) ->
    squash (ipdl_t (cons_ctx t g) p o) -> 
    ipdl_t g (New t p) (on _ (fun (x : fin n) -> o (x + 1)))

let rec lift_rxn #n #a (i : pos n) t (g : ctx n Type0) (r : rxn g a) : rxn (insert_ctx i t g) a = 
  match r with
  | Ret x -> Ret x
  | Read x -> Read (lift_pos i t g x)
  | Bind c f -> Bind (lift_rxn i t g c) (fun x -> lift_rxn i t g (f x))

let cons_insert_swap #n #t (i : fin n) (x y : t) (g : ctx n t) : Lemma (cons_ctx x (insert_ctx i y g) == insert_ctx (i + 1) y (cons_ctx x g)) [SMTPat (cons_ctx x (insert_ctx i y g))] = 
  let lem (j : fin (n + 2)) : Lemma (cons_ctx x (insert_ctx i y g) j == insert_ctx (i + 1) y (cons_ctx x g) j) = () in
  Classical.forall_intro lem;
  ctx_ext (cons_ctx x (insert_ctx i y g)) (insert_ctx (i + 1) y (cons_ctx x g) )

let rec lift_ipdl #n (i : pos n) t (g : ctx n Type0) (p : ipdl g) : Tot (ipdl (insert_ctx i t g)) (decreases p) =
  match p with
  | Zero -> Zero
  | Out x r -> Out (lift_pos i t g x) (lift_rxn i t g r)
  | Par p' q -> Par (lift_ipdl i t g p') (lift_ipdl i t g q)
  | New t' q -> New t' (lift_ipdl (i + 1) t (cons_ctx t' g) q)

let bump_ipdl #n t #g (p : ipdl g) : ipdl (cons_ctx t g) = 
  lift_ipdl #n 0 t g p

noeq type ipdl_eq #n (#g : ctx n Type0) : ipdl g -> ipdl g -> Type = 
| ENewComp : (t : Type0) -> (p : ipdl (cons_ctx t g))  -> (q : ipdl g) ->
  ipdl_eq (Par (New t p) q) (New t (Par p (lift_ipdl 0 t g q)))
  





