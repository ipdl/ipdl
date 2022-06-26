module MTProof
open FStar.FunctionalExtensionality
open MT
open FStar.Squash

let csetU0 #n (c : cset n) : Lemma (csetU c cset0 == c) [SMTPat (csetU c cset0)] = 
  ctx_ext c (csetU c cset0)

let cset0U #n (c : cset n) : Lemma (csetU cset0 c == c) [SMTPat (csetU cset0 c)] = 
  ctx_ext c (csetU cset0 c)


let unlift_pos #n #t (a : pos n) (x : t) (g : ctx n t) (y : fin (n + 1)) : Pure (option (fin n)) (requires True) (ensures fun z -> 
Some? z ==> g (Some?.v z) == insert_ctx a x g y) = 
   if y < a then Some y else 
   if y = a then None else
   Some (y - 1)
   
let lift_t #n (i : pos n) t (g : ctx n Type0) (p : ipdl g) (o : cset n) : Lemma (requires squash (ipdl_t g p o)) (ensures squash (ipdl_t (insert_ctx i t g) (lift_ipdl i t g p) (on _ (fun x -> 
                        match unlift_pos i t g x with | None -> false | Some y -> o y)))) = admit()

let zero_t_inv #n (g : ctx n Type0) o : Lemma (requires squash (ipdl_t g Zero o)) (ensures o == cset0) [SMTPat (ipdl_t g Zero o)]  =
 let aux (h : squash (ipdl_t g Zero o)) : Lemma (o == cset0) =
   let _ : squash (o == cset0) = bind_squash h (fun pf -> ()) in () in Classical.impl_intro aux

let zero_t #n (g : ctx n Type0) : Lemma (squash (ipdl_t g Zero cset0)) [SMTPat (ipdl_t g Zero cset0)] = 
  let h = Zero_t #n #g in return_squash h

let out_t_inv #n (g : ctx n Type0) (x : fin n) (r : rxn g (g x)) o :
  Lemma (requires squash (ipdl_t g (Out x r) o)) (ensures o == cset1 x) [SMTPat (ipdl_t g (Out x r) o)] =
  let aux (h : squash (ipdl_t g (Out x r) o)) : Lemma (o == cset1 x) = 
    let _ : squash (o == cset1 x) = bind_squash h (fun pf -> ()) in () in Classical.impl_intro aux

let out_t #n (g : ctx n Type0) (x : fin n) (r : rxn g (g x)) : Lemma (squash (ipdl_t g (Out x r) (cset1 x))) [SMTPat (ipdl_t g (Out x r))] = 
  let h = Out_t x r in return_squash h

let par_t_inv #n (g : ctx n Type0) (p q : ipdl g) (o : cset n) : Lemma (requires squash (ipdl_t g (Par p q) o)) (ensures exists (o1 o2 : cset n). squash (ipdl_t g p o1) /\ squash (ipdl_t g q o2) /\ disjoint o1 o2 /\ o == csetU o1 o2) [SMTPat (ipdl_t g (Par p q) o)] = 
  let aux (h : squash (ipdl_t g (Par p q) o)) : Lemma (exists (o1 o2 : cset n). squash (ipdl_t g p o1) /\ squash (ipdl_t g q o2) /\ disjoint o1 o2 /\ o == csetU o1 o2) = 
    let _ : squash ((exists (o1 o2 : cset n). squash (ipdl_t g p o1) /\ squash (ipdl_t g q o2) /\ disjoint o1 o2 /\ o == csetU o1 o2)) = 
      bind_squash h (fun pf -> match pf with | Par_t _ _ _ _ _ _ _ -> ()) in () in
  Classical.impl_intro aux
    

let par_t_construct #n (g : ctx n Type0) (p q : ipdl g) (o1 o2 : cset n) : Lemma (requires squash (ipdl_t g p o1) /\ squash (ipdl_t g q o2) /\ disjoint o1 o2) (ensures squash (ipdl_t g (Par p q) (csetU o1 o2))) [SMTPat (ipdl_t g p o1); SMTPat (ipdl_t g q o2); SMTPat (disjoint o1 o2)] = 
  let h : ipdl_t g (Par p q) (csetU o1 o2) = Par_t p q o1 o2 () () () in return_squash h

let par_t_infer #n (g : ctx n Type0) (p q : ipdl g) (o1 o2 : cset n) : Lemma (requires squash (ipdl_t g p o1) /\ squash (ipdl_t g q o2) /\ disjoint o1 o2) (ensures squash (ipdl_t g (Par p q) (csetU o1 o2))) [SMTPat (ipdl_t g (Par p q) (csetU o1 o2))] = ()


let deconstruct_par (a : Type)  #n (g : ctx n Type0) (p q : ipdl g) (o : cset n) 
  (f : (o1 : cset n) -> (o2 : cset n) -> 
    Lemma (requires squash (ipdl_t g p o1) /\ squash (ipdl_t g q o2) /\ disjoint o1 o2 /\ o == csetU o1 o2)
          (ensures a)) : Lemma (requires squash (ipdl_t g (Par p q) o)) (ensures a) = 
    assert (exists (o1 o2 : cset n). squash (ipdl_t g p o1) /\ squash (ipdl_t g q o2) /\ disjoint o1 o2 /\ o == csetU o1 o2); 
    admit()


let new_t_inv #n (g : ctx n Type0) t (p : ipdl (cons_ctx t g)) (o : cset n) : Lemma (requires squash (ipdl_t g (New t p) o)) (ensures
  (exists (o' : cset (n + 1)). 
    squash (ipdl_t (cons_ctx t g) p o') /\
    o == on _ (fun (x : fin n) -> o' (x + 1)))) [SMTPat (ipdl_t g (New t p) o)] = 
  let aux (h : squash (ipdl_t g (New t p) o)) : Lemma (
  (exists (o' : cset (n + 1)). 
    squash (ipdl_t (cons_ctx t g) p o') /\
    o == on _ (fun (x : fin n) -> o' (x + 1)))) = 
    let _ : squash (
  (exists (o' : cset (n + 1)). 
    squash (ipdl_t (cons_ctx t g) p o') /\
    o == on _ (fun (x : fin n) -> o' (x + 1)))) =
    bind_squash h (fun pf -> match pf with | New_t _ _ _ _ -> ()) in () in Classical.impl_intro aux

let new_t #n (g : ctx n Type0) t (p : ipdl (cons_ctx t g)) (o : cset (n + 1)) : Lemma (requires squash (ipdl_t (cons_ctx t g) p o)) (ensures squash (ipdl_t g (New t p) (on _ (fun (x : fin n) -> o (x + 1))))) [SMTPat (ipdl_t (cons_ctx t g) p o)] = 
  let h : ipdl_t g (New t p) (on _ (fun (x : fin n) -> o (x + 1))) =
    New_t t p o () in return_squash h

let t () : Lemma (squash (ipdl_t (zero_ctx Type0) (Par Zero Zero) cset0)) = 
  csetU0 #0 cset0;
   ()


let ipdl_eq #n (#g : ctx n Type0) (p q : ipdl g) (o : cset n) (h : ipdl_eq p q) : Lemma (squash (ipdl_t g p o) <==> squash (ipdl_t g q o)) =  
  match h with
  | ENewComp t p q -> 
     let lem1 (h : squash (ipdl_t g (Par (New t p) q) o)) : squash (ipdl_t g (New t (Par p (lift_ipdl 0 t g q))) o) = 
       deconstruct_par (squash (ipdl_t g (New t (Par p (lift_ipdl 0 t g q))) o)) g (New t p) q o (fun o1 o2 -> 
          assume (squash (ipdl_t (cons_ctx t g) p (on _ (fun (x : fin (n + 1)) -> if x = 0 then true else o1 (x - 1)))));
          assume (squash (ipdl_t (cons_ctx t g) (lift_ipdl 0 t g q) (on _ (fun (x : fin (n + 1)) -> if x = 0 then false else o1 (x - 1)))));
       ())
     in
     let lem2 (h : ipdl_t g (New t (Par p (lift_ipdl 0 t g q))) o) : squash (ipdl_t g (Par (New t p) q) o) = admit() in
     admit()

