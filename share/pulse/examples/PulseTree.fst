module PulseTree
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Stick.Util
module FA = Pulse.Lib.Forall.Util
open FStar.List.Tot

module T = Trees

noeq
type node (t:Type0) = {
    data : t;
    left : tree_t t;
    right : tree_t t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and tree_t (t:Type0) = option (node_ptr t)

// Another version
(*#set-options "--fuel 1 --ifuel 1 --z3rlimit 15"

#push-options "--__no_positivity"
noeq type node1 (a: Type0) = {
  data: a;
  left: option (ref (node1 a));
  right: option (ref (node1 a));
}

(** A tree is a ref to a node, themselves referencing other nodes *)
let t (a: Type0) = option (ref (node1 a))*)

// How can we say an optional pointer pointing to some memory is functionally a tree?
// for that we need to match the different cases of the functional tree.
//if the functional tree is a leaf, the the optional pointer points to None
//if the functional tree is a node with a value and left and right tree pointers,
//then there exists a data, a concrete left tree and a concrete right tree and 
//the optional pointer points to some concrete memory, where the data is the data
//of the functional tree, left and right are the left and right subtrees of the fiunctional tree
//respectively. Additionally, the left and right concrete subtrees are is_tree itself with respect to left
//and right of the functional tree respectively.
let rec is_tree #t (ct:tree_t t) (ft:T.tree t)
: Tot vprop (decreases ft)
= match ft with
  | T.Leaf -> pure (ct == None)
  | T.Node data left' right' ->
    exists* (p:node_ptr t) (lct:tree_t t) (rct:tree_t t).
      pure (ct == Some p) **
      pts_to p { data = data ; left = lct ; right = rct} **
      is_tree lct left' **
      is_tree rct right'

//boilerplate$
//elim functions are used to prove that if the tree type is is_tree with respect to a functional tree
//then we can prove the exisitense of its concrete version
//Whereas, intro is to prove the existence of the functional version from the concrete version.
```pulse
ghost
fn elim_is_tree_leaf (#t:Type0) (x:tree_t t)
requires is_tree x T.Leaf //elim is like from the LHS, we are getting the RHS
                                         //requires have the precondition that 'l is empty
                                         // And 'l comes from is_list x 'l
ensures pure (x == None)                 // Just look at the RHS of l == [], that is the postcondition
{
   //show_proof_state;
  //  rewrite each 'l as T.Leaf #t; //each instance of such 'l is Nil; We are setting the context for empty lists
   //show_proof_state;
   unfold (is_tree x T.Leaf) // unfold exposes the definition of the function inside it. 
                         // is_list x [], RHS side is pure (x == None)
  
}
```

```pulse
ghost
fn intro_is_tree_leaf (#t:Type0) (x:tree_t t) // opposite to elim. elim is breakig, intro is assembling.
requires pure (x == None) // From RHS
ensures is_tree x T.Leaf // To LHS
{
  fold (is_tree x T.Leaf); //just take the LHS and fold it to create the LHS.
}
```

```pulse
ghost
fn elim_is_tree_node (#t:Type0) (ct:tree_t t) (data:t) (ltree:T.tree t) (rtree:T.tree t)
requires is_tree ct (T.Node data ltree rtree)
ensures (
  exists* (p:node_ptr t) (lct:tree_t t) (rct:tree_t t).
    pure (ct == Some p) **
    pts_to p { data; left = lct;right = rct } **
    is_tree lct ltree **
    is_tree rct rtree
)
{
  unfold is_tree
}
```

```pulse
ghost
fn intro_is_tree_node (#t:Type0) (ct:tree_t t) (v:node_ptr t) (#node:node t) (#ltree:T.tree t) (#rtree:T.tree t)
requires
  pts_to v node **
  is_tree node.left ltree **
  is_tree node.right rtree **
  pure (ct == Some v)
ensures
  is_tree ct (T.Node node.data ltree rtree)
{
  fold (is_tree ct (T.Node node.data ltree rtree))
}
```

//boilerplate$
//is_tree_cases$
let is_tree_cases #t (x:tree_t t) (ft: T.tree t)
: vprop 
= match x with
  | None -> pure (ft == T.Leaf)
  | Some v -> 
    exists* (n:node t) (ltree:T.tree t) (rtree:T.tree t).
      pts_to v n **
      pure (ft == T.Node n.data ltree rtree) **
      is_tree n.left ltree **
      is_tree n.right rtree
//is_tree_cases$

```pulse //cases_of_is_tree$
ghost
fn cases_of_is_tree #t (x:tree_t t) (ft:T.tree t)
requires is_tree x ft
ensures  is_tree_cases x ft
{
  match ft {
    T.Leaf -> {
      unfold (is_tree x T.Leaf);
      fold (is_tree_cases None ft);
    }
    T.Node data ltree rtree -> {
      unfold (is_tree x (T.Node data ltree rtree));
      with p _lct _rct. _;
      fold (is_tree_cases (Some p) ft)
    }
  }
}

```

```pulse //is_list_case_none$
ghost
fn is_tree_case_none (#t:Type) (x:tree_t t) (#l:T.tree t)
requires is_tree x l ** pure (x == None)
ensures  is_tree x l ** pure (l == T.Leaf)
{
  cases_of_is_tree None l;
  unfold is_tree_cases;
  intro_is_tree_leaf x;
}

```

```pulse //is_list_case_some$
ghost
fn is_tree_case_some (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
requires is_tree x ft ** pure (x == Some v)
ensures  
   exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    pts_to v node **
    is_tree node.left ltree **
    is_tree node.right rtree **
    pure (ft == T.Node node.data ltree rtree)
  
{
  cases_of_is_tree (Some v) ft;
  unfold is_tree_cases;
}
```
///////////////////////////////////////////////////////////////////////////////

```pulse //height$
fn rec height (#t:Type0) (x:tree_t t)
requires is_tree x 'l
returns n:nat
ensures is_tree x 'l ** pure (n == T.height 'l)
{
   match x {
    None -> {
       is_tree_case_none x;
       0
    }
    Some vl -> {
      is_tree_case_some x vl;
      let node = !vl;
      let l_height = height node.left;
      let r_height = height node.right;
      intro_is_tree_node x vl;
      if (l_height > r_height) {
        (l_height + 1)
      } else {
        (r_height + 1)
      }
    }
  }
}
```

```pulse
fn add_k_height (#t:Type0) (x:tree_t t) (k:nat)
requires is_tree x 'l
returns n:nat
ensures is_tree x 'l ** pure (n == k + T.height 'l)
{
  let h = height x;
  (h + k)
}
```

```pulse
fn is_empty (#t:Type) (x:tree_t t) 
  requires is_tree x 'l
  returns b:bool
  ensures is_tree x 'l ** pure (b <==> ('l == T.Leaf))
{
  match x {
    None -> {
      is_tree_case_none x;
      true
    }
    Some vl -> {
      is_tree_case_some x vl;
      intro_is_tree_node x vl;
      false
    }
  }
}
```
let null_tree_t (t:Type0) : tree_t t = None


```pulse
fn create (t:Type0)
  requires emp
  returns x:tree_t t
  ensures is_tree x T.Leaf
{
  let tree = null_tree_t t;
  intro_is_tree_leaf tree;
  tree
}
```

// ```pulse
// fn node_cons (#t:Type0) (data:t) (ltree:tree_t t) (rtree:tree_t t) 
//   requires is_tree ltree 'l  **
//            is_tree rtree 'r  //functional equivalent of x is 'l; x is the tail of the constructed tree.
//   returns y:tree_t t
//   ensures is_tree y (T.Node v 'l 'r)
// {
//   let y = alloc { data=v; left =ltree; right = rtree };
//   rewrite each ltree as ({data = v; left = ltree; right = rtree}).left in (is_tree ltree 'l);
//   rewrite each rtree as ({data = v; left = ltree; right = rtree}).right in (is_tree rtree 'r);
//   intro_is_tree_cons (Some y) y;
//   Some y
// }
// ```

// val get_left (#a: Type0) (n: node a) : tree_t a
// val get_right (#a: Type0) (n: node a) : tree_t a
// val get_data (#a: Type0) (n: node a) : a

// let get_left #a n = n.left
// let get_right #a n = n.right
// let get_data #a n = n.data


// val mk_node (#a: Type0) (data: a) (left right: tree_t a)
//     : Pure (node a)
//       (requires True)
//       (ensures (fun n -> get_left n == left /\ get_right n == right /\ get_data n == data))

// let mk_node #a data left right = {
//   data;
//   left;
//   right
// }



// /// Appends value [v] at the leftmost leaf of the tree that [ptr] points to.
// ```pulse
// fn rec append_left_none (#t:Type0) (x:tree_t t) (v:t) 
// requires is_tree x 'l ** pure (None? x)
// returns y:tree_t t
// ensures is_tree x 'l  ** is_tree y (T.Node v T.Leaf T.Leaf)
// {
//   let left = create t;
//   let right = create t;
//   let y = node_cons v left right;
//       //intro_is_tree_nil x;
//       //fold (is_tree y (T.append_left 'l v));
//       //rewrite each (None #(ref (node t))) as x;
//       //y
//       //elim_is_tree_nil x;
//   //intro_is_tree_nil x;
//   //intro_is_tree_cons y;
//   y // How can we remove is_tree x 'l from the context?
// }
// ```


// ```pulse
// fn rec append_left (#t:Type0) (x:tree_t t) (v:t) 
// requires is_tree x 'l
// returns y:tree_t t
// ensures is_tree y  (T.append_left 'l v)
// {
//    match x {
//     None -> {
//       //current context: is_tree x (reveal 'l)
//       (*cond: requires is_tree x l ** pure (x == None)
//               ensures  is_tree x l ** pure (l == T.Leaf)*)
//       is_tree_case_none x;
//       //current context: is_tree x (reveal 'l) ** pure (reveal 'l == T.Leaf)
//       (*cond: requires is_tree x 'l ** pure ('l == T.Leaf)
//               ensures pure (x == None)*)
//       elim_is_tree_nil x;
//       //current cotext: pure (x == None)
      
//       let left = create t;
//       let right = create t;
//       //Current context: is_tree right T.Leaf ** is_tree left T.Leaf
    
//       let y = node_cons v left right;
//       //Current context:
//       //is_tree y (T.Node v (reveal (hide T.Leaf)) (reveal (hide T.Leaf))) **
//       //pure (Some? y)
    
//       let np = Some?.v y;
      
//     //Current context:
//     //pure (np == y.v) **
//     //is_tree y (T.Node v (reveal (hide T.Leaf)) (reveal (hide T.Leaf)))
//      (*cond: requires is_tree x ft ** pure (x == Some v)
//              ensures  
//                 exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
//                 pts_to v node **
//                 is_tree node.left ltree **
//                 is_tree node.right rtree **
//                 pure (ft == T.Node node.data ltree rtree)*)
//      is_tree_case_some y np;

//      (*Current context:
//                (exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
//                pts_to np node ** 
//                is_tree node.left ltree ** 
//                is_tree node.right rtree **
//                pure (T.Node v (reveal (hide T.Leaf)) (reveal (hide T.Leaf)) ==
//                T.Node node.data ltree rtree))*)
    
//       intro_is_tree_cons y np;

//       (*Current context:
//         is_tree y (T.Node (reveal node).data (reveal ltree) (reveal rtree)*)
//       (*requires
//         pts_to v node **
//         is_tree node.left ltree **
//         is_tree node.right rtree **
//         pure (ct == Some v)
//       ensures
//         is_tree ct (T.Node node.data ltree rtree)*)
//       y 
//     }
//     Some vl -> {
//       //current context: is_tree x (reveal 'l)
//       let np = Some?.v x;
//       (*Current context:
//         pure (np == x.v) ** is_tree x (reveal 'l)*)
//       is_tree_case_some x np;
//       (*Current context:
//         (exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
//          pts_to np node ** is_tree node.left ltree ** is_tree node.right rtree **
//          pure (reveal 'l == T.Node node.data ltree rtree))*)
//       with _node _ltree _rtree._;
//       (*Current context:
//         pts_to np (reveal node) **
//         is_tree (reveal node).left (reveal ltree) **
//         is_tree (reveal node).right (reveal rtree) **
//         pure (reveal 'l == T.Node (reveal node).data (reveal ltree) (reveal rtree))*)
//       let node = !np;
//       (*Current context:
//          pts_to np (reveal node) **
//          pure (reveal node == node) **
//         is_tree (reveal node).left (reveal ltree) **
//         is_tree (reveal node).right (reveal rtree)*)
      
//       rewrite each _node as node;

//       (*Current context:
//         is_tree node.right (reveal rtree) **
//         is_tree node.left (reveal ltree) ** pts_to np node*)

      
//       let left_new = append_left node.left v;
      
//       (*Current context:
//         is_tree left_new (T.append_left (reveal ltree) v) **
//         pts_to np node ** is_tree node.right (reveal rtree)*)
//       np := {node with left = left_new};
      
       
//       (*Current context:
//         pts_to np (Mknode node.data left_new node.right) **
//         is_tree node.right (reveal rtree) **
//         is_tree left_new (T.append_left (reveal ltree) v)*)
      
//        rewrite each left_new as ({ node with left = left_new }).left in (is_tree left_new ((T.append_left (reveal _ltree) v)));
      

//       (*Current context:
//          is_tree (Mknode node.data left_new node.right).left
//                 (T.append_left (reveal ltree) v) **
//          pts_to np (Mknode node.data left_new node.right) **
//          is_tree node.right (reveal rtree)*)

//        rewrite each node.right as ({ node with left = left_new }).right in (is_tree node.right _rtree);
       
//       (*Current context:
//          is_tree (Mknode node.data left_new node.right).right (reveal rtree) **
//          is_tree (Mknode node.data left_new node.right).left
//                   (T.append_left (reveal ltree) v) **
//         pts_to np (Mknode node.data left_new node.right)*)
       
//        intro_is_tree_cons x np;

//        (*Current context:
//         is_tree x
//              (T.Node (Mknode node.data left_new node.right).data
//                   (T.append_left (reveal ltree) v)
//                   (reveal rtree))*)
//        //show_proof_state;

//       x
//     }
//   }
// } 
// ```


// ```pulse
// fn rec append_right (#t:Type0) (x:tree_t t) (v:t) 
// requires is_tree x 'l
// returns y:tree_t t
// ensures is_tree y  (T.append_right 'l v)
// {
//    match x {
//     None -> {
      
//       is_tree_case_none x;
      
//       elim_is_tree_nil x;
     
//       let left = create t;
//       let right = create t;
      
    
//       let y = node_cons v left right;
      
//       let np = Some?.v y;
      
//       is_tree_case_some y np;

//       intro_is_tree_cons y np;
      
//       y 
//     }
//     Some vl -> {
      
//       let np = Some?.v x;
      
//       is_tree_case_some x np;
      
//       with _node _ltree _rtree._;
      
//       let node = !np;
      
//       rewrite each _node as node;

//       let right_new = append_right node.right v;
      
//       np := {node with right = right_new};
      
//       rewrite each right_new as ({ node with right = right_new }).right in (is_tree right_new ((T.append_right (reveal _rtree) v)));
      
//       rewrite each node.left as ({node with right = right_new}).left in (is_tree node.left _ltree);
      
//       intro_is_tree_cons x np;
      
//       x
//     }
//   }
// } 
// ```

// ```pulse
// fn node_data (#t:Type) (x:tree_t t) 
//     requires is_tree x 'l  ** (pure (Some? x))
//     returns v:t
//     ensures is_tree x 'l 
// {
//   let np = Some?.v x;
      
//   is_tree_case_some x np;
      
//   with _node _ltree _rtree._;
      
//   let node = !np;
      
//   rewrite each _node as node;

//   let v = node.data;
  
//   intro_is_tree_cons x np;
//   v
// }
// ```

// ```pulse
// fn rec is_mem (#t:eqtype) (x:tree_t t) (v: t)
//     requires is_tree x 'l
//     returns b:bool
//     ensures is_tree x 'l ** pure (b <==> (T.mem 'l v))
// {
//    match x {
//         None -> {
//             is_tree_case_none x;
//             false
//         }
//         Some vl -> {
//             //let dat = node_data x;
//             is_tree_case_some x vl;
//             with _node _ltree _rtree. _;
//             let n = !vl;
//             rewrite each _node as n;

//             let dat = n.data;
            
//             if (dat = v) 
//             {
//               intro_is_tree_cons x vl;
//               true
//             }
//             else{
//               let b1 = is_mem n.left v;
//               let b2 = is_mem n.right v;

//               let b3 = b1 || b2;
//               intro_is_tree_cons x vl;
//               b3;
              
//             }
//         }
//     }
// }
// ```
// ```pulse //cases_of_is_tree$
// ghost
// fn cases_of_is_tree_reverse #t (x:tree_t t) (ft:T.tree t)
// requires  is_tree_cases x ft

// ensures is_tree x ft
// {
//   admit()
// }
// ```

// ```pulse //is_list_case_some$
// ghost
// fn is_tree_case_some1 (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
// requires 
// exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
//     is_tree x ft **
//     pts_to v node **
//     is_tree node.left ltree **
//     is_tree node.right rtree **
//     pure (ft == T.Node node.data ltree rtree)

// ensures  is_tree x ft ** pure (x == Some v)
   
  
// {
  
//   fold(is_tree_cases (Some v) ft);
//   //rewrite each (Some v) as x;
//   //show_proof_state;
//   cases_of_is_tree_reverse (Some v) ft;
//   //show_proof_state;
//   assert (is_tree x ft);
  
//   //show_proof_state;
  
//   admit()
// }
// ```


// (*cases_of_is_tree x ft;
//   rewrite each x as (Some v);
//   unfold (is_tree_cases (Some v) ft);*)

// ```pulse
// ghost
// fn non_empty_tree (#t:Type0) (x:tree_t t) (ft:T.tree t)
// requires is_tree x ft ** pure (T.Node? ft)
// ensures is_tree x ft ** pure (Some? x)
// {
//     match x {
//       None -> {
//         intro_is_tree_nil x;
//         show_proof_state;
//         admit()
//       }
//       Some vl -> {
//         admit()
//       }
//     }
   
//     (*n intro_is_tree_cons (#t:Type0) (ct:tree_t t) (v:node_ptr t) (#node:node t) (#ltree:T.tree t) (#rtree:T.tree t)
//   requires
//   pts_to v node **
//   is_tree node.left ltree **
//   is_tree node.right rtree **
//   pure (ct == Some v)*)

//     (*elim_is_tree_cons x _ (T.Node?.data 'l) (T.Node?.left 'l) (T.Node?.right 'l);

//     with v lct rct. _;
//     with n left right. assert (pts_to v n ** is_tree lct left ** is_tree rct right);
    
//     (*Current context:
//     pts_to (reveal p) (Mknode (reveal 'l).data (reveal lct) (reveal rct)) **
//     is_tree (reveal lct) (reveal 'l).left **
//     is_tree (reveal rct) (reveal 'l).right*)

    
//     rewrite each (reveal lct) as n.left;
//     show_proof_state;
//     // show_proof_state;

//     (*Current context:
//     is_tree (Mknode (reveal 'l).data (reveal lct) (reveal rct)).left
//       (reveal 'l).left **
//     pts_to (reveal p)
//       (Mknode (reveal 'l).data
//           (Mknode (reveal 'l).data (reveal lct) (reveal rct)).left
//           (reveal rct)) **
//     is_tree (reveal rct) (reveal 'l).right*)
    
//     rewrite each rct as n.right;
//     show_proof_state;
    
//     (*Current context:
//     is_tree (Mknode (reveal 'l).data (reveal lct) (reveal rct)).right
//       (reveal 'l).right **

//     pts_to (reveal p)
//       (Mknode (reveal 'l).data
//           (Mknode (reveal 'l).data
//               (reveal lct)
//               (Mknode (reveal 'l).data (reveal lct) (reveal rct)).right)
//             .left
//           (Mknode (reveal 'l).data (reveal lct) (reveal rct)).right) **

//     is_tree (Mknode (reveal 'l).data
//           (reveal lct)
//           (Mknode (reveal 'l).data (reveal lct) (reveal rct)).right)
//         .left
//       (reveal 'l).left


//     show_proof_state;
    
    
    

   
//     //show_proof_state;
//     //intro_is_tree_cons x v #n #left #right;*)*)
// }

// ```

// (*```pulse //non_empty_list$
// ghost
// fn non_empty_list (#t:Type0) (x:llist t)
// requires is_list x 'l ** pure (Cons? 'l)
// ensures is_list x 'l ** pure (Some? x)
// {
//     elim_is_list_cons x _ (Cons?.hd 'l) (Cons?.tl 'l);
//     with v tail. _;
//     with n tl. assert (pts_to v n ** is_list tail tl);
//     rewrite each tail as n.tail;
//     intro_is_list_cons x v #n #tl;
// }
// ```*)

// (*n intro_is_tree_cons (#t:Type0) (ct:tree_t t) (v:node_ptr t) (#node:node t) (#ltree:T.tree t) (#rtree:T.tree t)
// requires
//   pts_to v node **
//   is_tree node.left ltree **
//   is_tree node.right rtree **
//   pure (ct == Some v)*)

// (*fn elim_is_tree_cons (#t:Type0) (ct:tree_t t) (ft:T.tree t) (data:t) (ltree:T.tree t) (rtree:T.tree t)
// requires is_tree ct ft ** pure (ft == T.Node data ltree rtree)*)



```pulse
fn rec rotate_left (#t:Type0) (x:tree_t t) (#l:T.tree t{ Some? (T.rotate_left l) })
requires is_tree x l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_left l)))
{
  


  admit ()
  // //get the node, node_x from the tree x --- T.Node data_x left_x right_x

  //  let np = Some?.v x;
   
  //  is_tree_case_some x np;
      
  //  with _node _ltree _rtree._;
      
  //  let node_x = !np;
      
  //  rewrite each _node as node_x;

  //  (*Current context:
  //   is_tree node.right (reveal rtree) **
  //   is_tree node.left (reveal ltree) ** pts_to np node ** is_tree rtr rtree*)

  //  //get the data, data_x from the node_x --- data_x
  //  let data_x = node_x.data;
   
  //  (* Current context:
  //   pure (data_x == node_x.data) **
  //   is_tree node_x.right (reveal rtree) **
  //   is_tree node_x.left (reveal ltree) ** pts_to np node_x ** is_tree rtr rtree*)

   

  // //get the node, node_r from the right tree of x, node_x.right --- T.Node data_xr left_xr right_xr
  // let r_np = Some?.v rtr;
  // (*Current context:
  //   pure (r_np == rtr.v) **
  //   is_tree node_x.right (reveal rtree) **
  //   is_tree node_x.left (reveal ltree) ** pts_to np node_x ** is_tree rtr rtree*)
  
  // is_tree_case_some rtr r_np;
  // (*Current context:
  //   (exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
  //     pts_to r_np node ** is_tree node.left ltree ** is_tree node.right rtree **
  //     pure (rtree == T.Node node.data ltree rtree)) **
  //   is_tree node_x.right (reveal rtree) **
  //   is_tree node_x.left (reveal ltree) ** pts_to np node_x*)
  
  // show_proof_state;
      
  //  with _node_r _ltree_r _rtree_r._;
      
  //  let node_r = !r_np;
      
  //  rewrite each _node_r as node_r;
  
  
  // show_proof_state;
  // //get the data, data_r from node_r --- data_xr

  // //create subnode with data_x, 
  // // left tree as node.left
  // // right tree as (node_r).left 

  // // create a new node with data as data_r, left as x
  // // right node_r.right;

  // //write in (node_x).right new node

  // //write in x subnode

  // //pack_tree x (node_x.left) (node_r.left);

  // //pack_tree (node_x.right) x (node_r.right);

  // // (node_x.right)

  // admit()
 
}
```



(*(data:t) (ltree:T.tree t) (rtree:T.tree t)
requires is_tree ct ft ** pure (ft == T.Node data ltree rtree)*)



(*fn is_tree_case_some (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
requires is_tree x ft ** pure (x == Some v)
ensures  
   exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    pts_to v node **
    is_tree node.left ltree **
    is_tree node.right rtree **
    pure (ft == T.Node node.data ltree rtree)*)

    
