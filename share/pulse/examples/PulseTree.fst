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

module G = FStar.Ghost

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

```pulse //cases_of_is_tree$ -CHECK THIS AGAIN
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
(*Ctrl + K, Ctrl + U removes the // comments*)

```pulse
fn node_cons (#t:Type0) (v:t) (ltree:tree_t t) (rtree:tree_t t) 
  requires is_tree ltree 'l  **
           is_tree rtree 'r  //functional equivalent of x is 'l; x is the tail of the constructed tree.
  returns y:tree_t t
  ensures is_tree y (T.Node v 'l 'r) ** (pure (Some? y))
{
  let y = alloc { data=v; left =ltree; right = rtree };
  rewrite each ltree as ({data = v; left = ltree; right = rtree}).left in (is_tree ltree 'l);
  rewrite each rtree as ({data = v; left = ltree; right = rtree}).right in (is_tree rtree 'r);
  intro_is_tree_node (Some y) y;
  Some y
}
```


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



/// Appends value [v] at the leftmost leaf of the tree that [ptr] points to.
```pulse
fn rec append_left_none (#t:Type0) (x:tree_t t) (v:t) 
requires is_tree x 'l ** pure (None? x)
returns y:tree_t t
ensures is_tree x 'l  ** is_tree y (T.Node v T.Leaf T.Leaf)
{
  let left = create t;
  let right = create t;
  let y = node_cons v left right;
      //intro_is_tree_nil x;
      //fold (is_tree y (T.append_left 'l v));
      //rewrite each (None #(ref (node t))) as x;
      //y
      //elim_is_tree_nil x;
  //intro_is_tree_nil x;
  //intro_is_tree_cons y;
  y // How can we remove is_tree x 'l from the context?
}
```



```pulse
fn rec append_left (#t:Type0) (x:tree_t t) (v:t) 
requires is_tree x 'l
returns y:tree_t t
ensures is_tree y  (T.append_left 'l v)
{
   match x {
    None -> {
      //current context: is_tree x (reveal 'l)
      (*cond: requires is_tree x l ** pure (x == None)
              ensures  is_tree x l ** pure (l == T.Leaf)*)
      is_tree_case_none x;
      //current context: is_tree x (reveal 'l) ** pure (reveal 'l == T.Leaf)
      (*cond: requires is_tree x 'l ** pure ('l == T.Leaf)
              ensures pure (x == None)*)
      elim_is_tree_leaf x;
      //current cotext: pure (x == None)
      
      let left = create t;
      let right = create t;
      //Current context: is_tree right T.Leaf ** is_tree left T.Leaf
    
      let y = node_cons v left right;
      //Current context:
      //is_tree y (T.Node v (reveal (hide T.Leaf)) (reveal (hide T.Leaf))) **
      //pure (Some? y)
    
      let np = Some?.v y;
      
    //Current context:
    //pure (np == y.v) **
    //is_tree y (T.Node v (reveal (hide T.Leaf)) (reveal (hide T.Leaf)))
     (*cond: requires is_tree x ft ** pure (x == Some v)
             ensures  
                exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
                pts_to v node **
                is_tree node.left ltree **
                is_tree node.right rtree **
                pure (ft == T.Node node.data ltree rtree)*)
     is_tree_case_some y np;

     (*Current context:
               (exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
               pts_to np node ** 
               is_tree node.left ltree ** 
               is_tree node.right rtree **
               pure (T.Node v (reveal (hide T.Leaf)) (reveal (hide T.Leaf)) ==
               T.Node node.data ltree rtree))*)
    
      intro_is_tree_node y np;

      (*Current context:
        is_tree y (T.Node (reveal node).data (reveal ltree) (reveal rtree)*)
      (*requires
        pts_to v node **
        is_tree node.left ltree **
        is_tree node.right rtree **
        pure (ct == Some v)
      ensures
        is_tree ct (T.Node node.data ltree rtree)*)
      y 
    }
    Some vl -> {
      //current context: is_tree x (reveal 'l)
      let np = Some?.v x;
      (*Current context:
        pure (np == x.v) ** is_tree x (reveal 'l)*)
      is_tree_case_some x np;
      (*Current context:
        (exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
         pts_to np node ** is_tree node.left ltree ** is_tree node.right rtree **
         pure (reveal 'l == T.Node node.data ltree rtree))*)
      with _node _ltree _rtree._;
      (*Current context:
        pts_to np (reveal node) **
        is_tree (reveal node).left (reveal ltree) **
        is_tree (reveal node).right (reveal rtree) **
        pure (reveal 'l == T.Node (reveal node).data (reveal ltree) (reveal rtree))*)
      let node = !np;
      (*Current context:
         pts_to np (reveal node) **
         pure (reveal node == node) **
        is_tree (reveal node).left (reveal ltree) **
        is_tree (reveal node).right (reveal rtree)*)
      
      rewrite each _node as node;

      (*Current context:
        is_tree node.right (reveal rtree) **
        is_tree node.left (reveal ltree) ** pts_to np node*)

      
      let left_new = append_left node.left v;
      
      (*Current context:
        is_tree left_new (T.append_left (reveal ltree) v) **
        pts_to np node ** is_tree node.right (reveal rtree)*)
      np := {node with left = left_new};
      
       
      (*Current context:
        pts_to np (Mknode node.data left_new node.right) **
        is_tree node.right (reveal rtree) **
        is_tree left_new (T.append_left (reveal ltree) v)*)
      
       rewrite each left_new as ({ node with left = left_new }).left in (is_tree left_new ((T.append_left (reveal _ltree) v)));
      

      (*Current context:
         is_tree (Mknode node.data left_new node.right).left
                (T.append_left (reveal ltree) v) **
         pts_to np (Mknode node.data left_new node.right) **
         is_tree node.right (reveal rtree)*)

       rewrite each node.right as ({ node with left = left_new }).right in (is_tree node.right _rtree);
       
      (*Current context:
         is_tree (Mknode node.data left_new node.right).right (reveal rtree) **
         is_tree (Mknode node.data left_new node.right).left
                  (T.append_left (reveal ltree) v) **
        pts_to np (Mknode node.data left_new node.right)*)
       
       intro_is_tree_node x np;

       (*Current context:
        is_tree x
             (T.Node (Mknode node.data left_new node.right).data
                  (T.append_left (reveal ltree) v)
                  (reveal rtree))*)
       //show_proof_state;

      x
    }
  }
} 
```


```pulse
fn rec append_right (#t:Type0) (x:tree_t t) (v:t) 
requires is_tree x 'l
returns y:tree_t t
ensures is_tree y  (T.append_right 'l v)
{
   match x {
    None -> {
      
      is_tree_case_none x;
      
      elim_is_tree_leaf x;
     
      let left = create t;
      let right = create t;
      
    
      let y = node_cons v left right;
      
      let np = Some?.v y;
      
      is_tree_case_some y np;

      intro_is_tree_node y np;
      
      y 
    }
    Some vl -> {
      
      let np = Some?.v x;
      
      is_tree_case_some x np;
      
      with _node _ltree _rtree._;
      
      let node = !np;
      
      rewrite each _node as node;

      let right_new = append_right node.right v;
      
      np := {node with right = right_new};
      
      rewrite each right_new as ({ node with right = right_new }).right in (is_tree right_new ((T.append_right (reveal _rtree) v)));
      
      rewrite each node.left as ({node with right = right_new}).left in (is_tree node.left _ltree);
      
      intro_is_tree_node x np;
      
      x
    }
  }
} 
```

```pulse
fn node_data (#t:Type) (x:tree_t t) 
    requires is_tree x 'l  ** (pure (Some? x))
    returns v:t
    ensures is_tree x 'l 
{
  let np = Some?.v x;
      
  is_tree_case_some x np;
      
  with _node _ltree _rtree._;
      
  let node = !np;
      
  rewrite each _node as node;

  let v = node.data;
  
  intro_is_tree_node x np;
  v
}
```

```pulse
fn rec is_mem (#t:eqtype) (x:tree_t t) (v: t)
    requires is_tree x 'l
    returns b:bool
    ensures is_tree x 'l ** pure (b <==> (T.mem 'l v))
{
   match x {
        None -> {
            is_tree_case_none x;
            false
        }
        Some vl -> {
            //let dat = node_data x;
            is_tree_case_some x vl;
            with _node _ltree _rtree. _;
            let n = !vl;
            rewrite each _node as n;

            let dat = n.data;
            
            if (dat = v) 
            {
              intro_is_tree_node x vl;
              true
            }
            else{
              let b1 = is_mem n.left v;
              let b2 = is_mem n.right v;

              let b3 = b1 || b2;
              intro_is_tree_node x vl;
              b3;
              
            }
        }
    }
}
```



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
//       }
//       Some vl -> {
//         admit()
//       }
//     }
   

module G = FStar.Ghost

```pulse
fn get_some_ref (#t:Type) (x:tree_t t) (#ft:G.erased (T.tree t))
requires is_tree x ft ** pure (T.Node? ft)
returns v:node_ptr t
ensures  
  exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    pure (x == Some v) **
    pure (ft == T.Node node.data ltree rtree) **
    pts_to v node **
    is_tree node.left ltree **
    is_tree node.right rtree
{
  match x {
    None -> {
      is_tree_case_none x;
      unreachable ()
    }
    Some v -> {
      is_tree_case_some x v;
      v
    }
  }
}
```
(*let rotate_left (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x t1 (Node z t2 t3) -> Some (Node z (Node x t1 t2) t3)
  | _ -> None*)
  
```pulse
fn rotate_left (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_left l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_left l)))
{
  let vl = get_some_ref tree;
  let n = !vl;
  let vlr = get_some_ref n.right;
  let nr = !vlr;
  (*--------------------------------------------------------------------------------------*)
  (*vl points to n*)
  (*x = n.data, t1 = n.left, (Node z t2 t3) = n.right *)

  (*vlr points to nr*)
  (*z = nr.data, t2 = nr.left, t3 = nr.right*)
  (*--------------------------------------------------------------------------------------*)

  vlr := { data = n.data; left = n.left; right = nr.left };
  
  (*vlr points to a sub_node as above *)
  (*x = n.data = sub_node.data, t1 = n.left = sub_node.left, t2 = nr.left = sub_node.right*)
  (*Node x t1 t2 ---- shape of spec*)
  
  intro_is_tree_node (Some vlr) vlr #{data = n.data; left = n.left; right = nr.left};
  (*pack the sub_node into a tree as above (Some vlr) is the tree which is an optional pointer to a node*)
  
  (*vl points to new_node*)
  vl := { data = nr.data; left = Some vlr; right = nr.right };
  (*z = nr.data = new_node.data, Some vlr = sub_node_tree = new_node.left, t3 = nr.right = new_node.right *)
  (*(Node z (Node x t1 t2) t3) ----- shape of spec*) 

  intro_is_tree_node (Some vl) vl #{data = nr.data; left = Some vlr; right = nr.right};
  (*pack new_node pointed to vl as a tree, (Some vl)*)

  Some vl
  (*return the newly formed tree.*)
  (*is_tree takes a concrete tree which is a (option node pointer), and a functional tree*)
  (*The functional tree is passed as l and the pre-condition says that the functional tree 
    obtained after rotating l to the left is Some*)
  (*for post condition, extract the functional tree from Some and match with the tree returned (Some vl)*)
}
```

(*let rotate_right (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x (Node z t1 t2) t3 -> Some (Node z t1 (Node x t2 t3))
  | _ -> None*)



```pulse
fn rotate_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_right l)))
{
  let vl = get_some_ref tree;
  let n = !vl;
  let vll = get_some_ref n.left;
  let nl = !vll;

  (*create the sub_node, (Node x t2 t3)*)
  vll := {data = n.data; left = nl.right; right = n.right};

  (*pack the sub_node pointed to vll as a new tree*)
  intro_is_tree_node (Some vll) vll #{data = n.data; left = nl.right; right = n.right};

  (*create the new_node (Node z t1 (Node x t2 t3))*)
  vl := {data = nl.data; left = nl.left; right = Some vll};

  (*pack the new_node pointed to vl as a new_tree*)
  intro_is_tree_node (Some vl) vl #{data = nl.data; left = nl.left; right = Some vll};
  Some vl
}
```
(*let rotate_right_left (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x t1 (Node z (Node y t2 t3) t4) -> Some (Node y (Node x t1 t2) (Node z t3 t4))
  | _ -> None*)

```pulse
fn rotate_right_left (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right_left l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_right_left l)))
{
  let vl = get_some_ref tree;
  let n = !vl;

  let vlr = get_some_ref n.right;

  let nr = !vlr;
  
  let vlrl = get_some_ref nr.left;

  let nrl = !vlrl;

  (*Construction of sub_node_right*)
   
  vlr := {data = nr.data; left = nrl.right; right = nr.right};
  (* (Node z t3 t4)*)
  intro_is_tree_node (Some vlr) vlr #{data = nr.data; left = nrl.right; right = nr.right};
  //intro_is_tree_node (Some vlrl) vlrl #{data = nr.data; left = nrl.right; right = nr.right};

  vlrl := {data = n.data; left = n.left; right = nrl.left};

  intro_is_tree_node (Some vlrl) vlrl #{data = n.data; left = n.left; right = nrl.left};

  vl := {data = nrl.data; left = Some vlrl; right = Some vlr};

  intro_is_tree_node (Some vl) vl #{data = nrl.data; left = Some vlrl; right = Some vlr};

  Some vl
}
```

(*let rotate_left_right (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x (Node z t1 (Node y t2 t3)) t4 -> Some (Node y (Node z t1 t2) (Node x t3 t4))
  | _ -> None*)
```pulse
fn rotate_left_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_left_right l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_left_right l)))
{
  (*Node x (Node z t1 (Node y t2 t3)) t4 -> Some (Node y (Node z t1 t2) (Node x t3 t4))
                      |----vllr---|
           |----------vll-----------|
   |---------vl------------------------|            *)
  let vl = get_some_ref tree;

  let n = !vl;

  let vll = get_some_ref n.left;

  let nl = !vll;

  let vllr = get_some_ref nl.right;

  let nlr = !vllr;

  vllr := {data = n.data; left = nlr.right; right = n.right};

  vll := {data = nl.data; left = nl.left; right = nlr.left};

  intro_is_tree_node (Some vllr) vllr #{data = n.data; left = nlr.right; right = n.right};

  intro_is_tree_node (Some vll) vll #{data = nl.data; left = nl.left; right = nlr.left};

  vl := {data = nlr.data; left = Some (vll); right = Some vllr};

  intro_is_tree_node (Some vl) vl #{data = nlr.data; left = Some (vll); right = Some vllr};
  
  Some vl
}
```

(*** Functions related to AVL trees ***)

/// Returns a boolean indicating if the tree that [ptr] points to is balanced

(*let rec is_balanced (#a: Type) (x: tree a) : bool =
  match x with
  | Leaf -> true
  | Node data left right ->
    M.abs(height right - height left) <= 1 &&
    is_balanced(right) &&
    is_balanced(left)*)

module M = FStar.Math.Lib

```pulse
fn rec is_balanced (#t:Type0) (tree:tree_t t)
requires is_tree tree 'l
returns b:bool
ensures is_tree tree 'l ** pure (b <==> (T.is_balanced 'l))
{
  match tree {
    None -> {
      is_tree_case_none tree;
      true
    }
    Some vl -> {
      is_tree_case_some tree vl;
      let n = !vl;

      let height_l = height n.left;
      let height_r = height n.right;

      let b1 =  (M.abs(height_r - height_l) <= 1);

      let b2 = is_balanced n.right;

      let b3 = is_balanced n.left;

      let b4 = b1 && b2 && b3;
      
      intro_is_tree_node tree vl;
      
      b4
    }
  }
}

```

/// Rebalances a tree according to the comparison function [cmp] on the tree elements

(*let rebalance_avl (#a: Type) (x: tree a) : tree a =
    match x with
    | Leaf -> x
    | Node data left right ->

      if is_balanced x then x
      else (

        if height left - height right > 1 then (
          let Node ldata lleft lright = left in
          if height lright > height lleft then (
            match rotate_left_right x with
            | Some y -> y
            | _ -> x
          ) else (
            match rotate_right x with
            | Some y -> y
            | _ -> x
          )

        ) else if height left - height right < -1 then (
          let Node rdata rleft rright = right in
            if height rleft > height rright then (
              match rotate_right_left x with
              | Some y -> y
              | _ -> x
            ) else (
              match rotate_left x with
              | Some y -> y
              | _ -> x
            )
        ) else (
          x
        )
      )

*)

```pulse
fn rec  rebalance_avl (#t:Type0) (tree:tree_t t)
requires is_tree tree 'l
returns y:tree_t t 
ensures (is_tree y (T.rebalance_avl 'l))
{
  //if the below statament is put in the Some branch, it will not work. 
  //Because is_tree tree 'l is not in context at that point.
  //Why it is not there in context at that point? Is it desirable?
  let b = is_balanced tree;
  match tree {
    None -> {
      is_tree_case_none tree;
      tree
    }
    Some vl -> {
      is_tree_case_some tree vl;
      
      if (b)
      {
        intro_is_tree_node tree vl;
        tree
      }
      else
      {
        let n = !vl;
        let height_l = height n.left;
        let height_r = height n.right;
        
        let diff_height = height_l - height_r ;

        if (diff_height > 1) 
        {
          let vll = get_some_ref n.left;
          intro_is_tree_node n.left vll;
          is_tree_case_some n.left vll;
         

          let nl = !vll;

          let height_ll = height nl.left;
          let height_lr = height nl.right;

          if (height_lr > height_ll)
          {
             (*Only in this branch, this situation happens, Node x (Node z t1 (Node y t2 t3)) t4*)
             let vllr = get_some_ref nl.right;
             
             (*pack tree back in the order it is unpacked*)
             intro_is_tree_node nl.right vllr;
             
             intro_is_tree_node n.left vll;
            
             
             intro_is_tree_node tree vl;
             
             (*Current context:
                      is_tree tree
                               (T.Node n.data
                                (T.Node nl.data
                                    (G.reveal ltree)
                                        (T.Node (G.reveal node).data (G.reveal ltree) (G.reveal rtree)))
                                    (G.reveal rtree))*)

             let y = rotate_left_right tree;
             y
          }
          else
          {
            (*Node x (Node z t1 t2) t3*)
            intro_is_tree_node n.left vll;
            intro_is_tree_node tree vl;
            let y = rotate_right tree;
            y
          }
        }
        else if (diff_height < -1)
        {
          let vlr = get_some_ref n.right;
          intro_is_tree_node n.right vlr;
          is_tree_case_some n.right vlr;
         

          let nr = !vlr;

          let height_rl = height nr.left;
          let height_rr = height nr.right;
          if (height_rl > height_rr)
          {
             (*Node x t1 (Node z (Node y t2 t3) t4)*)
             let vlrl = get_some_ref nr.left;
             
             (*pack tree back in the order it is unpacked*)
             intro_is_tree_node nr.left vlrl;
             intro_is_tree_node n.right vlr;
             intro_is_tree_node tree vl;
             let y = rotate_right_left tree;
             y
          }
          else
          {
            (*Node x t1 (Node z t2 t3)*)
            intro_is_tree_node n.right vlr;
            intro_is_tree_node tree vl;
            let y = rotate_left tree;
            y
          }
          
        }
        else
        {
          intro_is_tree_node tree vl;
          tree
        }
        
      }
    }
  }
}
```

```pulse
fn rec insert_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t)
requires is_tree tree 'l
returns y:tree_t t 
ensures (is_tree y (T.insert_avl cmp 'l key))
{
  match tree {
    None -> {
       is_tree_case_none tree;
      
       elim_is_tree_leaf tree;
     
       let left = create t;
       let right = create t;
      
    
       let y = node_cons key left right;
      
       let np = Some?.v y;
      
       is_tree_case_some y np;

       intro_is_tree_node y np;
       
       y
    }
    Some vl -> {
      is_tree_case_some tree vl;
      let n = !vl;
      let delta = cmp n.data key;
      if (delta >= 0)
      {
        let new_left = insert_avl cmp n.left key;
        vl := {data = n.data; left = new_left; right = n.right};
        intro_is_tree_node (Some vl) vl #({data = n.data; left = new_left; right = n.right});
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
      else
      {
        let new_right = insert_avl cmp n.right key;
        vl := {data = n.data; left = n.left; right = new_right};
        intro_is_tree_node (Some vl) vl #({data = n.data; left = n.left; right = new_right});
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
    }
  }
}
```


