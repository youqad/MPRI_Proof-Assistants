Class Monad (M : Type -> Type) :=
  { ret : forall {A}, A -> M A ;
    bind : forall {A B}, M A -> (A -> M B) -> M B ;

    bind_assoc {A B C} (x : M A) (f : A -> M B) (g : B -> M C) : 
    bind x (fun a => bind (f a) g) = bind (bind x f) g;

    bind_ret_l {A B} (x : A) (f : A -> M B) : 
      bind (ret x) f = f x;

    bind_ret_r {A} (x : M A) : bind x ret = x;
 }.