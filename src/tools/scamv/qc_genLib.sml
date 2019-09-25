structure qc_genLib : qc_genLib =
struct

datatype 'a Gen
  = Gen of (int -> Random.generator -> 'a);

(* sized :: (Int -> Gen a) -> Gen a *)
fun sized fgen = Gen (fn n => fn r =>
                         let val (Gen m) = fgen n in m n r end);

(* resize :: Int -> Gen a -> Gen a *)
fun resize n (Gen m) = Gen (fn _ => fn r => m n r);

(* rand :: Gen Random.generator *)
val rand = Gen (fn n => fn r => r);

(* promote :: (a -> Gen b) -> Gen (a -> b) *)
fun promote f = Gen (fn n => fn r => fn a =>
                        let val (Gen m) = f a in m n r end)

(* generate :: Int -> StdGen -> Gen a -> a *)
fun generate n rnd (Gen m) =
    let val sz = Random.range (0,n) rnd;
    in
        m sz rnd
    end

fun run_step n rnd (Gen m) =
    let val sz = Random.range (0,n) rnd;
    in
        (m sz rnd, rnd)
    end

fun return a = Gen (fn n => fn r => a);

fun >>= (Gen m,k) =
    Gen (fn n => fn r0 =>
            let val (Gen m') = k (m n r0)
            in m' n r0 end);
infix 5 >>=;

fun map_gen f m = m >>= (return o f)
fun op <$> (f,x) = map_gen f x;
infix 5 <$>;

fun two m1 m2 = ((fn x => fn y => (x,y)) <$> m1) >>=
                                                 (fn g => (m2 >>= (fn y => return (g y))));

fun sequence [] = return []
  | sequence (m::ms) = (op ::) <$> two m (sequence ms)

fun repeat n m =
    sequence (List.tabulate (n, fn _ => m));

fun sample amount n rnd g =
    generate n rnd (repeat amount g)

fun choose (a,b) =
    (Random.range (a,b)) <$> rand

fun elements xs =
    (fn i => List.nth (xs,i)) <$> choose (0, List.length xs - 1);

fun id x = x;
fun oneof gens = elements gens >>= id;

fun frequency xs =
    let val sum = List.foldr (op +) 0;
        val tot = sum (List.map fst xs);
        fun pick ((k,x)::xs) n =
            if n <= k
            then x
            else pick xs (n-k)
    in
        choose (1, tot) >>= (pick xs)
    end
end

(*
-- general monadic

two :: Monad m => m a -> m (a, a)
two m = liftM2 (,) m m

three :: Monad m => m a -> m (a, a, a)
three m = liftM3 (,,) m m m

four :: Monad m => m a -> m (a, a, a, a)
four m = liftM4 (,,,) m m m m

--------------------------------------------------------------------
-- Arbitrary

class Arbitrary a where
  arbitrary   :: Gen a
  coarbitrary :: a -> Gen b -> Gen b

instance Arbitrary () where
  arbitrary     = return ()
  coarbitrary _ = variant 0

instance Arbitrary Bool where
  arbitrary     = elements [True, False]
  coarbitrary b = if b then variant 0 else variant 1

instance Arbitrary Char where
  arbitrary     = choose (32,255) >>= \n -> return (chr n)
  coarbitrary n = variant (ord n)

instance Arbitrary Int where
  arbitrary     = sized $ \n -> choose (-n,n)
  coarbitrary n = variant (if n >= 0 then 2*n else 2*(-n) + 1)

instance Arbitrary Integer where
  arbitrary     = sized $ \n -> choose (-fromInt n,fromInt n)
  coarbitrary n = variant (fromInteger (if n >= 0 then 2*n else 2*(-n) + 1))

instance Arbitrary Float where
  arbitrary     = liftM3 fraction arbitrary arbitrary arbitrary 
  coarbitrary x = coarbitrary (decodeFloat x)

instance Arbitrary Double where
  arbitrary     = liftM3 fraction arbitrary arbitrary arbitrary 
  coarbitrary x = coarbitrary (decodeFloat x)

fraction a b c = fromInteger a + (fromInteger b / (abs (fromInteger c) + 1))

instance (Arbitrary a, Arbitrary b) => Arbitrary (a, b) where
  arbitrary          = liftM2 (,) arbitrary arbitrary
  coarbitrary (a, b) = coarbitrary a . coarbitrary b

instance (Arbitrary a, Arbitrary b, Arbitrary c) => Arbitrary (a, b, c) where
  arbitrary             = liftM3 (,,) arbitrary arbitrary arbitrary
  coarbitrary (a, b, c) = coarbitrary a . coarbitrary b . coarbitrary c

instance (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d)
      => Arbitrary (a, b, c, d)
 where
  arbitrary = liftM4 (,,,) arbitrary arbitrary arbitrary arbitrary
  coarbitrary (a, b, c, d) =
    coarbitrary a . coarbitrary b . coarbitrary c . coarbitrary d

instance Arbitrary a => Arbitrary [a] where
  arbitrary          = sized (\n -> choose (0,n) >>= vector)
  coarbitrary []     = variant 0
  coarbitrary (a:as) = coarbitrary a . variant 1 . coarbitrary as

instance (Arbitrary a, Arbitrary b) => Arbitrary (a -> b) where
  arbitrary         = promote (`coarbitrary` arbitrary)
  coarbitrary f gen = arbitrary >>= ((`coarbitrary` gen) . f)
*)
