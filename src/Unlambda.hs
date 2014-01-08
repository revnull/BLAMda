{-# LANGUAGE RankNTypes #-}

import Profunctor
import Control.Monad.Error
import Data.Maybe
import Data.Char
import Unsafe.Coerce
import qualified Data.Set as S
import qualified Data.Map as M

data ExpF a b =
    App b b
  | AppCPS b b b 
  | Lam (a -> b)
  | Chr Char
  | Builtin String 
  | Promise

instance Profunctor ExpF where
    dimap f g (App x y) = App (g x) (g y)
    dimap f g (AppCPS x y k) = AppCPS (g x) (g y) (g k)
    dimap f g (Lam h)   = Lam (g . h . f)
    dimap f g (Chr c) = Chr c
    dimap f g (Builtin s) = Builtin s
    dimap f g Promise = Promise

data Rec p a b
    = Place b
    | Roll (p a (Rec p a b))

type Exp = Rec ExpF

instance Profunctor p => Monad (Rec p a) where
    return = Place
    Place b >>= f = f b
    Roll bs >>= f = Roll $ rmap (>>= f) bs

cata :: Profunctor p => (p a b -> b) -> Rec p a b -> b
cata _ (Place b) = b
cata phi (Roll bs) = phi (rmap (cata phi) bs)

lam :: (a -> Exp a b) -> Exp a b
lam f = Roll (Lam f)

app :: Exp a b -> Exp a b -> Exp a b
app x y = Roll (App x y)

appCPS :: Exp a b -> Exp a b -> Exp a b -> Exp a b
appCPS x y k = Roll (AppCPS x y k)

var :: b -> Exp a b
var = return

builtin :: String -> End Exp
builtin s = Roll $ Builtin s

dot :: Char -> End Exp
dot c = Roll (Chr c)

k :: End Exp
k = lam $ \x -> lam $ \y -> var x

s :: End Exp
s = lam $ \x -> lam $ \y -> lam $ \z -> 
    app (app (var x) (var z)) (app (var y) (var z))

i :: End Exp
i = lam $ \x -> var x

v :: End Exp
v = lam $ \_ -> builtin "v"

d :: End Exp
d = Roll $ Promise

type End p = forall x. p x x

iter0 :: Profunctor p => (p a a -> a) -> End (Rec p) -> a
iter0 phi x = cata phi x

dump :: End Exp -> String
dump b = cata phi b vars "" where
    phi (App f g) xs = showString "(" . f xs . showString ") (" .
        g xs . showString ")"
    phi (AppCPS f g k) xs = showChar '(' . f xs . showString ") (" .
        g xs . showString ") $ ( " . k xs . showChar ')'
    phi (Lam h) (x:xs) = showChar '\\' . showString x . showString " -> " .
        h (const (showString x)) xs
    phi (Chr c) xs = showChar '.' . showChar c . showChar ' '
    phi (Builtin b) xs = showChar '&' . showString b
    phi Promise _ = showString "{PROMISE}"
    strs = fmap (:[]) ['a'..'z']
    vars = strs ++ zipWith (++) (cycle strs) vars

compileBuiltins = foldr (.) id bic where
    bic = map comp bi
    comp (name, exp) = toC name $ optimize $ toCPS $ (unsafeCoerce exp)
    bi = [("s",s), ("i",i), ("k", k), ("v", v)] ++ dots
    dots = do
        c <- map chr [0..255]
        return $ ("dot_" ++ (show $ ord c), dot c)

toC :: String -> End Exp -> String -> String
toC name b = c where
    (_ , _, c, _, _) = cata phi b 0 M.empty vars
    phi (App f g) 0 vs (x:xs) = appExp where
        (fn, Nothing, fs, _, xs') = f 0 vs xs
        (gn, Nothing, gs, _, xs'') = g 0 vs xs'
        s = showString "closure " . x . showString "= {&root,0,apply,2,{"
            . fn . showChar ',' . gn . showString "}};\n"
        frag = fn . showString "->fn(" . fn . showChar ',' .
            gn . showString ",cont);";
        appExp = (showChar '&' . x, Just (True, frag), fs . gs . s,
            S.empty, xs'')
    phi (App f g) d vs (x:xs) = appExp where
        (fn, ff, fs, vl, xs') = f d vs xs
        (gn, gf, gs, vr, xs'') = g d vs xs'
        frag = fn . showString "->fn(" . fn . showChar ',' .
            gn . showString ",cont);";
        frags = foldr (.) id $ fmap snd $ catMaybes [ff, gf]
        appExp = (x, Just (True, frags . frag), fs . gs, S.union vl vr, xs'')
    phi (AppCPS f g k) d vs (x:xs) = appExp where
        (fn, ff, fs, vl, xs') = f d vs xs
        (gn, gf, gs, vr, xs'') = g d vs xs'
        (kn, kf, ks, vk, xs''') = k d vs xs''
        frag = showString "ALLOC_F(c,2);c->fn=compose;c->data[0]=" .
            kn . showString ";c->data[1]=cont;" .
            fn . showString "->fn(" . fn . showChar ',' .
            gn . showString ",c); //HERE\n"
        frags = foldr (.) id $ fmap snd $ catMaybes [ff, gf, kf]
        appExp = (x, Just (True, frags . frag), fs . gs . ks,
            S.union vk $ S.union vl vr, xs''')
    phi (Lam h) d vs (x:xs) = lamExp where
        (c, cf', sub, v, xs') = h hf (d + 1) vs' xs
        vs' = if S.member d v
            then M.insert d (-1) vs''
            else vs''
        vs'' = M.fromList $ zip (takeWhile (< d) $ S.toAscList v) [0..]
        cf = case cf' of
            Just (True, x) -> x
            Just (False, x) -> x . showString "eval(" . c . showString ",cont);"
            Nothing -> showString "eval(" . c . showString ",cont);"
        hf d' vs xs'' = if d == d' - 1
            then (showString "input", Nothing, id, S.empty, xs'')
            else (var, Nothing, id, S.singleton d, xs'') where
                var = showString "self->data[" . shows w . showChar ']'
                w = fromJust $ M.lookup d vs
        fnname = showChar 'l' . x
        proto = showString "void " . fnname . 
            showString "(closure *self, closure *input, closure *cont);"
        fn = showString "void " . fnname . 
            showString "(closure *self, closure *input, closure *cont) {\n" .
            cf . showString "}\n"
        clos = showString "closure " . x .
            showString "={&root,0," . fnname . showString ",0};\n"
        frag = showString "ALLOC_F(" . x . showChar ',' . shows (M.size vs'') .
            showString ");" . x . showString "->fn=" . fnname .
            showString ";" . copyvars
        copyvars = foldr (.) id $ do
            i <- [0..d-1]
            (Just sb) <- return $ M.lookup i vs
            (Just xb) <- return $ M.lookup i vs'
            let bind = if (sb < 0)
                    then showString "input;"
                    else showString "self->data[" . shows sb . showString "];"
            return $ x . showString "->data[" . shows xb . showString "]=" .
                bind
--        copyvars = foldr (.) id $ map copy [0..d-2]
        copy i = if S.member i v
            then x . showString "->data[" . shows i .
                showString "]=self->data[" . shows i . showString "];"
            else x . showString "->data[" . shows i .
                showString "]=NULL;"
        lamExp = if d == 0
            then (showChar '&' . x, Nothing, sub . proto . clos . fn, v, xs')
            else (x, Just (False, frag), sub . fn, v, xs')
    phi (Chr c) 0 vs (x:xs) = chrExp where
        fnname = showChar 'l' . x
        fn = showString "void " . fnname . 
            showString "(closure *self, closure *input, closure *cont) {\n" .
            showString "putchar(" . shows (ord c) . 
            showString ");eval(input,cont);}\n"
        clos = showString "closure " . x .
            showString "={&root,0," . fnname . showString ",0};\n"
        chrExp = (showChar '&' . x, Nothing, fn . clos, S.empty, xs)
    phi (Builtin name) _ vs xs =
        (showChar '&' . showString name, Nothing, id, S.empty, xs)
    vars = (showString name):(fmap ((showString name .) . shows) [0..])

toCValue :: End Exp -> String
toCValue b = include . compileBuiltins . c . main . d $ "" where
    include = showString "#include \"unlambda_core.c\"\n"
    c = toC "p" b
    main = showString "int main() { initialize(&p,&ex);}\n"
    d = showString "/*\n" . showString (dump b) . showString "\n*/\n"

compile :: String -> Either String (Exp a a)
compile input = case compile' 0 input of
    (Right [x]) -> Right x
    (Right []) -> Left "No Input"
    (Right _) -> Left "Unconsumed input"
    (Left err) -> Left err

compile' :: Int -> String -> Either String [Exp a a]
compile' _ [] = Right []
compile' c ('`':xs) = 
    case compile' (c + 1) xs of
        (Right (f:g:xxs)) -> Right $ (app f g):xxs
        (Right _) -> Left $ "` failed at character " ++ show c
        l -> l
compile' c ('s':xs) = fmap (s:) $ compile' (c + 1) xs
compile' c ('k':xs) = fmap (k:) $ compile' (c + 1) xs
compile' c ('i':xs) = fmap (i:) $ compile' (c + 1) xs
compile' c ('d':xs) = fmap (d:) $ compile' (c + 1) xs
compile' c ('v':xs) = fmap (v:) $ compile' (c + 1) xs
compile' c ('c':xs) = fmap ((builtin "callcc"):) $ compile' (c + 1) xs
compile' c ('r':xs) = fmap ((builtin "dot_10"):) $ compile' (c + 1) xs
compile' c ['.'] = Left $ ". failed at character " ++ show c
compile' c ('.':x:xs) = fmap ((builtin $ "dot_" ++ show (ord x)):) $
    compile' (c + 2) xs
compile' c (_:xs) = compile' (c + 1) xs

compileFile :: FilePath -> FilePath -> IO ()
compileFile input output = do
    contents <- readFile input
    case compile contents of
        (Left err) -> print $ "Error: " ++ err
        (Right exp) -> writeFile output $ toCValue $
            optimize $ toCPS $ computePromise $ optimize $ unsafeCoerce exp

optimize :: End Exp -> End Exp
optimize b = opt where
    (optb, _, opt') = cata phi b Nothing
    opt = if optb then optimize (unsafeCoerce opt') else opt'
    phi (App l r) Nothing = appExp where
        (lo, lb, l') = l $ if rb then Nothing else (Just r')
        (_, rb, r') = r Nothing
        appExp = if lo && (not (lb || rb))
            then (True, lb, l')
            else (lo, lb, app l' r')
    phi (App l r) (Just v) = appExp where
        (lo, lb, l') = l $ if rb then Nothing else (Just r')
        (_, rb, r') = r Nothing
        appExp = if lo && (not (lb || rb))
            then (True, lb, app l' v)
            else (lo, lb, app l' r')
    phi (AppCPS l r k) Nothing = appExp where
        (lo, lb, l') = l $ if rb then Nothing else (Just r')
        (_, rb, r') = r Nothing
        (_, _, k') = k Nothing
        appExp = if lo && (not (lb || rb))
            then (True, lb, app k' l')
            else (False, lb, appCPS l' r' k')
    phi (AppCPS l r k) (Just v) = appExp where
        (lo, lb, l') = l $ if rb then Nothing else (Just r')
        (_, rb, r') = r Nothing
        (_, _, k') = k Nothing
        appExp = if lo && (not (lb || rb))
            then (True, lb, appCPS l' v k')
            else (False, lb, appCPS l' r' k')
    phi (Lam f) Nothing = lamExp where
        lamExp = (False, False, fn)
        fn = lam $ \x ->
            let (_, _, f') = f h' Nothing
                h' _ = (False, False, var x)
            in f'
    phi (Lam f) (Just v) = lamExp where
        lamExp = (True, False, res)
        h' _ = (False, False, v)
        (_, _, res) = f h' Nothing
    phi (Builtin b) _ = (False, True, builtin b)
    phi (Chr c) _ = (False, True, dot c)
    phi Promise _ = (False, False, d)

toCPS :: End Exp -> End Exp
toCPS b = cps where
    cps = cata phi b Nothing
    phi (App l r) Nothing = appExp where
        appExp = l (Just lk)
        lk = lam $ \k -> r (Just $ rk k)
        rk k = lam $ \l -> app (var k) (var l)
    phi (App l r) (Just k) = appExp where
        appExp = l (Just lk)
        lk = lam $ \l -> r (Just $ rk l)
        rk l = lam $ \m -> appCPS (var l) (var m) k
    phi (Lam f) Nothing = lamExp where
        lamExp = lam $ \x ->
            let f' = f h' Nothing
                h' (Just k) = app k $ var x
                h' Nothing = var x
            in f' 
    phi (Lam f) (Just l) = app l lamExp where
        lamExp = lam $ \x ->
            let f' = f h' Nothing
                h' (Just k) = app k (var x)
                h' Nothing = var x
            in f' 
    phi (Builtin b) Nothing = builtin b
    phi (Builtin b) (Just k) = app k $ builtin b
    phi (Chr c) Nothing = dot c
    phi (Chr c) (Just k) = app k $ dot c

computePromise :: End Exp -> End Exp
computePromise b = prom where
    (_, prom) = cata phi b (\_ -> i)
    phi (App l r) v = appExp where
        (lb, l') = l lf
        lf True = r'
        lf False = i
        (rb, r') = r v
        appVal = if lb then l' else app l' r'
        appExp = (rb, appVal)
    phi (Lam f) v = (False, fn) where
        fn = lam $ \x -> 
            let (_, f') = f h' v
                h' _ = (False, var x)
            in f'
    phi (Builtin b) v = (False, builtin b)
    phi Promise v = promExp where
        promExp = (True, lam $ \x -> app (v True) (var x))

