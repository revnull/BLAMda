{-# LANGUAGE RankNTypes, TemplateHaskell #-}

module Unlambda (compileFile) where

import Profunctor
import Control.Monad.Error
import Data.Maybe
import Data.Char
import Unsafe.Coerce
import qualified Data.Set as S
import qualified Data.Map as M
import Language.Haskell.TH (stringE, runIO)

core = $( stringE <=< runIO $ readFile "unlambda_core.c" )

data ExpF a b =
    App b b
  | AppCPS b b b 
  | Lam Bool (a -> b)
  | Frag (String -> String) (String -> String) (String -> String) b
    -- Frag identifier builder content
  | Noop
  | Promise

instance Profunctor ExpF where
    dimap f g (App x y) = App (g x) (g y)
    dimap f g (AppCPS x y k) = AppCPS (g x) (g y) (g k)
    dimap f g (Lam b h) = Lam b (g . h . f)
    dimap f g (Frag i b c x) = Frag i b c (g x)
    dimap f g Noop = Noop
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
lam f = Roll (Lam False f)

blam :: (a -> Exp a b) -> Exp a b
blam f = Roll (Lam True f)

app :: Exp a b -> Exp a b -> Exp a b
app x y = Roll (App x y)

appCPS :: Exp a b -> Exp a b -> Exp a b -> Exp a b
appCPS x y k = Roll (AppCPS x y k)

var :: b -> Exp a b
var = return

noop :: End Exp
noop = Roll Noop

builtin :: String -> End Exp
builtin s = Roll $ Frag (showString s) id id noop

dot :: Char -> End Exp
dot c = blam $ \x -> Roll $ Frag id putc id (var x)
  where putc = showString "putchar(" . shows c . showString ");"

k :: End Exp
k = lam $ \x -> lam $ \y -> var x

s :: End Exp
s = lam $ \x -> lam $ \y -> lam $ \z -> 
    app (app (var x) (var z)) (app (var y) (var z))

i :: End Exp
i = lam $ \x -> var x

v :: End Exp
v = lam $ \_ -> builtin "&v"

d :: End Exp
d = Roll $ Promise

callcc :: End Exp
callcc = blam $ \x -> Roll $ Frag id (showString fr) id noop where
    fr = "ALLOC_F(c,1);c->fn=cc;c->data[0]=cont;input->fn(input,c,cont);"

type End p = forall x. p x x

iter0 :: Profunctor p => (p a a -> a) -> End (Rec p) -> a
iter0 phi x = cata phi x

dump :: End Exp -> String
dump b = cata phi b vars "" where
    phi (App f g) xs = showString "(" . f xs . showString ") (" .
        g xs . showString ")"
    phi (AppCPS f g k) xs = showChar '(' . f xs . showString ") (" .
        g xs . showString ") $ ( " . k xs . showChar ')'
    phi (Lam b h) (x:xs) = ls where
        ls = if b then showChar '#' . base . showChar '#' else base
        base = showChar '\\' . showString x . showString " -> " .
            h (const (showString x)) xs
--    phi (Chr c) xs = showChar '.' . showChar c . showChar ' '
--    phi (Builtin b) xs = showChar '&' . showString b
    phi (Frag i b c s) xs = showString "#(" . i . showChar ',' . b .
        showChar ',' . c . showString ")#" . s xs
    phi Noop _ = id
    phi Promise _ = showString "{PROMISE}"
    strs = fmap (:[]) ['a'..'z']
    vars = strs ++ zipWith (++) (cycle strs) vars

compileBuiltins = foldr (.) id bic where
    bic = map comp bi
    comp (name, exp) = toC name $ optimize $ toCPS (unsafeCoerce exp)
    bi = [("s",s), ("i",i), ("k", k), ("v", v)]

toFrag :: String -> End Exp -> ExpF () ()
toFrag name b = Frag fi fb fc () where
    (Frag fi fb fc _, _) = cata phi b 0 False M.empty vars
    vars = (showString name):(fmap ((showString name .) . shows) [0..])
    ref = (showChar '&' .)

    phi (App l r) 0 top vs (appId:xs) = appExp where
        (Frag li lb lc _, xs') = l 0 False vs xs 
        (Frag ri rb rc _, xs'') = r 0 False vs xs'
        appStr = lc . rc . lb . rb . showString "closure " . appId .
            showString "= {&root,0,apply,2,{" . li . showChar ',' .
            ri . showString "}};\n"
        appExp = (Frag (ref appId) id appStr S.empty, xs'')

    phi (App l r) d top vs (appId:xs) = appExp where
        (Frag li lb lc lv, xs') = l d False vs xs 
        (Frag ri rb rc rv, xs'') = r d False vs xs'
        appStr = lb . rb . li . showString "->fn(" . li . showChar ',' .
            ri . showString ",cont);";
        vs' = S.union lv rv
        appExp = (Frag appId appStr (lc . rc) vs', xs'')

    phi (AppCPS l r k) d top vs (appId:xs) = appExp where
        (Frag li lb lc lv, xs') = l d False vs xs 
        (Frag ri rb rc rv, xs'') = r d False vs xs'
        (Frag ki kb kc kv, xs''') = k d False vs xs''
        appStr = lb . rb . kb . 
            showString "ALLOC_F(c,2);c->fn=compose;c->data[0]=" . ki .
            showString ";c->data[1]=cont;" . li . showString "->fn(" . li .
            showChar ',' . ri . showString ",c);"
        vs' = S.union kv $ S.union lv rv 
        appExp = (Frag appId appStr (lc . rc . kc) vs', xs''')

    phi (Lam _ h) d top vs (fnId:xs) = lamExp where
        hf d' top vs' xs = (Frag v ev id vs'', xs) where
            (v,vs'') = if d == d' - 1
                then (showString "input", S.empty)
                else (showString "self->data[" . shows w . showChar ']',
                    S.singleton d)
            ev = if top
                then showString "eval(" . v . showString ",cont);"
                else id
            w = fromJust $ M.lookup d vs'
        vs' = if S.member d hv
            then M.insert d (-1) vs''
            else vs''
        vs'' = M.fromList $ zip (takeWhile (< d) $ S.toAscList hv) [0..]
        (Frag hi hb hc hv, xs') = h hf (d + 1) True vs' xs
        fnname = showChar 'l' . fnId
        proto = showString "void " . fnname . 
            showString "(closure *self, closure *input, closure *cont);"
        fn = showString "void " . fnname . 
            showString "(closure *self, closure *input, closure *cont) {\n" .
            hb . showString "}\n"
        clos = showString "closure " . fnId .
            showString "={&root,0," . fnname . showString ",0};\n"
        frag = showString "ALLOC_F(" . fnId . showChar ',' . shows (M.size vs'') .
            showString ");" . fnId . showString "->fn=" . fnname .
            showString ";" . copyvars . callFrag
        callFrag = if top
            then showString "eval(" . fnId . showString ",cont);"
            else id
        copyvars = foldr (.) id $ do
            i <- [0..d-1]
            (Just sb) <- return $ M.lookup i vs
            (Just xb) <- return $ M.lookup i vs'
            let bind = if (sb < 0)
                    then showString "input;"
                    else showString "self->data[" . shows sb . showString "];"
            return $ fnId . showString "->data[" . shows xb . showString "]=" .
                bind
        fnC = hc . proto . fn
        lamExp = if d == 0
            then (Frag (ref fnId) id (fnC . clos) hv, xs')
            else (Frag fnId frag fnC hv, xs')

    phi (Frag i b c l) d top vs xs = fragExp where
        (Frag li lb lc lv, xs') = l d top vs xs 
        fragExp = (Frag (i . li) (b . lb) (c . lc) lv, xs')

    phi Noop _ _ _ xs = (Frag id id id S.empty, xs)

toC :: String -> End Exp -> String -> String
toC n b = frag where
    (Frag _ _ frag _) = toFrag n b

toCValue :: End Exp -> String
toCValue b = include . compileBuiltins . c . main $ "" where
    include = showString core
    c = toC "p" b
    main = showString "int main() { initialize(&p,&ex);}\n"

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
compile' c ('c':xs) = fmap (callcc:) $ compile' (c + 1) xs
compile' c ('r':xs) = fmap ((dot '\n'):) $ compile' (c + 1) xs
compile' c ['.'] = Left $ ". failed at character " ++ show c
compile' c ('.':x:xs) = fmap ((dot x):) $
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
    phi (Lam True f) _ = lamExp where
        lamExp = (False, True, fn)
        fn = blam $ \x ->
            let (_, _, f') = f h' Nothing
                h' _ = (False, False, var x)
            in f'
    phi (Lam _ f) Nothing = lamExp where
        lamExp = (False, False, fn)
        fn = lam $ \x ->
            let (_, _, f') = f h' Nothing
                h' _ = (False, False, var x)
            in f'
    phi (Lam _ f) (Just v) = lamExp where
        lamExp = (True, False, res)
        h' _ = (False, False, v)
        (_, _, res) = f h' Nothing
    phi Noop (Just v) = (True, False, v)
    phi Noop _ = (False, False, noop)
    phi (Frag i b c l) _ = (False, True, frag) where
        (_, _, l') = l Nothing
        frag = Roll $ Frag i b c l'
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
    phi (Lam b f) Nothing = lamExp where
        lf = if b then blam else lam
        lamExp = lf $ \x ->
            let f' = f h' Nothing
                h' (Just k) = app k $ var x
                h' Nothing = var x
            in f' 
    phi (Lam b f) (Just l) = app l lamExp where
        lf = if b then blam else lam
        lamExp = lf $ \x ->
            let f' = f h' Nothing
                h' (Just k) = app k (var x)
                h' Nothing = var x
            in f' 
    phi (Frag i c b l) v = Roll $ Frag i c b l' where
        l' = l v
    phi Noop Nothing = noop
    phi Noop (Just v) = v

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
    phi (Lam b f) v = (False, fn) where
        lf = if b then blam else lam
        fn = lf $ \x -> 
            let (_, f') = f h' v
                h' _ = (False, var x)
            in f'
    phi Promise v = promExp where
        promExp = (True, blam $ \x -> app (v True) (var x))
    phi Noop _ = (False, noop)
    phi (Frag i b c l) v = (lb, frag) where
        (lb, l') = l v
        frag = Roll $ Frag i b c l'

