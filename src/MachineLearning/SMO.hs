{-# LANGUAGE ImplicitParams, FlexibleContexts, NoMonomorphismRestriction, ScopedTypeVariables, BangPatterns, DoAndIfThenElse #-}
{-# OPTIONS_GHC -fspec-constr-count=16 -O2 #-}

module MachineLearning.SMO 
       (smo
        , SVM(..)
        , hypo
        )
       where
import Control.Applicative
import Control.Monad
import Control.Monad.ST
import Data.Array.MArray
import Data.Array.ST
import Data.Array
import Data.Ord
import Data.List
import Data.Maybe
import Data.STRef
import Control.Monad.Cont

f
  :: (?is::[Int],
      ?alpha::STUArray s Int Double,
      ?kMatrix::Array (Int, Int) Double,
      ?ys::Array Int Double,
      ?b::STRef s Double) =>
     Int -> ST s Double
f j = do
  b' <- readSTRef ?b
  vals <- forM ?is $ \i -> do 
    a <- (readArray ?alpha i)
    return $ a * (?ys ! i) * (?kMatrix ! (i,j))
  return $! sum vals - b'

-- prediction error
pError
  :: (?is::[Int],
      ?alpha::STUArray s Int Double,
      ?kMatrix::Array (Int, Int) Double,
      ?ys::Array Int Double,
      ?b::STRef s Double) =>
     Int -> ST s Double
pError i = subtract (?ys ! i) <$> f i

eps :: Double
eps = 1e-3
tol :: Double
tol = 1e-3

clip :: Ord a => a -> a -> a -> a
clip x lo hi = if x < lo then lo else if x > hi then hi else x

snap :: (Ord a, Fractional a) => a -> a -> a -> a
snap lo hi x = if x < lo+ 1e-8 then lo else if x > hi - 1e-8 then hi else x

sumAlphas
  :: (?is::[Int],
      ?alpha::STUArray s Int Double) =>
     ST s Double
sumAlphas = sum <$> (forM (?is) $ readArray ?alpha)

objective
  :: (?is::[Int],
      ?alpha::STUArray s Int Double,
      ?kMatrix::Array (Int, Int) Double,
      ?ys::Array Int Double) =>
     ST s Double
objective = do 
  salpha <- sumAlphas
  err <- sum <$> (forM (liftM2 (,) ?is ?is) $ \(i,j) -> do
    a1 <- readArray ?alpha i
    a2 <- readArray ?alpha j
    return $ a1 * a2 * (?ys ! i) * (?ys ! j) * (?kMatrix ! (i,j)))
  return $ salpha - (err / 2)

atBounds :: (?c::Double) => Double -> Bool
atBounds alph = (alph <= 0 + 1e-8) || (alph >= ?c - 1e-8)


getError
  :: (?is::[Int],
      ?alpha::STUArray s Int Double,
      ?c::Double,
      ?kMatrix::Array (Int, Int) Double,
      ?ys::Array Int Double,
      ?b::STRef s Double,
      ?errors::STUArray s Int Double) =>
     Int -> ST s Double
getError i = do
  a <- readArray ?alpha i
  if not $ atBounds a then 
    readArray ?errors i
    else 
      (subtract $ ?ys ! i) <$> f i 
    
withAlpha
  :: (?alpha :: STUArray s Int Double) =>
     Int 
     -> Double 
     -> ST s Double
     -> ST s Double
withAlpha j newaj action = do
  a <- readArray ?alpha j
  writeArray ?alpha j newaj
  ret <- action
  writeArray ?alpha j a
  return ret

takeStep
  :: (?b::STRef s Double,
      ?errors::STUArray s Int Double,
      ?ys::Array Int Double,
      ?kernel::a -> a -> Double,
      ?xs::Array Int a,
      ?c::Double,
      ?alpha::STUArray s Int Double,
      ?kMatrix :: Array (Int,Int) Double,
      ?is :: [Int]) =>
     Int -> Int -> ST s Bool
takeStep i j =   do
    let (y1,y2) = (?ys ! i, ?ys ! j)
    alpha1 <- ?alpha `readArray` i
    alpha2 <- ?alpha `readArray` j
    b <- readSTRef ?b
    e1 <- getError i
    e2 <- getError j
    let s = y1 * y2
    let lo = max 0 (if s > 0 then alpha1 + alpha2 - ?c else alpha2 - alpha1 ) :: Double
    let hi = min ?c (if s > 0 then alpha1 + alpha2 else ?c + alpha2 - alpha1 )
    let k11 = ?kMatrix ! (i,i)
    let k22 = ?kMatrix ! (j,j)
    let k12 = ?kMatrix ! (i,j)
    let eta = 2*k12 - k11 - k22
    if (abs(hi - lo) > eps) then do
        a2 <- snap 0 ?c <$> if eta < 0 then do
                let a2' = alpha2 - y2 * (e1 - e2) / eta
                return $ clip a2' lo hi
              else do
                 lobj <- withAlpha j lo objective
                 hobj <- withAlpha j hi objective
                 if (lobj > hobj + eps) then return lo
                   else if (lobj < hobj - eps)  then return hi
                     else return alpha2
        if abs(a2 - alpha2) >= eps*(a2+alpha2 + eps) then do
           let a1 = snap 0 ?c $ alpha1 + s*(alpha2-a2)
           writeArray ?alpha i a1
           writeArray ?alpha j a2
           let (b1 :: Double) = e1 + y1*(a1 - alpha1) * k11
                    + y2*(a2 - alpha2) * k12 + b
           let (b2 :: Double) = e2 + y1*(a1 - alpha1) * k12
                    + y2*(a2 - alpha2) * k22 + b
           let newB = if (not $ atBounds a1) then b1
                        else if( not $ atBounds a2) then b2
                           else (b1 + b2) / 2
           writeSTRef ?b newB
           writeArray ?errors i =<< if (atBounds a1) then pError i else return 0
           writeArray ?errors j =<< if (atBounds a2) then pError j else return 0
           forM_ ?is $ \k -> do
             alphk <- readArray ?alpha k
             unless (atBounds alphk || i == k || j == k) $ do
               e <- readArray ?errors k
               let newError = e + y1 * (a1 - alpha1) * (?kMatrix ! (i,k))
                              + y2 * (a2 - alpha2) * (?kMatrix ! (j,k))
                              - newB + b
               writeArray ?errors k newError
           return True
        else do
--           stTrace "step too small"
           return False
    else do
--     stTrace "hi == lo"
     return False


alphaCandidates
  :: (?c::Double,
      ?alpha:: STUArray s Int Double) =>
     ST s [Int]
alphaCandidates = do
  map fst . filter (not . atBounds . snd) <$> getAssocs ?alpha
  
sndChoice
  :: (?is::[Int],
      ?alpha::STUArray s Int Double,
      ?c::Double,
      ?kMatrix::Array (Int, Int) Double,
      ?ys::Array Int Double,
      ?b::STRef s Double,
      ?errors::STUArray s Int Double) =>
     Double -> [Int] -> ST s Int
sndChoice e1 candidates = do
  err <- forM candidates $ \i -> do
     e2 <- getError i 
     return (i,e2)
  return . fst $ maximumBy (comparing $ abs . (subtract e1) . snd ) err
  
-- randomized list = do
--   let l = length list
--   r <- unsafeIOToST $ randomRIO (0,l-1)
--   return . (uncurry . flip $ (++)) $ splitAt r list


randomized list = return list

atLeast2 :: [t] -> Bool
atLeast2 (_:_:_) = True
atLeast2 _ = False

examineExample
  :: (?errors::STUArray s Int Double,
      ?b::STRef s Double,
      ?ys::Array Int Double,
      ?kernel::a -> a -> Double,
      ?kMatrix :: Array (Int,Int) Double,
      ?xs::Array Int a,
      ?c::Double,
      ?alpha::STUArray s Int Double,
      ?is :: [Int] ) =>
     Int -> ST s Int
examineExample j = flip runContT return $ callCC $ \creturn -> do
    let y2 = ?ys ! j
    alpha2 <- lift $ ?alpha  `readArray` j
    e2 <- lift $ getError j
    let r2 = e2 * y2 
    candidates <- lift $ filter (/= j) <$> alphaCandidates
    unless ((r2 < (negate tol) && alpha2 < ?c) || (r2 > tol && alpha2 > 0 )) $
      creturn 0
    when (atLeast2 candidates) $ do
        i <- lift $ sndChoice e2 candidates
        res <- lift $ takeStep i j
        when res $ creturn 1
    candidates' <- lift $ randomized candidates 
    forM_ candidates' $ \i -> do
      res <- lift $ takeStep i j
      when res $ creturn 1
    alpha' <- lift $ randomized ?is
    forM_ alpha' $ \i -> unless (i==j) $ do
      res <- lift $ takeStep i j
      when res $ creturn 1
    return 0
    
while :: Monad m => m Bool -> m a -> m ()
while p a = p >>= \p' -> if p' then a >> while p a else return ()

data SVM a = SVM {
    kern :: a -> a -> Double
  ,  sv :: [(a,Double,Double)] -- support vectors
  , threshold :: !Double
  , numRounds :: Integer
  }

smo  :: Double
     -> Array Int a
     -> Array Int Double
     -> (a -> a -> Double)
     -> SVM a
smo c xs ys kernel = runST $ do 
  let l@(startx,endx) = bounds xs
  let is = range l
  let ?is = is
  let ?xs = xs
  let ?ys = ys
  alpha <- newArray l 0
  let ?alpha = alpha
  errors <- newArray l 0
  let ?errors = errors
  let ?c = c
  b <- newSTRef 0
  let ?b = b
  let ?kernel = kernel
  let ?kMatrix = array ((startx,startx),(endx,endx)) $
        [((i,j),kernel (xs ! i) (xs ! j)) | i <- is, j <- is]
  forM_ is $ \i -> (subtract (ys ! i)) <$>  f i  >>= writeArray errors i
  numChanged <- newSTRef (0 :: Int)
  examineAll <- newSTRef True
  count <- newSTRef 0
  while (do
            ea <- readSTRef examineAll            
            nc <- readSTRef numChanged 
            return $ nc > 0 || ea)$ do
      cnt <- readSTRef count 
      writeSTRef count $ cnt + 1 
      ea <- readSTRef examineAll
      candidates <- if ea then return is
                     else alphaCandidates
      nc' <- forM candidates examineExample
      let nc = sum nc'
      writeSTRef numChanged nc
      writeSTRef examineAll (if ea then False else nc > 0 )
  rounds <- readSTRef count
  b' <- readSTRef b
  svs <- catMaybes <$> (forM is $ \i -> do
    a <- readArray alpha i
    if a > 0 then return $ Just (xs ! i, ys ! i, a)
    else return Nothing)
  return $ SVM kernel svs b' rounds

g :: Double -> Double
g z = if z >= 0 then 1 else -1

hypo :: SVM a -> a -> Double
hypo svm x = g $ sum [alphai * yi * kern svm x xi | (xi, yi, alphai) <- sv svm] 
                    - threshold svm
