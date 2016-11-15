module ScaledBinary (
    ScaledBinary,
    divideWithBinaryScale,
    toScaledBinary
) where
import Scaled
import Char (isSpace, isDigit)
import Ratio (numerator, denominator, (%))

data ScaledBinary = SB !Integer !Int
approx :: Integer -> Int -> ScaledBinary

approx n s = SB n s -- may be redefined by an implementation
common_scale :: ScaledBinary -> ScaledBinary ->
                (Integer, Integer, Int)

common_scale (SB nx sx) (SB ny sy)
  | sx > sy = (nx, ny * 2^(sx-sy), sx)
  | sx < sy = (nx * 2^(sy-sx), ny, sy)
  | True    = (nx,              ny, sx)

instance Scaled ScaledBinary where
  scale (SB _ s) = s
  ratio x y = ratio nx ny where (nx,ny,_) = common_scale x y

toScaledBinary :: Real a => a -> Int -> ScaledBinary

toScaledBinary x s =
  approx (round (toRational x * 2^s)) s
instance Eq ScaledBinary where
  x == y = nx == ny
    where (nx,ny,_) = common_scale x y
instance Ord ScaledBinary where
  compare x y = compare nx ny
    where (nx,ny,_) = common_scale x y
instance Num ScaledBinary where
  negate (SB n s) = SB (negate n) s
  abs    (SB n s) = SB (abs n)    s
  signum (SB n _) = SB (signum n) 0
  fromInteger i   = approx i 0

  x + y = approx (nx+ny) s where (nx,ny,s) = common_scale x y
  x - y = approx (nx-ny) s where (nx,ny,s) = common_scale x y
  (SB nx sx) * (SB ny sy) = approx (nx*ny) (sx+sy)
instance Real ScaledBinary where
  toRational (SB n s) = n % 2^s
round_to_integer (SB n s) =
  (n * 2 + signum n) `quot` 2 ^ (s + 1)

instance Enum ScaledBinary where
  succ (SB n s) = approx (succ n) s
  pred (SB n s) = approx (pred n) s
  toEnum i      = approx (fromIntegral i) 0
  fromEnum x    = fromIntegral (round_to_integer x) -- bogus

  enumFrom       x     = x : enumFrom (succ x)
  enumFromThen   x y   = loop x (y-x)
                         where loop x d = x : loop (x+d) d
  enumFromTo     x   z = if x > z then [] else x : enumFromTo (succ x) z
  enumFromThenTo x y z = loop x (y-x)
                         where loop x d = if x > z then []
                                          else x : loop (x+d) d
instance Integral ScaledBinary where
  toInteger x = round_to_integer x
  quotRem x y = (SB q 0, SB r s)
                where (nx, ny, s) = common_scale x y
                      (q, r)      = quotRem nx ny
  divMod x y  = (SB q 0, SB r s)
                where (nx, ny, s) = common_scale x y
                      (q, r)      = divMod nx ny
divideWithBinaryScale x y s = toScaledBinary (ratio x y) s

defaultDivisionScale = 60

instance Fractional ScaledBinary where
  x / y = divideWithBinaryScale x y
            (scale x `max` scale y `max` defaultDivisionScale)

  recip y = 1 / y

  fromRational x = find_scale (numerator x) (denominator x) 0
    where find_scale n 1 s = approx n s
          find_scale n d s =
              if d`mod`2 == 0 then find_scale n (d`div`2) (s+1) else
              error "ScaledBinary.fromRational: not a binary number"
instance RealFrac ScaledBinary where
  properFraction (SB n s) = (fromIntegral q, SB r s)
                            where (q,r) = quotRem n (2^s)
  truncate (SB n s) = fromIntegral (n `quot` 2^s)
  floor    (SB n s) = fromIntegral (n `div`  2^s)
  ceiling  (SB n s) = fromIntegral (negate (negate n `div` 2^s))
  round    (SB n s) = fromIntegral (
    if s == 0 then n else
    (if n >= 0 then n + 2^(s-1) else n - 2^(s-1)) `quot` 2^s)

--- Show and Read do not work properly.

-- Not quite right.

instance Show ScaledBinary where
  showsPrec p (SB n s) suffix
    | n < 0 && p > 6 = "(-" ++ showAbs (abs n) s (")" ++ suffix)
    | n < 0          =  "-" ++ showAbs (abs n) s         suffix
    | True           =         showAbs      n  s         suffix
    where showAbs n s suffix
            | s <= 0 = shows n suffix
            | True = take (n1-s) d1 ++ "." ++ drop (n1-s) d1 ++ suffix
            where d0  = show (n * (5 ^ s))
                  n0 = length d0
                  d1 = if n0 > s then d0 else
                       replicate (s+1-n0) '0' ++ d0
                  n1 = length d1

instance Read ScaledBinary where
  readsPrec _ cs = parse cs
    where parse  :: String ->                           [(ScaledBinary,String)]
          before :: String -> Integer -> Bool ->        [(ScaledBinary,String)]
          after  :: String -> Integer -> Bool -> Int -> [(ScaledBinary,String)]
          decbin :: Integer -> Int -> ScaledBinary

          parse ( c:cs) | isSpace c = parse cs
          parse ('+':cs) = before cs 0 False
          parse ('-':cs) = before cs 0 True
          parse      cs  = before cs 0 False

          before ( c :cs) n neg | isDigit c =
            before cs (n*10 + val c) neg
          before ('.':cs) n neg =
            after cs n neg 0
          before      cs  n neg =
            [(approx (if neg then negate n else n) 0, cs)]

          after (c:cs) n neg s | isDigit c =
            after cs (n*10 + val c) neg (s+1)
          after cs     n neg s =
            [(decbin (if neg then negate n else n) s, cs)]

          -- converting decimal to binary, divide by 10^n and then
          -- multiply by 2^ceiling(10n/3), then round
          decbin n s = approx n' s'
            where s' = ceiling (s * 10 % 3)
                  n' = round ((n * 2^s') % (10^s))

          val c = fromIntegral (fromEnum c - fromEnum '0')
