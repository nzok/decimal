module ScaledDecimal (
    ScaledDecimal,
    divideWithScale,
    toScaledDecimal
) where
import Scaled
import Char (isSpace, isDigit)
import Ratio (numerator, denominator, (%))
data ScaledDecimal = SD !Integer !Int
approx :: Integer -> Int -> ScaledDecimal

approx n s = SD n s -- may be redefined by an implementation
common_scale :: ScaledDecimal -> ScaledDecimal ->
                (Integer, Integer, Int)

common_scale (SD nx sx) (SD ny sy)
  | sx > sy = (nx, ny * 10^(sx-sy), sx)
  | sx < sy = (nx * 10^(sy-sx), ny, sy)
  | True    = (nx,              ny, sx)
instance Scaled ScaledDecimal where
  scale (SD _ s) = s
  ratio x y = ratio nx ny where (nx,ny,_) = common_scale x y
toScaledDecimal :: Real a => a -> Int -> ScaledDecimal

toScaledDecimal x s =
  approx (round (toRational x * 10^s)) s
instance Eq ScaledDecimal where
  x == y = nx == ny
    where (nx,ny,_) = common_scale x y
instance Ord ScaledDecimal where
  compare x y = compare nx ny
    where (nx,ny,_) = common_scale x y
instance Num ScaledDecimal where
  negate (SD n s) = SD (negate n) s
  abs    (SD n s) = SD (abs n)    s
  signum (SD n _) = SD (signum n) 0
  fromInteger i   = approx i 0

  x + y = approx (nx+ny) s where (nx,ny,s) = common_scale x y
  x - y = approx (nx-ny) s where (nx,ny,s) = common_scale x y
  (SD nx sx) * (SD ny sy) = approx (nx*ny) (sx+sy)
instance Real ScaledDecimal where
  toRational (SD n s) = n % 10^s
round_to_integer (SD n s) =
  (n * 10 + signum n * 5) `quot` 10 ^ (s + 1)

instance Enum ScaledDecimal where
  succ (SD n s) = approx (succ n) s
  pred (SD n s) = approx (pred n) s
  toEnum i      = approx (fromIntegral i) 0
  fromEnum x    = fromIntegral (round_to_integer x) -- bogus

  enumFrom       x     = x : enumFrom (succ x)
  enumFromThen   x y   = loop x (y-x)
                         where loop x d = x : loop (x+d) d
  enumFromTo     x   z = if x > z then [] else x : enumFromTo (succ x) z
  enumFromThenTo x y z = loop x (y-x)
                         where loop x d = if x > z then []
                                          else x : loop (x+d) d
instance Integral ScaledDecimal where
  toInteger x = round_to_integer x
  quotRem x y = (SD q 0, SD r s)
                where (nx, ny, s) = common_scale x y
                      (q, r)      = quotRem nx ny
  divMod x y  = (SD q 0, SD r s)
                where (nx, ny, s) = common_scale x y
                      (q, r)      = divMod nx ny
divideWithScale x y s = toScaledDecimal (ratio x y) s

defaultDivisionScale = 18

instance Fractional ScaledDecimal where
  x / y = divideWithScale x y
            (scale x `max` scale y `max` defaultDivisionScale)

  recip y = 1 / y

  fromRational x = find_scale (numerator x) (denominator x) 0
    where find_scale n 1 s = approx n s
          find_scale n d s =
              if d`mod`10 == 0 then find_scale n     (d`div`10) (s+1) else
              if d`mod` 2 == 0 then find_scale (n*5) (d`div` 2) (s+1) else
              if d`mod` 5 == 0 then find_scale (n*2) (d`div` 5) (s+1) else
              error "ScaledDecimal.fromRational: not a decimal number"
instance RealFrac ScaledDecimal where
  properFraction (SD n s) = (fromIntegral q, SD r s)
                            where (q,r) = quotRem n (10^s)
  truncate (SD n s) = fromIntegral (n `quot` 10^s)
  floor    (SD n s) = fromIntegral (n `div`  10^s)
  ceiling  (SD n s) = fromIntegral (negate (negate n `div` 10^s))
  round    (SD n s) = fromIntegral (
    if s == 0 then n else
    (if n >= 0 then n + 5*10^(s-1) else n - 5*10^(s-1)) `quot` 10^s)
instance Show ScaledDecimal where
  showsPrec p (SD n s) suffix
    | n < 0 && p > 6 = "(-" ++ showAbs (abs n) s (")" ++ suffix)
    | n < 0          =  "-" ++ showAbs (abs n) s suffix
    | True           =         showAbs      n  s suffix
    where showAbs n s suffix
            | s <= 0 = shows n suffix
            | True = take (n1-s) d1 ++ "." ++ drop (n1-s) d1 ++ suffix
            where d0  = show n
                  n0 = length d0
                  d1 = replicate (s+1-n0) '0' ++ d0
                  n1 = length d1

instance Read ScaledDecimal where
  readsPrec _ cs = parse cs
    where parse ( c:cs) | isSpace c = parse cs
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
            [(approx (if neg then negate n else n) s, cs)]

          val c = fromIntegral (fromEnum c - fromEnum '0')
