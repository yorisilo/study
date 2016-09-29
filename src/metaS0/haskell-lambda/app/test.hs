
foldr' :: (Int -> Int -> Int) -> Int -> [Int] -> Int
foldr' f z [] = z
foldr' f z (x:xs) = x `f` foldr' f z xs
