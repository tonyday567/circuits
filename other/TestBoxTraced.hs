module Main where
import BoxTraced

main :: IO ()
main = do
  putStrLn $ "liftP (*2) (Left 21) = "   ++ show test_liftP
  putStrLn $ "filterP even (Left 3) = "  ++ show test_filterP
  putStrLn $ "filterP even (Left 4) = "  ++ show test_filterP2
  putStrLn $ "compose (Left 5) = "        ++ show test_compose
  putStrLn $ "(,) Knot (Left (0,5)) = "  ++ show test_stateP
  xs <- test_queue
  putStrLn $ "queue [1..5] = "            ++ show xs
