{-# LANGUAGE ViewPatterns #-}

data Client = GovOrg String
            | Company String Integer String
            | Individual String Bool
            deriving Show

clientName :: Client -> String
clientName client = case client of
                      GovOrg name -> name
                      Company name id resp -> name
                      Individual name ads -> name

responsibility :: Client -> String
responsibility (Company _ _ r) = r
responsibility _ = "Unknown"

specialClient :: Client -> Bool
specialClient (clientName -> "Schemer") = True
specialClient (responsibility -> "CEO") = True
specialClient _                         = False

main :: IO ()
main = putStrLn (show (specialClient (Individual "Schemer" False)))
