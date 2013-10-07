module Main
    ( main ) where

import qualified Control.Monad as Monad
import           Control.Monad.State.Lazy (State)
import qualified Control.Monad.State.Lazy as State
import           Control.Monad.Unicode ((≫=), (≫))
import           Data.Conduit (($$), ($=), runResourceT)
import           Data.Conduit.Binary (sourceFile)
import qualified Data.Conduit.List as CL
import           Data.Conduit.Text as CT
import           Data.Function.Unicode ((∘))
import           Data.Functor (fmap)
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (Maybe(Just, Nothing), catMaybes, maybe)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Tuple (swap)
import           Prelude (Bool(False), Eq, Int, Show, (&&), ($), (++), (+), (-), (>), compare, error, flip, id, min, max, not, show, uncurry)
import           Prelude.Unicode ((≠))
import           System.Environment (getArgs)
import           System.IO (IO, putStrLn)

type Candidate = Int
type CandidateName = Text
type Votes = Int
data Ballot a = Ballot { unBallot ∷ [a] } deriving (Eq, Show)

main ∷ IO ()
main = do
    args ← getArgs
    let [inPath] = args

    ballots ← runResourceT $ sourceFile inPath $= CT.decode CT.utf8 $= CT.lines $= CL.map parseBallot $$ CL.consume
    putStrLn $ show (List.length ballots) ++ " ballots."
    -- Monad.mapM_ (putStrLn ∘ show) ballots

    let candidates = Set.toAscList $ List.foldl' f Set.empty ballots
            where f s (Ballot r) = s `Set.union` Set.fromList r
    putStrLn $ show (List.length candidates) ++ " candidates:"
    Monad.mapM_ (putStrLn ∘ Text.unpack) candidates

    let candidates' = [1 .. List.length candidates]
        ballots' = List.map (Ballot ∘ List.map (m Map.!) ∘ unBallot) ballots
            where m = Map.fromList $ candidates `List.zip` candidates'

    let
        dumpTable ∷ Show a ⇒ Map (Candidate, Candidate) a → IO ()
        dumpTable t = do
            putStrLn $ "\t" ++ (List.intercalate "\t" $ List.map Text.unpack candidates)
            Monad.forM_ (List.zip candidates candidates') $ \ (rowName, row) → do
                putStrLn $ List.intercalate "\t" $ (Text.unpack rowName :) $ List.map (maybe "" show ∘ flip Map.lookup t ∘ (,) row) candidates'

    let votes = computeVotes ballots'
    putStrLn "Votes:"
    dumpTable votes

    let strongestPaths = computeStrongestPaths candidates' votes
    putStrLn "Strongest paths:"
    dumpTable strongestPaths

    let cmp i j = compare (strongestPaths Map.! (j, i)) (strongestPaths Map.! (i, j))
        sorted = List.sortBy cmp candidates'
    putStrLn "Sorted:"
    Monad.mapM_ (putStrLn ∘ Text.unpack ∘ (candidates List.!!) ∘ (flip (-) 1)) sorted

computeVotes ∷ [Ballot Candidate] → Map (Candidate, Candidate) Votes
computeVotes [] = Map.empty
computeVotes ((Ballot r):bs) = Map.unionWith (+) (computeVotes bs) $ Map.fromList $ toPairs r
    where
        toPairs ∷ [a] → [((a,a), Int)]
        toPairs (c:cs) = List.foldl (\ tl d → ((c,d), 1) : tl) (toPairs cs) cs
        toPairs _ = []

type SPMemo = State (Map ([Candidate], (Candidate, Candidate)) (Maybe Votes))
computeStrongestPaths ∷ [Candidate] → Map (Candidate, Candidate) Votes → Map (Candidate, Candidate) Votes
computeStrongestPaths candidates votes =
    Map.fromList $ catMaybes $ flip State.evalState Map.empty $ Monad.mapM (\ e → (fmap∘fmap) (e,) $ sp candidates e) edges
    where
        edges ∷ [(Candidate, Candidate)]
        edges = [(i,j) | i ← candidates, j ← candidates, i ≠ j]

        sp ∷ [Candidate] → (Candidate, Candidate) → SPMemo (Maybe Votes)
        sp cs edge =
            let k = (cs, edge)
            in State.gets (Map.lookup (cs, edge)) ≫= \ case
                Just memoed →                                                          Monad.return memoed
                _           → sp' cs edge ≫= \ res → State.modify (Map.insert k res) ≫ Monad.return res

        sp' ∷ [Candidate] → (Candidate, Candidate) → SPMemo (Maybe Votes)
        sp'    []  edge                   = case (Map.lookup edge votes, Map.lookup (swap edge) votes) of
                                                (Just for, Just against) | for > against → Monad.return $ Just for
                                                _                                        → Monad.return $ Nothing
        sp' (c:cs) (i,j) | c ≠ i && c ≠ j = do direct ← sp cs (i,j)
                                               viaC1  ← sp cs (i,c)
                                               viaC2  ← sp cs (c,j)
                                               Monad.return $ inMaybe max direct $ Monad.liftM2 min viaC1 viaC2
        sp' (_:cs) edge                   = sp cs edge

        inMaybe ∷ (a → a → a) → Maybe a → Maybe a → Maybe a
        inMaybe f a b = Monad.liftM2 f a b `Monad.mplus` a `Monad.mplus` b

parseBallot ∷ Text → Ballot CandidateName
parseBallot = Ballot ∘ List.drop 1 ∘ Text.splitOn "\t"
