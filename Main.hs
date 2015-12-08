module Main
    ( main ) where

import           Control.Arrow (first)
import qualified Control.Monad as Monad
import           Control.Monad.State.Lazy (State)
import qualified Control.Monad.State.Lazy as State
import           Control.Monad.Trans.Resource (runResourceT)
import           Control.Monad.Unicode ((≫=), (≫))
import           Data.Bool (not)
import           Data.Bool.Unicode ((∧))
import           Data.Conduit (($$), ($=))
import           Data.Conduit.Binary (sourceFile)
import qualified Data.Conduit.List as CL
import           Data.Conduit.Text as CT
import           Data.Either (Either(Left, Right), partitionEithers)
import           Data.Eq (Eq)
import           Data.Eq.Unicode ((≢))
import           Data.Function (($), flip)
import           Data.Function.Unicode ((∘))
import           Data.Functor (fmap)
import           Data.Int (Int)
import qualified Data.List as List
import           Data.List ((!!))
import           Data.List.Unicode ((⧺))
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe (Maybe(Just, Nothing), catMaybes, fromMaybe, maybe)
import           Data.Monoid (mconcat)
import           Data.Ord (Ord, compare)
import           Data.Ord.Unicode ((≤), (≥))
import qualified Data.Set as Set
import           Data.String (String)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Tuple (snd, swap)
import           Prelude ((+), (-), error, min, max, maxBound)
import           System.Environment (getArgs)
import           System.IO (IO, putStrLn)
import           Text.Read (readEither)
import           Text.Show (Show, show)

type Candidate = Int
type Match     = (Candidate, Candidate)
type Votes     = Int
type Strength  = Int
data Ballot a  = Ballot { unBallot ∷ Map a Int } deriving (Eq, Show)
data VoteLine  = VoteLine Text Text Int

(!) ∷ (Ord k, Show a, Show k) ⇒ Map k a → k → a
m ! k | Just v ← Map.lookup k m = v
m ! k = error $ "key " ⧺ show k ⧺ " not found in:\n" ⧺ show m

main ∷ IO ()
main = do
    args ← getArgs
    let [inPath] = args

    (errors, ballotMaterial) ← fmap (first mconcat ∘ partitionEithers) $ runResourceT $ sourceFile inPath $= CT.decode CT.utf8 $= CT.lines $= CL.map parseVote $$ CL.consume
    Monad.when (not $ List.null errors) $ Monad.fail $ show errors
    let
        makeBallot (VoteLine voter candidate ranking) = Map.singleton voter $ Map.singleton candidate ranking
        providedBallots = Map.elems $ Map.unionsWith Map.union $ List.map makeBallot ballotMaterial
        candidates = Set.toAscList $ List.foldl' f Set.empty providedBallots
            where f s r = s `Set.union` Set.fromList (Map.keys r)
        defaultBallot = Map.fromList $ List.map (, maxBound ∷ Int) candidates
        completeBallot = flip Map.union defaultBallot
        ballots = List.map Ballot $ List.map completeBallot providedBallots

    putStrLn $ show (List.length ballots) ⧺ " ballots."
    -- Monad.mapM_ (putStrLn ∘ show) ballots

    putStrLn $ show (List.length candidates) ⧺ " candidates:"
    Monad.mapM_ (putStrLn ∘ Text.unpack) candidates

    let candidates' = [1 .. List.length candidates]
        ballots' = List.map (Ballot ∘ Map.mapKeys (m !) ∘ unBallot) ballots
            where m = Map.fromList $ candidates `List.zip` candidates'

    let
        dumpTable ∷ Show a ⇒ Map Match a → IO ()
        dumpTable t = do
            putStrLn $ "For ⬇ Against ➡\t" ⧺ (List.intercalate "\t" $ List.map Text.unpack candidates)
            Monad.forM_ (List.zip candidates candidates') $ \ (rowName, row) → do
                putStrLn $ List.intercalate "\t" $ (Text.unpack rowName :) $ List.map (maybe "" show ∘ flip Map.lookup t ∘ (,) row) candidates'

    let votes = computeVotes ballots'
    putStrLn "Votes:"
    dumpTable votes

    let strongestPaths = computeStrongestPaths candidates' votes
    putStrLn "Strongest paths:"
    dumpTable strongestPaths

    let cmp i j =
            let against = fromMaybe 0 $ Map.lookup (j,i) strongestPaths
                for     = fromMaybe 0 $ Map.lookup (i,j) strongestPaths
            in compare against for
        sorted = List.sortBy cmp candidates'
    putStrLn "Sorted:"
    Monad.mapM_ (putStrLn ∘ Text.unpack ∘ (candidates !!) ∘ (flip (-) 1)) sorted

computeVotes ∷ [Ballot Candidate] → Map Match Votes
computeVotes [] = Map.empty
computeVotes ((Ballot ranking):bs) = Map.unionWith (+) (computeVotes bs) $ Map.fromList $ toPairs $ List.sortBy (\ (_,l) (_,r) → compare l r) $ Map.toList ranking
    where
        toPairs ∷ [(Candidate, Int)] → [(Match, Int)]
        toPairs ((c,r):cs) = List.foldl (\ tl (c',_) → ((c,c'), 1) : tl) (toPairs cs) $ List.dropWhile ((≤ r) ∘ snd) cs
        toPairs _ = []

type SPMemo = State (Map ([Candidate], Match) (Maybe Votes))
computeStrongestPaths ∷ [Candidate] → Map Match Votes → Map Match Strength
computeStrongestPaths candidates votes =
    Map.fromList $ catMaybes $ flip State.evalState Map.empty $ Monad.mapM (\ e → (fmap∘fmap) (e,) $ sp candidates e) edges
    where
        edges ∷ [Match]
        edges = [(i,j) | i ← candidates, j ← candidates, i ≢ j]

        sp ∷ [Candidate] → Match → SPMemo (Maybe Strength)
        sp cs edge =
            let k = (cs, edge)
            in State.gets (Map.lookup (cs, edge)) ≫= \ case
                Just memoed →                                                          Monad.return memoed
                _           → sp' cs edge ≫= \ res → State.modify (Map.insert k res) ≫ Monad.return res

        sp' ∷ [Candidate] → Match → SPMemo (Maybe Strength)
        sp'    []  edge                   = case (Map.lookup edge votes, Map.lookup (swap edge) votes) of
                                                (Just for, Just against) | for ≥ against → Monad.return $ Just for
                                                _                                        → Monad.return $ Nothing
        sp' (c:cs) (i,j) | c ≢ i ∧ c ≢ j = do direct ← sp cs (i,j)
                                              viaC1  ← sp cs (i,c)
                                              viaC2  ← sp cs (c,j)
                                              Monad.return $ inMaybe max direct $ Monad.liftM2 min viaC1 viaC2
        sp' (_:cs) edge                   = sp cs edge

        inMaybe ∷ (a → a → a) → Maybe a → Maybe a → Maybe a
        inMaybe f a b = Monad.liftM2 f a b `Monad.mplus` a `Monad.mplus` b

parseVote ∷ Text → Either [String] VoteLine
parseVote line =
    case Text.splitOn "\t" line of
        voter:candidate:(readRanking → Right ranking):[] →
            Right $ VoteLine (Text.toLower voter) (Text.toLower candidate) ranking
        voter:candidate:rankStr@(readRanking → Left err):[] →
            Left ["failed to parse ranking " ⧺ show rankStr ⧺ " for candidate " ⧺ show candidate ⧺ " by voter " ⧺ show voter ⧺ ": " ⧺ err]
        other →
            Left ["unexpected number of columns in row: " ⧺ show other]
    where
        readRanking ∷ Text → Either String Int
        readRanking = readEither ∘ Text.unpack


