-- | Solver for an n-puzzle using the A* algorithm and the sum of the manhattan distances as its heuristic. This implementation works only for quadratic puzzles.
--
-- Explanation (Wikipedia):
-- 
-- The n-puzzle is known in various versions, including the 8 puzzle, the 15 puzzle, and with various names (Gem Puzzle, Boss Puzzle, Game of Fifteen, Mystic Square and many others). 
-- It is a sliding puzzle that consists of a frame of numbered square tiles in random order with one tile missing. If the size is 3x3, the puzzle is called the 8-puzzle or 9-puzzle, and if 4x4, 
-- the puzzle is called the 15-puzzle or 16-puzzle. The object of the puzzle is to place the tiles in order (see diagram) by making sliding moves that use the empty space.
-- The n-puzzle is a classical problem for modelling algorithms involving heuristics. Commonly used heuristics for this problem include counting the number of misplaced tiles and finding the sum 
-- of the Manhattan distances between each block and its position in the goal configuration. Note that both are admissible, i.e., they never overestimate the number of moves left, 
-- which ensures optimality for certain search algorithms such as A*.
--
--   (C) 2011 Stefan M&#252;nchow
module NPuzzle where

import Data.List
import System.Environment

-- * Types

-- | Board is represented as a matrix of Int.
type Board                                  = [[Int]]

-- | Position is a tuple of Int.
type Position                               = (Int, Int)

-- | Object to represent a current state of the puzzle with a representation of 
--   the board and its cost value pursuant to the heuristic.
data State
    -- | Creates a new State object with the given board and cost value.
    = State Board Int
    deriving Show                                              

-- | Object to represent a search result. A result consists of a value indicating
--   success or failure and a list of all visited states.
data Result                                 
    -- | Creates a new Result object with the given result value and state list. 
    = Result Bool [State] 
    deriving Show
          
-- | States are equal if their boards are equal.
instance Eq State where
    (State b1 _) == (State b2 _)            = b1 == b2
    s1 /= s2                                = not (s1 == s2)
    
-- | States are ordered by their cost value. The smaller a cost value
--   is, the smaller is the state.
instance Ord State where
    compare (State _ c1) (State _ c2)
        | c1 < c2                           = LT
        | c1 == c2                          = EQ
        | otherwise                         = GT

-- * Functions 

-- ** Getting elements from structures

-- | Returns the value of a Maybe type. Throws an error if the value is Nothing.
value                                       :: Maybe Int -> Int
value (Just v)                              = v
value Nothing                               = error "Value 'Nothing' is not allowed!"  

-- | Returns the board of a State object.
board                                       :: State -> Board
board (State b _)                           = b   

-- | Returns the state list from a Result object.
states                                      :: Result -> [State]
states (Result _ s)                         = s

-- ** Calculating the heuristic

-- | Calculates the manhattan distance of two points.
manhattanMetric                             :: (Position, Position) -> Int
manhattanMetric ((x1,y1), (x2,y2))          = abs (x1 - x2) + abs (y1 - y2)

-- | Calculates the heuristic for then given current cost value, state and goal state.
calculateCost                               :: Int -> [Position] -> [Position] -> Int
calculateCost g statePos goalPos            = foldl (+) g $ map manhattanMetric $ zip statePos goalPos


-- | Returns the position (x, y) of the value on the board.
position                                    :: Board -> Int -> Position
position board val                          = position2 board 0 val

-- | Returns the position (x, y) of the value on the board, using the specified start
--   index to count rows from.
position2                                   :: Board -> Int -> Int -> Position
position2 [] _ _                            = error "Element not found on board."
position2 board start val
    | elem val (head board)                 = (start, value $ elemIndex val $ head board)
    | otherwise                             = position2 (tail board) (start + 1) val

-- | Calculates the cost value of the given state by adding up the manhattan distances
--   of every piece on the current board compared to the position of the piece in the goal state.
evalState                                   :: [State] -> State -> State -> State
evalState vis goal state                    =  State (board state) (calculateCost (length vis) currentCoords goalCoords)
                                                where 
                                                    currentCoords = map (position (board state)) flatState
                                                    goalCoords = map (position (board goal)) flatState
                                                    flatState = concat (board state)

-- ** Generate states

-- | Returns a list of all possible positions to which a piece at the specified position can
--   be moved.
possibleMoves                               :: Position -> Int -> [Position]
possibleMoves (x, y) max
    | x == 0 && y == 0                      = [(x + 1, y), (x, y + 1)]
    | x == max && y == max                  = [(x - 1, y), (x, y - 1)]
    | x == max && y == 0                    = [(x - 1, y), (x, y + 1)]
    | x == 0 && y == max                    = [(x + 1, y), (x, y - 1)]
    | x == 0                                = [(x + 1, y), (x, y - 1), (x, y + 1)]
    | y == 0                                = [(x - 1, y), (x + 1, y), (x, y + 1)]
    | x == max                              = [(x, y + 1), (x, y - 1), (x - 1, y)]
    | y == max                              = [(x + 1, y), (x - 1, y), (x, y - 1)]
    | otherwise                             = [(x, y + 1), (x, y - 1), (x + 1, y), (x - 1, y)]

-- | Returns a list with the element at the specified index replaced by the specified value.
replaceElem                                 :: [a] -> Int -> a -> [a]
replaceElem xs idx x                        = take idx xs ++ [x] ++ drop (idx + 1) xs

-- | Swaps the values of two positions on the board and returns the resulting state.
swap                                        :: State -> Position -> Position -> State
swap (State f v) (x1, y1) (x2, y2)          = State (replaceElem replaced x1 (replaceElem (replaced !! x1) y1 ((f !! x2) !! y2))) v
                                                where 
                                                    replaced = replaceElem f x2 (replaceElem (f !! x2) y2 ((f !! x1) !! y1))

-- | Generates a list of all following states of the specified state with their cost
--   value.
movements                                   :: State -> State -> [State] -> [State]
movements state goal vis                    = map (evalState vis goal)
                                                [swap state blankField x | x <- possibleMoves blankField (length (board goal) - 1)]
                                                where 
                                                    blankField = position (board state) 0

-- ** Inserting states into lists 
              
-- | Inserts each element of a given list of states into a second list. Assuming that the second list
--   is sorted by cost value in ascending order, the states are inserted at the correct position based
--   on the ordering of the State class.
insertStates                                :: [State] -> [State] -> [State]
insertStates [] ss                          = ss 
insertStates (s:ss1) ss2                    = insertStates ss1 (insert s ss2)
               
-- | If result value is True, a new Result with the specified state added to the list of visited states 
--   is returned. Otherwise the given result is returned without adding the given state.
addVisited                                  :: State -> Result -> Result
addVisited state (Result True vis)          = Result True (state:vis)
addVisited _ (Result False vis)             = Result False vis         

-- ** Search functions

-- | Implements the A* search algorithm. Searches the given open list containing all nodes to expand
--   sorted by cost value in ascending order (cheapest node is expanded first). The given result
--   contains all visited nodes and is used to avoid cycles.
search                                      :: [State] -> State -> [State] -> Result                          
search open goal vis
    | null open                             = Result False []
    | (head open) == goal                   = Result True [head open]
    | otherwise                             = addVisited node $ search (insertStates succs nodeList) goal (node:vis)
                                                where 
                                                    node = head open
                                                    nodeList = tail open
                                                    succs = filter (\s -> notElem s vis) (movements node goal vis)

-- | Solves the puzzle with the given start state.
solve                                       :: State -> State -> [Board]
solve start goal                            = map board $ states (search [start] goal [])

-- ** IO functions and main

-- | Prints a list of ints to stdout in a formatted way.
printList                                   :: [Int] -> IO ()
printList []                                = do return ()
printList (i:is)                            = do      
                                                if i < 10
                                                    then putStr (" " ++ (show i))
                                                    else putStr (show i)
                                                putStr " | "
                                                printList is
                                                return ()

-- | Prints a board to stdout in a formatted way.
printBoard                                 :: Board -> IO ()
printBoard []                              = do return ()
printBoard (r:rs)                           = do                                                
                                                putStr "| "                                          
                                                printList r
                                                putStr "\n"
                                                putStrLn $ take (((length r) * 5) + 1) (repeat '-')
                                                printBoard rs
                                                return ()

-- | Prints a sequence of boards to stdout in a formatted way.
printResult                                 :: [Board] -> IO ()
printResult []                              = do return ()
printResult (b:bs)                          = do              
                                                putStrLn $ take (((length b) * 5) + 1) (repeat '-')                                  
                                                printBoard b
                                                putStr "\n"
                                                printResult bs
                                                return ()

-- | Parses a list of lists of Ints.
parseList                                   :: ReadS Board
parseList                                   = readList

-- | Parses a board from stdin and returns it.
parseBoard                                  :: String -> Board
parseBoard s                                = fst $ head (parseList s)

-- | Checks if a the dimensions of a board are equal.
dimsEqual                                   :: Board -> Bool
dimsEqual b                                 = all (\x -> x == (length b)) (map length b)

-- | Main function. Takes the start state and the goal state as lists of Int as
--   command line arguments.   
main                                        :: IO ()
main                                        = do
                                                args <- getArgs
                                                let boardStart = parseBoard (head args)
                                                let boardGoal = parseBoard (args !! 1)
                                                putStrLn "(C) 2011 Stefan Münchow"
                                                putStrLn "Solving puzzle ...\n"
                                                if (dimsEqual boardStart && dimsEqual boardGoal)
                                                    then printResult $ solve (State boardStart 0) (State boardGoal 0)
                                                    else error "Failure! Boards have to be quadratic."
                                                putStrLn "Solved!"
                                                return ()

