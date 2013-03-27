--Main file that provides an easy interface to use Carneades.

module Runme where
import Parser
import Carneades
import Data.List

appTest :: String -> CAES -> AGraph -> [Argument]
appTest str caes agraph = filter (`applicability` caes) $ getArgs prop agraph 
  where prop = mkProp str

propTest  :: String -> CAES -> Bool
propTest str caes = acceptable prop caes
  where prop = mkProp str

parsefile :: String -> (CAES, AGraph)
parsefile str = (caesCONS, newArgGraph)
  where
    file = getFile str
    arglist = getArglist file
    newAssumptions = getAssumptions file
    newAudience = (newAssumptions, (getWeight arglist))
    newArgGraph = getArgGraph arglist
    standards_list = getStandards file
    getStandardFN prop = getPropStd standards_list prop
    caesCONS = CAES (newArgGraph, newAudience, getStandardFN)
    
--Use those two functions to test for applicability and arguments
testApp :: String -> String -> [Argument]
testApp filename prop = appTest prop caes agraph
  where (caes, agraph) = parsefile filename
	
testProp :: String -> String -> Bool
testProp filename prop = propTest prop caes
  where (caes, _) = parsefile filename
	
--Extended functionality for part two that emulates stages of the process	
	
process_init :: String -> String -> IO ()
process_init prem filename = process file opp_pairs new_assumptions vindications accusations prem "START"
  where 
    file = getFile filename
    arglist = getArglist file
    opp_pairs = get_oposing_pairs arglist
    assumptions = getAssumptions file
    more_assumptions = getAddAssumptions file
    all_assumptions = assumptions ++ more_assumptions
    blame_prem = mkProp prem
    vindict_prem = mkProp ("-" ++ prem)
    accusations_tmp = get_accusations prem arglist
    vindications = (intersect (get_vindications ("-" ++ prem) accusations_tmp arglist) all_assumptions) \\ assumptions
    accusations = (intersect accusations_tmp all_assumptions) \\ assumptions --Get the ones not used and in all assumptions
    new_assumptions = assumptions ++ (more_assumptions \\ (union vindications accusations)) --Puts assumptions that we've missed
    --into the initial list
    
process :: String -> [([Proposition], [Proposition])] -> [Proposition] -> [Proposition] -> [Proposition] -> String -> String -> IO ()
process filestr opp_pairs curr_assumptions vindict_ass accus_ass blame_prem previous
  | (vindict_ass == []) && (state == True) = putStrLn ("Finished process, premise \"" ++ blame_prem ++ "\" is found True.")
  | (accus_ass == []) && (state == False) && (state_inverse == False) && (vindict_ass == []) = putStrLn ("Finished process, premise \"" ++ blame_prem ++ "\" is found False, however the reverse could not be proven either.")
  | (accus_ass == []) && (state_inverse == True) = putStrLn ("Finished process, premise \"" ++ blame_prem ++ "\" is found False, and the reverse is proven to be true.")
  | state == False && (accus_ass /= []) = do
                        putStrLn audience_str
                        putStrLn ""
                        if (previous == "FALSE") then putStrLn "It is still the prosecution turn to provide argument." else putStrLn "Currently it's the prosecution turn to provide convictive evidence."
                        putStrLn blame_str
                        putStrLn ""
                        putStrLn ""
                        x <- process filestr opp_pairs (curr_assumptions ++ new_blame) vindict_ass (drop 1 accus_ass) blame_prem new_previous
                        return x
  | state == True = do  
                        putStrLn audience_str
                        putStrLn ""
                        if (previous == "TRUE") then putStrLn "It is still the defense's turn to provide counter argument." else putStrLn "Currently it's the defense's turn to provide vindictive evidences."
                        putStrLn def_str
                        putStrLn ""
                        putStrLn ""
                        x <- process filestr opp_pairs (curr_assumptions ++ new_def) new_vindict accus_ass blame_prem new_previous
                        return x
  | (state_inverse == False) = do  
                        putStrLn audience_str
                        putStrLn ""
                        putStrLn not_guilty_prove_str
                        putStrLn def_str
                        putStrLn ""
                        putStrLn ""
                        x <- process filestr opp_pairs (curr_assumptions ++ new_def) new_vindict accus_ass blame_prem new_previous
                        return x
  where 
    state = propTestProc blame_prem caes
    state_inverse = propTestProc ("-" ++ blame_prem) caes --Check if the inverse is true
    new_previous = if (state == True) then "TRUE" else "FALSE"
    (caes, _) = compute_caes_state filestr (nub curr_assumptions)
    new_blame = [head accus_ass]
    blame_str = "Prosecution has chosen evidence: \"" ++ (snd $ head new_blame) ++ "\" from the pool of evidence!"
    new_def = [defend opp_pairs vindict_ass curr_assumptions]
    def_str = "The defense has chosen evidence: \"" ++ (snd $ head new_def) ++ "\" from the pool of evidence!"
    new_vindict = vindict_ass \\ new_def
    not_guilty_prove_str = ("The premise: \"" ++ blame_prem ++ "\" could not be proven but the defense is trying to prove the opposite.")
    audience_str = "Evidences taken into account thus far are: " ++ (print_audience (nub curr_assumptions))
    
-- Use this function to find a candidate proposition for defense. Unnrecessary complicated
-- And working through the powers of black magic and nested lists...
defend :: [([Proposition], [Proposition])] -> [Proposition] -> [Proposition] -> Proposition
defend opp_pairs vindict_ass curr_assumptions
  | counters == [] = head vindict_ass --We didn't find a counter so we just give a vindictive assumption
  | otherwise = head counters --Otherwise just give the head to the counters
  where 
    new_curr = curr_assumptions \\ vindict_ass --Remove all vindictive assumptions befor elooking for cocunters
    counters = intersect (head (map f new_curr)) vindict_ass
    f prem = find_counter [prem] opp_pairs
    
propTestProc  :: String -> CAES -> Bool
propTestProc str caes = acceptable prop caes
  where prop = mkProp str
  
compute_caes_state :: String -> [Proposition] -> (CAES, AGraph)
compute_caes_state file newAssumptions = (caesCONS, newArgGraph)
  where
    arglist = getArglist file
    newAudience = (newAssumptions, (getWeight arglist))
    newArgGraph = getArgGraph arglist
    standards_list = getStandards file
    getStandardFN prop = getPropStd standards_list prop
    caesCONS = CAES (newArgGraph, newAudience, getStandardFN)
    
print_audience :: [Proposition] -> String
print_audience proplist = take ((length string) -1) string
  where f (bool, prop) = if (bool == True) then ("(True," ++ prop ++"),") else ("(False," ++ prop ++ "),")
        string = concat (map f proplist)
        
	
-- For testing purposes I have implemented the argument from the language.lhs
test :: Bool
test = test1 && test2 && test3 && test4 && test5 && test6

test1 :: Bool
test1 = testAppIntent == (testApp "Test_Argument" "intent")

test2 :: Bool
test2 = testAppNotIntent == (testApp "Test_Argument" "-intent")

test3 :: Bool
test3 = testAppMurder == (testApp "Test_Argument" "murder")

test4 :: Bool
test4 = testAppNotMurder == (testApp "Test_Argument" "-murder")

test5 :: Bool
test5 = testMurder == (testProp "Test_Argument" "murder")

test6 :: Bool
test6 = testNotMurder == (testProp "Test_Argument" "-murder")