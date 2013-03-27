--This module contains all functions that do the actual parsing.

module Parser where
import Carneades
import Data.Char
import System.IO.Unsafe
import Data.List

-- IO Functions
getFilefromHDD :: String -> String
getFilefromHDD x = unsafePerformIO $ readFile x

getFile :: String -> String
getFile str = filtercomments $ getFilefromHDD ("./" ++ str)
--End here

--Argument list functions. I am using a data structure [((String, Argument), Double)]
--So that i can carry around all the information from the Arguments part of the file

getArglist :: String -> [((String, Argument), Double)]
getArglist file = get_all_arguments arg_list
  where arg_list = dropemptylines (takeUntil "ASSUMPTIONS:" (dropUntil "ARGUMENTS:" file))
	
get_all_arguments :: String -> [((String, Argument), Double)]
get_all_arguments str = map construct_argument arglist
  where arglist = striparguments str
	
-- Construct argument expects to find something in the format:
-- argname [prop,prop] [prop,prop] prop weight. It looks for the next element and when it matches
-- it, it drops the matching string and tries to match the next part with the function for the
-- next part of the argument.

construct_argument :: String -> ((String, Argument), Double)
construct_argument initial
  | not $ all(/=[]) [argument,bracket1,bracket2,lastprop] = error $ "Parse error on the line containing: " ++ 
  (concat(map (++ " ") [argument,bracket1,bracket2,lastprop]))
  | finalfloat > 1 = error "Weight should be between 0 and 1"
  | finalfloat == (read "-1" :: Double) = error "No weight assigned"
  | otherwise = (((stripwhitespaces argument), arg),finalfloat)
  where	argument = getArgName initial
	new_str = dropUntil argument initial
	bracket1 = find_bracket_seq new_str
	newer_str = dropUntil bracket1 new_str
	bracket2 = find_bracket_seq newer_str
	even_newer_str = dropUntil bracket2 newer_str
	lastprop = getLastProp even_newer_str
	newest_str = dropUntil lastprop even_newer_str
	float = find_float newest_str 
	finalfloat = if (isFloatStr float) then (read float :: Double) else read "-1" :: Double
	prem = (stringtolist bracket1) 
	exc = (stringtolist bracket2)
	arg = mkArg	      prem 
			      exc
			      (stripwhitespaces lastprop)
			      
-- Helper functions for construct argument:

getArgName :: String -> String --Gets the argument name
getArgName str = takeWhile (/='[') str

getLastProp :: String -> String --Gets the last proposition in the argument the one outside of the
getLastProp str = takeWhile (not . isSpace) (delleadwhitespaces str) --brackets before the weight

find_bracket_seq :: String -> String --Proposition that is in a bracket sequence
find_bracket_seq str = (takeWhile (/=']') (dropWhile (/= '[') str)) ++ "]"

stringtolist :: String -> [String] --Converts a bracketsequence proposition into a list
stringtolist str = split_at ',' (stripwhitespaces str_nobrackets) --of strings so that it can
  where str_nobrackets = drop 1 $ reverse (drop 1 (reverse str)) --be constructed
	
--Float functions:
-- Check if String is Float.
isFloatStr :: String -> Bool
isFloatStr str = (all isNumber (numbers ++ numbers2)) && (point == ".") && (numbers /= "") && (numbers2 /= "")
  where numbers = takeWhile isNumber str
	left = dropWhile isNumber str
	point = take 1 left
	leftover = drop 1 left
	numbers2 = takeWhile isNumber leftover

find_float :: String -> String --Find the float
find_float str = (takeWhile isNumber str_nowhite) ++ "." ++  (takeWhile isNumber 
								(drop 1  
								  (dropWhile isNumber str_nowhite)))
  where str_nowhite = delleadwhitespaces str

--Function for finding the weight.
getWeight :: [((String, Argument), Double)] -> Weight
getWeight args arg
  | arg == arg_iter = weight
  | otherwise = getWeight (tail args) arg
  where ((name, arg_iter), weight) = head(args)    
	
--End of Float functions. End of helper functions for the [((String, Argument), Double)] data
--Structure

-- Function for finding the assumption. Uses the same thing that construct_argument uses to
-- construct list of propositions.

getAssumptions :: String -> [Proposition]
getAssumptions file = mkAssumptions $ stringtolist $ find_bracket_seq assumption_string
  where assumption_string = takeUntil "STANDARDS:" (dropUntil "ASSUMPTIONS:" file)
	
--Function for finding the additional assumptions: 

getAddAssumptions :: String -> [Proposition]
getAddAssumptions file = mkAssumptions $ stringtolist $ find_bracket_seq assumption_string
  where assumption_string = (dropUntil "ADDITIONAL ASSUMPTIONS:" file)
        
--Function used for parsing standards.
--Get all the propositions and standards into a list of tuples so that we can use the name of
--the standard later to parse the appropriate standard.
getStandards :: String -> [(Proposition, String)] --The string is the name of the standard. Use it later
getStandards file = map getStandard recline --When constructing the AssignStandard data type
  where standardstr =  delleadwhitespaces (takeUntil "ADDITIONAL ASSUMPTIONS:" (dropUntil "STANDARDS:" file))
	recline = split_at '\n' standardstr

getStandard :: String -> (Proposition, String) --Put a single standard in a (prop, standardname) tupple
getStandard str = ((mkProp propstr), (delleadwhitespaces standard))
  where propstr = delleadwhitespaces (takeUntil " " str)
	standard = dropUntil propstr str
	
--Assigns Standard based on the standard name string parsed. If proposition is not in Standards line
--defaults to scintilla. If the standard name is unrecognized throws an error.
getPropStd :: [(Proposition, String)] -> AssignStandard
getPropStd propstr prop --Given a proposition finds an appropriate Standard
  | propstr == [] = scintilla --If none is found doesn't do anythign
  | prop == prop_ = fn
  | otherwise = getPropStd (tail propstr) prop
  where (prop_, str) = head (propstr)
	fn = if (str == "scintilla") then scintilla
			      else if (str == "beyond_reasonable_doubt") then beyond_reasonable_doubt
						    else if (str == "preponderance") then preponderance
					   else if (str == "clear_and_convincing") then clear_and_convincing
						else if (str == "dialectical_validity") then dialectical_validity
					     else error ("Unrecognized Standard: " ++ str)

-- End of Standard Functions
-- Graph Functions	

getArgGraph :: [((String, Argument), Double)] -> AGraph
getArgGraph arglist = mkArgGraph (aGraph arglist)


--Unpacks just the arguments from the big list in order to construct an argGraph
aGraph :: [((String, Argument), Double)] -> [Argument]
aGraph str
  | str == [] = []
  | otherwise = [arg] ++ aGraph (tail str)
  where ((name, arg), weight_) = head str

--End of graph Functions

--Functions for lawyer and prosecutor system
--Functions that take input of the type [((String, Argument), Double)] and construct
--Tuples of premises and exceptions that counter them. We will use this later in order
--to make an automatic system that simulates a lawyer and a prosecutor.

--FInd premises that we need to prove in order to vindict the individual.
--With negation could be easily used to achieve the opposite end with "-str"
find_convictive_prem :: String -> [((String, Argument), Double)] -> [Proposition]
find_convictive_prem str arglist 
  | arglist == [] = []
  | premtoprove == c = prem ++  find_convictive_prem str (drop 1 arglist)
  | otherwise = find_convictive_prem str (drop 1 arglist)
  where (Arg prem exc c) = snd $ fst $ head arglist
        premtoprove = mkProp str
        
--In order to deal with multilayer proofs we need to check if one of the propositions
--returned by the function above actually has some premice that needs to be satisfied
--If that is the case we should add that premice to the things the jurator may and should
--use. We need to run that more than once, because with each run we go one level deeper
--in the argumentative graph so for multilevel proofs we need to be sure we have taken
--into account everything needed.

find_convictive_rec :: [Proposition] -> [((String, Argument), Double)] -> [Proposition]
find_convictive_rec props arglist
  | arglist == [] = nub props --Remove potential duplicates
  | (elem c props) = find_convictive_rec (props ++ prem) (drop 1 arglist)
  | otherwise = find_convictive_rec props (drop 1 arglist)
  where (Arg prem exc c) = snd $ fst $ head arglist

--explore multiple layers in the network
find_convictive_rec_rec :: [Proposition] -> [Proposition] -> [((String, Argument), Double)] -> [Proposition]
find_convictive_rec_rec props propsnewer arglist
  | props == propsnew = props
  | otherwise = find_convictive_rec_rec propsnew props arglist
  where propsnew = find_convictive_rec props arglist

-- Function that combines the 3 above. This are the premises which a jurator needs to prove
get_accusations :: String -> [((String, Argument), Double)] -> [Proposition]
get_accusations str arglist = find_convictive_rec_rec (find_convictive_prem str arglist) [] arglist

--Function together with the ones below that combined give the assumptions that the defense needs
get_vindications :: String -> [Proposition] -> [((String, Argument), Double)] -> [Proposition]
get_vindications str acc_prop_list input = (get_accusations str input) ++ rev_accusations acc_prop_list pairs
  where pairs = get_oposing_pairs input

rev_accusations :: [Proposition] -> [([Proposition], [Proposition])] -> [Proposition]
rev_accusations premices proplists
  | premices == [] = []
  | otherwise = (rev_accusation (head premices) proplists) ++ (rev_accusations (drop 1 premices) proplists)

rev_accusation :: Proposition -> [([Proposition], [Proposition])] -> [Proposition]
rev_accusation prop proplists
  | proplists == [] = []
  | elem prop prem = exc ++ rev_accusation prop (drop 1 proplists)
  | otherwise = rev_accusation prop (drop 1 proplists)
  where (prem, exc) = head proplists
        
--Given a premise by the prosecutor we should find what counters it (if such thing exists)
find_counter :: [Proposition] -> [([Proposition], [Proposition])] -> [Proposition]
find_counter prem premlist
  | premlist == [] = []
  | prem_cur == prem = exc
  | otherwise = find_counter prem (drop 1 premlist)
  where (prem_cur,exc) = head premlist

get_oposing_pairs :: [((String, Argument), Double)] -> [([Proposition], [Proposition])]
get_oposing_pairs input = map get_opposition input 

--returns (Premise, Exception)
get_opposition :: ((String, Argument), Double) -> ([Proposition], [Proposition])
get_opposition ((str,arg),double) = (prem, exc)
  where (Arg prem exc c) = arg

--End of lawyer and prosecutor functions

--Generic helper functions for various input processing tasks.

--Functions for taking until a String or Dropping until a string
-- String given is dropped as well)
dropUntil :: String -> String -> String --Drop Until a certain string
dropUntil todrop str
  | str == [] = []
  | take n str == todrop = drop n str
  | otherwise = dropUntil todrop (drop 1 str)
  where n = length todrop
	
takeUntil :: String -> String -> String -- Take until a certain String
takeUntil totake str = takeUntilHelper totake str []
	
takeUntilHelper :: String -> String -> String -> String --Drop Until a certain string
takeUntilHelper until_str str returnstring
  | str == [] = []
  | take n str == until_str = returnstring
  | otherwise = takeUntilHelper until_str (drop 1 str) return_new
  where n = length until_str
	return_new = returnstring ++ (take 1 str)

-- Functions for stripping whitespaces

stripwhitespaces :: String -> String --Removes all whitespaces from a string. Useful for when parsing
stripwhitespaces str = [x | x <- str, (not $ isSpace x)] --arguments within brackets []

delleadwhitespaces :: String -> String
delleadwhitespaces str = dropWhile isSpace str
  
--Splits string at a given char
split_at :: Char -> String -> [String]
split_at char str = split_rec char [] str

split_at_test :: Bool
split_at_test = ["I","like","pie","too","fuckin'","much"] == split_at ' ' "I like pie too fuckin' much"

split_rec :: Char -> [String] -> String -> [String]
split_rec char list str
  | str == "" = list
  | otherwise = split_rec char (list ++ [to_concat]) rest_output
  where [to_concat,rest_output] = give_first char str
       
give_first :: Char -> String -> [String]
give_first char str = [part_one, rest]
  where part_one = takeWhile (/= char) str
        rest = drop (length part_one + 1) str 

droplines :: Int -> String -> String
droplines 0 str = str
droplines n str = droplines (n-1) (dropline str)

dropline :: String -> String
dropline str = delleadwhitespaces (drop 1 (dropWhile ('\n'<) str))

--Strip comments:When parsing we should strip all the comments lines

filtercomments :: String -> String
filtercomments str = concat (map (++ "\n") nocomments)
  where nocomments = dropcomment $ lines str  
  
dropcomment :: [String] -> [String]
dropcomment str --Str is a list of strings so head takes the first list
  | str == [] = []
  | take 2 (delleadwhitespaces $ head str) == "--" = dropcomment (tail str)
  | otherwise = [head str] ++ dropcomment (tail str)

-- Drops empty lines, to fascilitate parsing

dropemptylines :: String -> String
dropemptylines str = concat (map (++ "\n") noemptylines)
  where noemptylines = dropemptylines_helper $ lines str

dropemptylines_helper :: [String] -> [String]
dropemptylines_helper str
  | str == [] = []
  | (delleadwhitespaces current) == [] = dropemptylines_helper $ tail str
  | otherwise = [current] ++ (dropemptylines_helper $ tail str)
  where current = head str
  
--Strips the arguments that are separated by points
--Striparguments gets a list of arguments. It matches the parts between an argument name
--and a fulstop. We parse those to construct_argument one by one in order to avoid parsing
--empty lines or something irrelevant so that we can detect syntax errors within construct_argument.
striparguments :: String -> [String]
striparguments str
  | str == [] = []
  | rest == "\n" = [output] --If all that is left is an empty line
  | otherwise = [output] ++ (striparguments rest)
  where (output, rest) = giveargument str
    
--Give an argument and the rest of the string for matching more of the argument.
giveargument :: String -> (String, String)
giveargument str 
  | rest == [] = (candidate, rest)
  | not (isNumber (head rest)) =  (candidate, rest)
  | otherwise = (candidate ++ numberandpoint, (dropUntil numberandpoint rest))
  where candidate = (takeWhile (/= '.') str) ++ "."
	rest = dropUntil candidate str
	numberandpoint = (takeWhile (/= '.') rest) ++ "."