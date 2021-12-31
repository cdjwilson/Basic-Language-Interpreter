module Main where

import Control.Monad (when)
import System.Directory (doesFileExist, XdgDirectory (XdgCache))
import System.Environment (getArgs)
import Bird.Parser
import Bird.Printer
import Data.Char
import GHC.Real (reduce)
import System.Directory.Internal.Prelude (undefined)
import Data.List
import Data.Maybe
import Data.Bits (Bits(xor))

main :: IO ()
main = do args <- getArgs
          let files = filter ("-p" /=) args
              go | elem "-p" args = goParse
                 | otherwise      = goEval
          when (not (null files)) $
              go  . concat =<< mapM readFile files

goParse, goEval :: String -> IO ()
goParse s = putStrLn (printlogic (runParser logicparser s))
goEval s  = putStrLn (basicq (runParser logicparser s))

{-----------------------------------------------------------------------------------------------
What are we doing.
Parsing a input file that has multiple lines but will only have one function on each line
So split the lines and parse each line

Syntax:
Term - atom     : string starting with lowercase letter                             -- x, start, end
       variable : string beginnning with an uppercase letter                        -- X, Start
       string   : string starting with " and has anything inbetween and ends with " -- "This is an example of a String123"
       compound : starts with an atom then ( then t1...tn terms then )              -- edge(c,d), lam("x", app(var("x"), var("x")))

predicate is syntactically identical to terms, however it will have a . or a ? after it
each line if non empty will be a predicate or comment
we have a Term that is either an Atom, Variable, String, or Compound. Where a compound consists of an atom and then a list of terms
and Atom, Variable, and String are just Strings
now on each line of a logic program we have a predicate. This predicate is composed of an Atom and a list of terms
where each of those terms themselves can be Compounds
but each line is either a comment, rule, or query
so a whole logic file is going to be a list of rules or querys
so we will end with a Logic data type that is either a query, rule, or list of these things
query can be a list of queries seperated by commas -- q1,q2,...,qn?
rule can be of type p.
or p :- p1,p2,...pn.

What to do 
--------------------------------------------------
fix string1 implementation to accept any character --fixed
implement parsing of comment in logicparser -- probably done
implement full parsing of query and rule -- probably done

--------
Query is solved by getting having predicate return a list of predicates if it is seperated by commas
Rule has a problem. It returns the list of predicates as type rule but you want the 
p is true iff the program contains a rule p :- q1,q1,...,qn. and each qi is true.
How can qi be true when it is supposed to be a list of predicates
I think its saying that p is true if...
going to still store as a Rule with a list of predicates, just remember that the head is p and the tail is q1,q2,...,qn
--------

desugaring numbers and lists -- finished integers, finished lists
figure out printing

-------------------
for printing
end goal: print a [Logic] where each element in the list is going to be a Query or Rule
so we want to print Query or Rule
where Query has a list of predicates seperated by commas then a ? or just one predicate with a ?
where Rule has a list of predicates but if its greater than one then its of the form p :- q1,q2,q3,q4 then a dot
-------------------


What to do for eval
-------------------
Start with basic operations
Everytime you see a Rule add it to the list of Rules
Everytime you see a Query check to see if its within the list of Rules
logicparse gives a list of rules and query
reverse it then check if the element is a query or a rule
    if its a query check if it exists in the rest of the list
figured out how to take care of basic query and query with multiple predicates
need to figure out how to responde to a query that references a Rule with multiple predicates
the first predicate in the rule is the reference one, then the rest of them have to be true for that rule to be true

finished basic operations
possibly finshed unification

Now finish resolution
take a predicate p from query
find a rule p = :- q1...qn that applies to the query
replace p with q1...qn in the query
need a way to check for variables.
problem: both rules and queries can have variables so p(X). p(X)? will return yes when it should return 
first check if query has variables
    if it does check

need a resolution algorithm that takes a query with variables and returns a list of list of variables that work
if the list has no elements then we know that there are no rules that apply
we need to check if there is a value for each varialbe such that the query is true

-------------------------------------------------------------------------------------------------}

data Term = Atom String | Variable String | String String | Compound Term [Term]
       deriving (Eq, Show, Ord)

data Predicate = Predicate Term [Term]
       deriving (Eq, Show)

data Logic = Query [Predicate] | Rule [Predicate]
       deriving (Eq, Show)


atom :: Parser Term
atom = do x <- lower
          xs <- allLetter
          return (Atom (x : xs))

allLetter :: Parser String
allLetter = (do x <- token lower <|> token upper
                xs <- allLetter
                return (x : xs)) <|>
            return ""


variable :: Parser Term
variable = do x <- upper
              xs <- allLetter
              return (Variable (x : xs))

isquote :: Char -> Bool
isquote x = x == '"'

quote :: Parser Char
quote = satisfy isquote

iscom :: Char -> Bool
iscom x = x == ','

com :: Parser Char
com = satisfy iscom

isnotquote :: Char -> Bool
isnotquote x = x /= '"'

notquote :: Parser Char
notquote = satisfy isnotquote

allchar :: Parser String
allchar = (do x <- notquote
              xs <- allchar
              return (x : xs)) <|>
          return ""

string1 :: Parser Term
string1 = do x <- quote
             xs <- allchar
             xss <- quote
             return (String(x : xs ++ [xss]))

isopenp :: Char -> Bool
isopenp x = x == '('

openp :: Parser Char
openp = satisfy isopenp

isclosep :: Char -> Bool
isclosep x = x == ')'

closep :: Parser Char
closep = satisfy isclosep

isnewl :: Char -> Bool
isnewl x = x == '\n'

newl :: Parser Char
newl = satisfy isnewl

desugint :: Int -> Term
desugint x | x == 0 = Atom "zero"
           | otherwise = Compound (Atom "succ") [desugint (x-1)]

desugl :: [Term] -> Term
desugl [] = Atom "nil"
desugl (x : xs) = Compound (Atom "cons") [x, desugl xs]

desuglp :: [Term] -> [Term] -> Term
desuglp x y | length x == 1 = Compound (Atom "cons") [head x, head y]
                       | otherwise = Compound (Atom "cons") [head x, desuglp (tail x) y]

desuglist :: Parser Term
desuglist = (do a <- token (satisfy (=='['))
                b <- token middlecomp
                c <- token (satisfy (=='|'))
                d <- token middlecomp
                e <- token (satisfy (==']'))
                return (desuglp b d)) <|>
            (do a <- token (satisfy (=='['))
                b <- token middlecomp
                e <- token (satisfy (==']'))
                return (desugl b))

allnewl :: Parser String
allnewl = (do x <- newl
              xs <- allnewl
              return (x : xs)) <|>
          return ""

middlecomp :: Parser [Term]
middlecomp = (do a <- token compound
                 b <- token com
                 c <- token middlecomp
                 return (a : c)) <|>
             (do a <- token variable
                 b <- token com
                 c <- token middlecomp
                 return (a : c)) <|>
             (do a <- token string1
                 b <- token com
                 c <- token middlecomp
                 return (a : c)) <|>
             (do a <- token atom
                 b <- token com
                 c <- token middlecomp
                 return (a : c)) <|>
             (do a <- token nat
                 b <- token com
                 c <- token middlecomp
                 return (desugint a : c)) <|>
             (do a <- token desuglist
                 b <- token com
                 c <- token middlecomp
                 return (a : c)) <|>
             (do a <- token compound
                 return [a]) <|>
             (do a <- token variable
                 return [a]) <|>
             (do a <- token string1
                 return [a]) <|>
             (do a <- token atom
                 return [a]) <|>
             (do a <- token nat
                 return [desugint a]) <|>
             (do a <- token desuglist
                 return [a]) <|>
             return []

compound :: Parser Term
compound = do a <- token atom
              c <- parens middlecomp
              return (Compound a c)

rulething :: Parser String
rulething = do x <- satisfy (==':')
               xs <- satisfy (=='-')
               return (x : [xs])

predicate :: Parser [Predicate]
predicate = (do a <- token atom
                b <- token openp
                c <- token middlecomp
                d <- token closep
                e <- token com
                f <- token predicate
                return (Predicate a c : f)) <|>
            (do a <- token atom
                b <- token openp
                c <- token middlecomp
                d <- token closep
                e <- token rulething
                f <- token predicate
                return (Predicate a c : f)) <|>
            (do a <- token atom
                b <- token openp
                c <- token middlecomp
                d <- token closep
                return [Predicate a c]) <|>
            return []

isperc :: Char -> Bool
isperc x = x == '%'

perc :: Parser Char
perc = satisfy isperc

isnotnewl :: Char -> Bool
isnotnewl x = x /= '\n'

notnewl :: Parser Char
notnewl = satisfy isnotnewl

allnotnewl :: Parser String
allnotnewl = (do x <- notnewl
                 xs <- allnotnewl
                 return (x : xs)) <|>
             return ""

comment :: Parser String
comment = (do a <- token perc
              b <- allnotnewl
              d <- comment
              return (a : b ++ d)) <|>
           (do a <- token perc
               b <- allnotnewl
               c <- token allnewl
               return (a : b ++ c)) <|>
           return []

logicparser :: Parser [Logic]
logicparser = (do z <- token comment
                  a <- token predicate
                  x <- token (satisfy (== '.'))
                  c <- token comment
                  b <- token logicparser
                  return (Rule a : b)) <|>
              (do z <- token comment
                  a <- token predicate
                  x <- token (satisfy (== '?'))
                  c <- token comment
                  b <- token logicparser
                  return (Query a : b)) <|>
              (do a <- token predicate
                  x <- token (satisfy (== '.'))
                  c <- token comment
                  b <- token logicparser
                  return (Rule a : b)) <|>
              (do a <- token predicate
                  x <- token (satisfy (== '?'))
                  c <- token comment
                  b <- token logicparser
                  return (Query a : b)) <|>
              (do a <- token predicate
                  b <- token (satisfy (== '.'))
                  c <- token logicparser
                  return (Rule a : c)) <|>
              (do a <- token predicate
                  b <- token (satisfy (== '?'))
                  c <- token logicparser
                  return (Query a : c)) <|>
              (do a <- token predicate
                  b <- token (satisfy (== '.'))
                  return [Rule a]) <|>
              (do a <- token predicate
                  b <- token (satisfy (== '?'))
                  return [Query a]) <|>
              return []

printcomp :: [Term] -> String
printcomp [] = []
printcomp (x : xs) | null xs = printterm x
                   | otherwise = printterm x ++ ", " ++ printcomp xs

printterm :: Term -> String
printterm (Atom x) = x
printterm (Variable x) = x
printterm (String x) = x
printterm (Compound x y) = printterm x ++ "(" ++ printcomp y ++ ")"

printlistterm :: [(Term, String)] -> String
printlistterm [] = []
printlistterm ((x, y) : xs) = printterm x

printpredicate :: Predicate -> String
printpredicate (Predicate x xs) = printterm x ++ "(" ++ printcomp xs ++ ")"

printlistpredicate :: [Predicate] -> String
printlistpredicate [] = []
printlistpredicate (x : xs) | null xs = printpredicate x
                            | otherwise = printpredicate x ++ ", " ++ printlistpredicate xs

printlistlogic :: [Logic] -> String
printlistlogic [] = []
printlistlogic (Rule [] : xs) = []
printlistlogic ((Query x) : xs) = printlistpredicate x ++ "?\n" ++ printlistlogic xs
printlistlogic (Rule (x : xs) : xss) | null xs = printpredicate x ++ ".\n" ++ printlistlogic xss
                                     | otherwise = printpredicate x ++ " :- " ++ printlistpredicate xs ++ ".\n" ++ printlistlogic xss

printlogic :: [([Logic], String)] -> String
printlogic [] = []
printlogic ((x,y) : xs)= printlistlogic x




-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
-- eval

evalrule :: [Predicate] -> [Logic] -> Bool
evalrule [] [] = False
evalrule x [] = False
evalrule [] x = False
evalrule p r | length [True | x <- p, Rule [x] `isElem` r] == length p = True -- for each rule after the hypothesis check that it is in the list of rules and queries
evalrule _ _ = False

isElem :: Logic -> [Logic] -> Bool
isElem (Query q) r = False
isElem (Rule q) r | Rule q `elem` r = True -- if the rule is in list then true
                  | not (null ([True | z <- [evalrule (tail x) r | Rule x <- r, q == [head x]], z])) = True -- for each rule from the list if the query is referencing the hypothesis then call evalrule for the rules in the hypothesis
                  | otherwise = False

predhasvars :: [Predicate] -> Bool
predhasvars [] = False
predhasvars ((Predicate a as) : ass) = listoftermshasvariable as || predhasvars ass

hasvariables :: [Predicate] -> [Logic] -> Bool
hasvariables [] [] = False
hasvariables [] xs = not (null ([True | Rule x <- xs, predhasvars x]))
hasvariables ((Predicate a as): ass) [] = hasvariable as as || hasvariables ass []
hasvariables ((Predicate a as): ass) xs = not (null ([True | Rule x <- xs, predhasvars x])) || hasvariable as as || hasvariables ass []

-- returns a the value of the variable if it exists
varinsubs :: Term -> [(Term, Term)] -> [Term]
varinsubs a [] = []
varinsubs a ((v, t) : vs) | a == v = [t]
                          | otherwise = varinsubs a vs

turnsubstostring :: [(Term, Term)] -> String -> String
turnsubstostring [] x = ""
turnsubstostring ((var, sub) : as) sep | null as = printterm var ++ " = " ++ printterm sub ++ sep
                                       | otherwise = printterm var ++ " = " ++ printterm sub ++ ",\n" ++ turnsubstostring as sep

isCompound :: Term -> Bool
isCompound (Compound a b) = True
isCompound x = False

compoundhasvars :: Term -> Bool
compoundhasvars (Compound a b) | listoftermshasvariable b = True
                               | otherwise = False
compoundhasvars x = False

returncompwithvarsubs :: Term -> [(Term, Term)] -> Term
returncompwithvarsubs (Compound a b) subs = Compound a (returncompwithvarsubshelp b subs)

returncompwithvarsubshelp :: [Term] -> [(Term, Term)] -> [Term]
returncompwithvarsubshelp [] subs = []
returncompwithvarsubshelp (a : as) subs | isVariable a = getvariablevaluefromsub a subs subs : returncompwithvarsubshelp as subs
                                        | compoundhasvars a = returncompwithvarsubs a subs : returncompwithvarsubshelp as subs
                                        | otherwise = a : returncompwithvarsubshelp as subs
getvariablevaluefromsub :: Term -> [(Term, Term)] -> [(Term, Term)] -> Term
getvariablevaluefromsub x [] subs = x
getvariablevaluefromsub x ((a, b) : as) subs | x == a && isVariable b = getvariablevaluefromsub b subs subs
                                             | x == a && compoundhasvars b = returncompwithvarsubs b subs
                                             | x == a = b
                                             | otherwise = getvariablevaluefromsub x as subs

getvariablefromsub :: Term -> [(Term, Term)] -> [(Term, Term)] -> (Term, Term)
getvariablefromsub a (x@(b, c) : bs) subs | a == b = (a, getvariablevaluefromsub a subs subs)
                                          | otherwise = getvariablefromsub a bs subs


getvariablesofdomain :: [Term] -> [(Term, Term)] -> [(Term, Term)]
getvariablesofdomain [] subs = []
getvariablesofdomain (var : vars) subs = getvariablefromsub var subs subs : getvariablesofdomain vars subs

getdomainofpredicates :: [Predicate] -> [Term]
getdomainofpredicates [] = []
getdomainofpredicates (Predicate a b : as) = nub (getdomainoflistofterms b ++ getdomainofpredicates as)

getdomainoflistofterms :: [Term] -> [Term]
getdomainoflistofterms [] = []
getdomainoflistofterms (Compound a b : as) = getdomainoflistofterms b ++ getdomainoflistofterms as
getdomainoflistofterms (a : as) | isVariable a = a : getdomainoflistofterms as
                                | otherwise = getdomainoflistofterms as

listofsubstostringhelp :: [[(Term, Term)]] -> [Term] -> String
listofsubstostringhelp [] domain = "No."
listofsubstostringhelp (a : as) domain | null as = turnsubstostring (reverse (getvariablesofdomain (reverse domain) a)) "."
                                       | otherwise = turnsubstostring (reverse (getvariablesofdomain (reverse domain) a)) ";\n" ++ listofsubstostringhelp as domain

listofemptytostring :: [[(Term, Term)]] -> String
listofemptytostring [] = "."
listofemptytostring (a : as) | null as = "."
                             | otherwise = ";\n" ++ listofemptytostring as

listofsubstostring :: [[(Term, Term)]] -> [Term] -> String
listofsubstostring [] domain = "No."
listofsubstostring [[]] [] = "Yes."
listofsubstostring [[]] domain = "Yes:\n."
listofsubstostring z@(a@(((x, xs) : xss)) : as) domain | length z == 1 && null a = "Yes:\n."
                                                       | null (getvariablesofdomain domain a) = "Yes:\n" ++ listofemptytostring z
                                                       | null as = "Yes:\n" ++ turnsubstostring (reverse (getvariablesofdomain domain a)) "."
                                                       | otherwise = "Yes:\n" ++ listofsubstostringhelp z domain

eval :: Logic -> [Logic] -> String
eval (Rule q) [] = ""
eval (Query q) [] = "No."
eval (Query q) rs | hasvariables q rs = listofsubstostring (take 20 (reverse (resolution q rs 1 []))) (getdomainofpredicates q)      -- for tomorrow probably, what to do when you run into a something dealing with variables
                  | length [x | x <- q, Rule [x] `isElem` rs] == length q = "Yes." -- if it doesnt have variables
                  | otherwise = "No."

answerbasicq :: Logic -> [Logic] -> String
answerbasicq (Query q) r | length [x | x <- q, Rule [x] `isElem` r] == length q = "Yes."
                         | otherwise = "No."
-- need to handle a query that references a rule with more than one predicate
basicqhelp :: [Logic] -> String
basicqhelp [] = []
basicqhelp (Query x : xs) = basicqhelp xs ++ eval (Query x) xs ++ "\n"
basicqhelp (Rule x : xs) = basicqhelp xs

basicq :: [([Logic], String)] -> String
basicq [(x, y)] = basicqhelp (reverse x)

applyvariabletoterm :: Term -> [(Term, Term)] -> Term
applyvariabletoterm a sub | null (varinsubs a sub) = a
                          | isVariable (head (varinsubs a sub)) = applyvariabletoterm (head (varinsubs a sub)) sub
                          | otherwise = head (varinsubs a sub)

applyvariablesterms :: [Term] -> [(Term, Term)] -> [Term]
applyvariablesterms [] sub = []
applyvariablesterms (Compound a b : as) sub = Compound a (applyvariablesterms b sub) : applyvariablesterms as sub
applyvariablesterms (a : as) sub | isVariable a && not (null (varinsubs a sub)) = applyvariabletoterm a sub : applyvariablesterms as sub
                                 | otherwise = a : applyvariablesterms as sub

applyvariables :: [Predicate] -> [(Term,Term)] -> [Predicate]
applyvariables x [] = x
applyvariables [] subs = []
applyvariables (x@(Predicate a b): as) subs | predhasvars [x] && not (null subs) = Predicate a (applyvariablesterms b subs) : applyvariables as subs
                                            | otherwise = x : applyvariables as subs

ruleapplys :: Predicate -> Predicate -> [(Term, Term)] -> Bool
ruleapplys x@(Predicate a b) y@(Predicate c d) sub | a == c && length b == length d = isJust (unifyingqpredicates x y sub)
                                                   | otherwise = False

resolution :: [Predicate] -> [Logic] -> Int -> [(Term, Term)] -> [[(Term, Term)]]
resolution a xs fresh subs | fresh < 500 = resolutionofpredicate a xs xs fresh subs
                           | otherwise = []

resolutionofpredicate :: [Predicate] -> [Logic] -> [Logic] -> Int -> [(Term, Term)] -> [[(Term, Term)]]
resolutionofpredicate [] [] xs fresh subs = [subs]
resolutionofpredicate [] r xs fresh subs = [subs]
resolutionofpredicate q [] xs fresh subs = []
resolutionofpredicate q (Query r : rs) xs fresh subs = resolutionofpredicate q rs xs fresh subs
resolutionofpredicate q (Rule r : rs) xs fresh subs | head q == head r && fresh < 500 && length r == 1 = resolution (applyvariables (tail (freshen r fresh)) subs ++ applyvariables (tail q) subs) xs (fresh + 1) subs ++ resolutionofpredicate q rs xs fresh subs
                                                    | null rs  && ruleapplys (head q) (head (freshen r fresh)) subs && fresh < 500 = resolution (applyvariables (tail (freshen r fresh)) (fromJust (unifyingqpredicates (head q) (head (freshen r fresh)) subs)) ++ applyvariables (tail q) subs) xs (fresh + 1) (fromJust (unifyingqpredicates (head q) (head (freshen r fresh)) subs))
                                                    | ruleapplys (head q) (head (freshen r fresh)) subs && fresh < 500 = resolution (applyvariables (tail (freshen r fresh)) (fromJust (unifyingqpredicates (head q) (head (freshen r fresh)) subs)) ++ applyvariables (tail q) (fromJust (unifyingqpredicates (head q) (head (freshen r fresh)) subs))) xs (fresh + 1) (fromJust (unifyingqpredicates (head q) (head (freshen r fresh)) subs)) ++ resolutionofpredicate q rs xs fresh subs
                                                    | otherwise = resolutionofpredicate q rs xs fresh subs

freshen :: [Predicate] -> Int -> [Predicate]
freshen [] x = []
freshen a@(Predicate b c : rs) x | x == 0 = a
                                 | otherwise = Predicate b (freshenlistofterms c x) : freshen rs x

freshenlistofterms :: [Term] -> Int -> [Term]
freshenlistofterms [] x = []
freshenlistofterms (Compound a b : as) x = Compound a (freshenlistofterms b x) : freshenlistofterms as x
freshenlistofterms (a : as) x | isVariable a = freshenvariable a x : freshenlistofterms as x
                              | otherwise = a : freshenlistofterms as x

freshenvariable :: Term -> Int -> Term
freshenvariable (Variable x) y = Variable (x ++ "$" ++ show y)

listoftermshasvariable :: [Term] -> Bool
listoftermshasvariable [] = False
listoftermshasvariable (Compound a b : as) = listoftermshasvariable b || listoftermshasvariable as
listoftermshasvariable (a : as) | isVariable a = True
                                | otherwise = listoftermshasvariable as

hasvariable :: [Term] -> [Term] -> Bool
hasvariable [] [] = False
hasvariable (a : as) (b : bs) | isvariable a b = True
                              | otherwise = hasvariable as bs

isvariable :: Term -> Term -> Bool
isvariable (Variable x) y = True
isvariable x (Variable y) = True
isvariable (Compound a b) (Compound c d) | a == c = hasvariable b d
                                         | otherwise = False
isvariable x y = False





-- unifiying predicate
unifyingqpredicates :: Predicate -> Predicate -> [(Term, Term)] -> Maybe [(Term, Term)]
unifyingqpredicates x@(Predicate a b) y@(Predicate c d) sub | a == c = unifyinglistofterms b d sub
                                                            | otherwise = Nothing

unifyinglistofterms :: [Term] -> [Term] -> [(Term, Term)] -> Maybe [(Term, Term)]
unifyinglistofterms [] [] sub = Just sub
unifyinglistofterms (a : as) (b : bs) sub | isNothing (unifyingterms a b sub) = Nothing
                                          | otherwise = unifyinglistofterms as bs (Data.Maybe.fromJust (unifyingterms a b sub))

unifyingterms :: Term -> Term -> [(Term, Term)] -> Maybe [(Term, Term)]
unifyingterms x@(Compound a b) y@(Compound c d) sub | a /= c = Nothing
                                                    | otherwise = unifyinglistofterms b d sub
unifyingterms a b sub | a == b = Just sub
                      | isVariable a && isVariable b && not (null sub) = unifyingvariables a b sub
                      | isVariable a && isVariable b && null sub = Just [(a, b)]
                      | isVariable a && not (isVariable b) && not (null sub) = unifyingsinglevariable a b sub
                      | not (isVariable a) && isVariable b && not (null sub) = unifyingsinglevariable b a sub
                      | isVariable a && not (isVariable b) && null sub = Just [(a, b)]
                      | not (isVariable a) && isVariable b && null sub = Just [(b, a)]
                      | otherwise = Nothing

unifyingsinglevariable :: Term -> Term -> [(Term, Term)] -> Maybe [(Term, Term)]
unifyingsinglevariable x@(Variable a) b [] = Just [(x, b)]
unifyingsinglevariable x@(Variable a) b sub | not( null( varinsubs x sub)) && isVariable (head (varinsubs x sub)) = unifyingsinglevariable (head (varinsubs x sub)) b sub
                                            | not( null( varinsubs x sub)) && not (isVariable (head (varinsubs x sub))) && varinsubs x sub == [b] = Just sub
                                            | not( null( varinsubs x sub)) && not (isVariable (head (varinsubs x sub))) && varinsubs x sub /= [b] = Nothing
                                            | not( null( varinsubs x sub)) && varinsubs x sub /= [b] = Nothing
                                            | null( varinsubs x sub) && not (variableinterm x b) = Just (sub ++ [(x, b)])
                                            | null( varinsubs x sub) && variableinterm x b = Just sub
                                            | otherwise = Nothing

unifyingvariables :: Term -> Term -> [(Term, Term)] -> Maybe [(Term, Term)]
unifyingvariables x@(Variable a) y@(Variable b) sub | not( null( varinsubs x sub)) && null( varinsubs y sub) = Just (sub ++ [(y, x)])
                                                    | null( varinsubs x sub) && not( null( varinsubs y sub)) = Just (sub ++ [(x, y)])
                                                    | otherwise = Just (sub ++ [(x, y)])

isVariable :: Term -> Bool
isVariable (Variable a) = True
isVariable a = False

variableinterm :: Term -> Term -> Bool
variableinterm x@(Variable a) (Compound b c) = variableinlistofterms x c
variableinterm x@(Variable a) b | x == b = True
                                | otherwise = False

variableinlistofterms :: Term -> [Term] -> Bool
variableinlistofterms x@(Variable a) [] = False
variableinlistofterms x@(Variable a) (b : bs) | x == b = True
                                              | otherwise = variableinterm x b



-- >>> unifyingqpredicates (Predicate (Atom "edge") [Variable "X", Variable "X"]) (Predicate (Atom "edge") [Variable "Y", Atom "b"]) []
-- Just [(Variable "X",Variable "Y"),(Variable "Y",Atom "b")]

-- will checking if the subs given are in the resulting subs prove if it fails or not
-- we will be using unification only when a query or rule likely has a variable in it.
-- prdicate on left is query predicate and predicate on right is rule predicate
-- case of query having variable, with no subs if you get [] then it has failed
--                                with subs, if the variable isnt in query then there will be more subs than before and so the variables given dont apply so you would just keep them and then 
--unification :: Predicate -> Predicate -> [[(Term, Term)]] -> [[(Term, Term)]]
--unification (Predicate a b) (Predicate c d) [] | a == c = [unifyterms b d []]
--                                               | otherwise = []
--unification x@(Predicate a b) y@(Predicate c d) (sub : subs) | a == c = unifyterms b d sub : unification x y subs
--                                                         | otherwise = []

--checksubs :: [(Term,Term)] -> [(Term,Term)] -> [(Term,Term)]

-- >>> unification (Predicate (Atom "hello") [Compound (Atom "hey") [Variable "X"],Variable "Y"]) (Predicate (Atom "hello") [Compound (Atom "hey") [Atom "this"], Atom "hola"]) [(Variable "X", Atom "this")]
-- [(Variable "X",Atom "this"),(Variable "Y",Atom "hola")]

-- >>> unification (Predicate (Atom "a") [Variable "X", Variable "X"]) (Predicate (Atom "a") [Variable "Y", Atom "b"]) []
-- [[(Variable "X",Variable "Y"),(Variable "Y",Atom "b")]]

-- >>> unifyterms [Atom "hey", Variable "X"] [Variable "Y", Variable "Z"] []
-- [(Variable "Y",Atom "hey"),(Variable "X",Variable "Z")]

--unifyterms :: [Term] -> [Term] -> [(Term, Term)] -> [(Term, Term)]
--unifyterms :: [Term] -> [Term] -> [(Term, Term)] -> [(Term, Term)]
--unifyterms [] [] subs = subs
--unifyterms x [] subs = []
--unifyterms [] x subs = []
--unifyterms (a : as) (b : bs) subs | a == b && length as == length bs = unifyterms as bs subs -- basically checking if they are the same, doesnt take into account them being a variable
--                                  | isvariable a b && length as == length bs = unifyterms as bs (unifyterm a b subs) -- this is if they arent the same but one or both of them have a variable in them
--                                  | otherwise = []

--unifyterm :: Term -> Term -> [(Term, Term)] -> [(Term, Term)]
--unifyterm (Atom a) (Atom b) subs | Atom a == Atom b = subs -- if theyre atoms
--                                 | otherwise = []
--unifyterm (String a) (String b) subs | String a == String b = subs -- if theyre string
--                                     | otherwise = []
--unifyterm (Variable a) (Variable b) subs | Variable a == Variable b = subs -- if theyre both the same variable
--                                         | otherwise = subs ++ [(Variable a, Variable b)] -- if theyre not the same variable what should i do?
--unifyterm (Variable a) x subs | notin (Variable a) x = unifyvar (Variable a) x subs-- if the query has a variable in it and the term its being unified with doesnt have the same variable in it,
--                              | otherwise = []
--unifyterm x (Variable a) subs | notin (Variable a) x = unifyvar (Variable a) x subs -- in the case that the query doesnt have a variable and the rule does.
--                              | otherwise = []
--unifyterm (Compound a b) (Compound c d) subs | a == c = unifyterms b d subs
--                                             | otherwise = []

-- >>> unifyterms [Compound (Atom "hey") [Variable "X"]] [Compound (Atom "hey") [Atom "sup"]] []
-- [(Variable "X",Atom "sup")]

--unifyvar :: Term -> Term -> [(Term, Term)] -> [(Term, Term)]
--unifyvar (Variable a) b subs | not (null (varinsubs (Variable a) subs)) = unifyterm (getsub (Variable a) subs) b subs -- if the variable is in the list of subs then make the sub and see if it still holds,
--
--                             | otherwise = subs ++ [(Variable a, b)]-- if it isnt in the list of subs then add the sub to the list of terms

--getsub :: Term -> [(Term, Term)] -> Term
--getsub (Variable a) ((b, c) : xs) | Variable a == b = c
--                                  | otherwise = getsub (Variable a) xs


-- >>> varinsubs (Variable "X") [(Variable "Y", Atom "hey"), (Variable "X", Atom "hey")]
-- True

--notin :: Term -> Term -> Bool
--notin (Variable a) (Compound b c) = null ([True | x <- c, not (notin (Variable a) x)])
--notin (Variable a) b | Variable a == b = False
--                     | otherwise = True


-- >>> notin (Variable "X") (Compound (Atom "ga") [Variable "X"])
-- False

-- >>> hasvariable [Atom "help", Variable "X", (Compound (Atom "hey") [Variable "Y", Compound (Atom "sup") [Variable "Z"], Compound (Atom "sup") [Variable "A"]])]
-- [Variable "X",Variable "Y",Variable "Z",Variable "A"]

-- >>> resolution [Predicate (Atom "hello") [Atom "help"]]
-- No instance for (Show ([Logic] -> Int))
--   arising from a use of ‘evalPrint’
--   (maybe you haven't applied a function to enough arguments?)

-- >>> basicq (runParser logicparser "p(zero)?\np(zero).\np(zero)?\n\np(one,two,three)?\np(zero)?")
-- /home/vscode/logic/src/Main.hs:(424,1)-(428,49): Non-exhaustive patterns in function eval

-- >>> basicqhelp (reverse [Rule [Predicate (Atom "hello") [Atom "help"]], Query [Predicate (Atom "hello") [Atom "help"]]])
-- "Yes."

-- >>> printlistlogic [Rule [Predicate (Atom "hello") [Atom "help"]], Query [Predicate (Atom "hello") [Atom "help"]]]
-- "hello(help).\nhello(help)?\n"

-- >>> printlistpredicate [Predicate (Atom "hello") [Atom "help"], Predicate (Atom "welp") [Atom "again"]]
-- "hello(help), welp(again)"

-- >>> runParser comment "% a small arithmetic grammar\n\n% variables, only 3 pre-defined ones allowed...\nlang"
-- [("% a small arithmetic grammar% variables, only 3 pre-defined ones allowed...","lang")]

-- >>> runParser logicparser "% a small arithmetic grammar\n\n% variables, only 3 pre-defined ones allowed...\nlang(v(\"x\")).\nlang(v(\"y\")).\nlang(v(\"z\"))."
-- [([Rule [Predicate (Atom "lang") [Compound (Atom "v") [String "\"x\""]]],Rule [Predicate (Atom "lang") [Compound (Atom "v") [String "\"y\""]]],Rule [Predicate (Atom "lang") [Compound (Atom "v") [String "\"z\""]]]],"")]

-- >>> runParser logicparser "lang(v(\"x\")).\nlang(v(\"y\")).\nlang(v(\"z\"))."
-- [([Rule [Predicate (Atom "lang") [Compound (Atom "v") [String "\"x\""]]],Rule [Predicate (Atom "lang") [Compound (Atom "v") [String "\"y\""]]],Rule [Predicate (Atom "lang") [Compound (Atom "v") [String "\"z\""]]]],"")]

-- >>> runParser comment "% a small arithmetic grammar\n\n% variables, only 3 pre-defined ones allowed...\nlang"
-- [("% a small arithmetic grammar% variables, only 3 pre-defined ones allowed...","lang")]

-- >>> printlogic (runParser logicparser "p(zero)?\np(zero).\np(zero)?")
-- "p(zero)?\np(zero).\np(zero)?\n"

-- >>> printpredicate (Predicate (Atom "edge") [Atom "b",Atom "a"])
-- "edge(b, a)"

-- >>> printterm (Compound (Atom "help") [Atom "here", Atom "there"])
-- "help(here, there)"

-- >>> printlogic (runParser logicparser "addn(1,2,3)?\naddn(1,2,4)?\n")
-- "addn(succ(zero), succ(succ(zero)), succ(succ(succ(zero))))?\naddn(succ(zero), succ(succ(zero)), succ(succ(succ(succ(zero)))))?\n"

-- >>> runParser logicparser "multn(4,2,8)?\n% multn(5,3,X)?\n% multn(3,5,X)?\n% multn(3,X,12)?\n% multn(X,6,18)?"
-- [([Query [Predicate (Atom "multn") [Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Atom "zero"]]]],Compound (Atom "succ") [Compound (Atom "succ") [Atom "zero"]],Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Compound (Atom "succ") [Atom "zero"]]]]]]]]]]],"")]

-- >>> typeOf (runParser logicparser "edge( a , b ).\n%this is a test\n\n\n\nedge(c,d)?\n\n\n\n\n")
-- Variable not in scope: typeOf :: [([Logic], String)] -> t

-- >>> runParser logicparser "p(\"eh\"\n, \"bee\", \n\n\"another string\"\n\n\n)\n\n."
-- [([Rule [Predicate (Atom "p") [String "\"eh\"",String "\"bee\"",String "\"another string\""]]],"")]

-- >>> runParser (token comment) "\n%this is a test\n\n\n\nedge"
-- [("%this is a test","edge")]

-- >>> runParser logicparser "parent(lee, virginia).\nparent(lee, bob).\nparent(lee, suzy).\nparent(virginia, garrett).\nparent(bob, robby).\nparent(suzy, chris).\nparent(suzy, jamie).\nparent(lee, bob)?\nparent(suzy, chris)?\nparent(suzy, bob)?"
-- [([Rule [Predicate (Atom "parent") [Atom "lee",Atom "virginia"]],Rule [Predicate (Atom "parent") [Atom "lee",Atom "bob"]],Rule [Predicate (Atom "parent") [Atom "lee",Atom "suzy"]],Rule [Predicate (Atom "parent") [Atom "virginia",Atom "garrett"]],Rule [Predicate (Atom "parent") [Atom "bob",Atom "robby"]],Rule [Predicate (Atom "parent") [Atom "suzy",Atom "chris"]],Rule [Predicate (Atom "parent") [Atom "suzy",Atom "jamie"]],Query [Predicate (Atom "parent") [Atom "lee",Atom "bob"]],Query [Predicate (Atom "parent") [Atom "suzy",Atom "chris"]],Query [Predicate (Atom "parent") [Atom "suzy",Atom "bob"]]],"")]

-- >>> runParser (allnewl) "\n\n\n"
-- [("\n\n\n","")]

-- >>> runParser (token comment) "   % hello test\n\n\n"
-- [("%hellotest\n\n\n","")]

-- >>> printlistpredicate (runParser predicate "edge(b,a)")
-- Couldn't match type ‘[Predicate]’ with ‘Predicate’
-- Expected type: [(Predicate, String)]
--   Actual type: [([Predicate], String)]

-- >>> runParser atom "edge(a,e)"
-- [(Atom "edge","(a,e)")]

-- >>> runParser variable "Body"
-- [(Variable "Body","")]

-- >>> runParser string1 "\"hello"
-- [(String "\"hello","")]

-- >>> runParser (option "" comment) "avc"
-- [("","avc")]

-- >>> Logic Q

-- >>> runParser allchar "a"
-- []


-- >>> runParser (token predicate) "help(1), help(2), help(c)"
-- [([Predicate (Atom "help") [Compound (Atom "succ") [Atom "zero"]],Predicate (Atom "help") [Compound (Atom "succ") [Compound (Atom "succ") [Atom "zero"]]],Predicate (Atom "help") [Atom "c"]],"")]

-- >>> runParser predicate "x(comp(a,b),H)"
-- [([Predicate (Atom "x") [Compound (Atom "comp") [Atom "a",Atom "b"],Variable "H"]],"")]

-- >>> printlistterm (runParser compound "bca(a)")
-- "bca(a)"

-- >>> runParser middlecomp "bca(a)"
-- [([Compound (Atom "bca") [Atom "a"]],"")]

-- >>> runParser allLetter "\n\n\nedge"
-- [("edge","")]

-- >>> runParser comment "%this is a comment\n\n\n\n\n%hello\n\n\n\n%youthere\n"
-- [("%this is a comment%hello%youthere","")]


-- >>> runParser allnotnewl "agsdfasdcvasdvasd\n"
-- [("agsdfasdcvasdvasd","\n")]


-- >>> runParser rulething ":-"
-- [(":-","")]


-- >>> runParser compound "a(1,v)"
-- [(Compound (Atom "a") [Compound (Atom "succ") [Atom "zero"],Atom "v"],"")]

-- >>> runParser string1 "\"hello\""
-- [(String "\"hello\"","")]

-- >>> runParser atom "abc"
-- [(Atom "abc","")]

-- >>> runParser openp "("
-- [('(',"")]

-- >>> runParser middlecomp "a"
-- [([Atom "a"],"")]


-- >>> runParser nat "123"
-- [(123,"")]


-- >>> runParser logicparser "%this is comment\nedge( a , b ).\nedge(c,d)?"
-- [([],"%this is comment\nedge( a , b ).\nedge(c,d)?")]


-- >>> runParser string1 "\"hello234$#$@#{}<>?/.,[]2adfga\""
-- [(String "\"hello234$#$@#{}<>?/.,[]2adfga\"","")]


-- >>> runParser allchar "#$$#$%#>?:{|};./112321fadsfa1234"
-- [("#$$#$%#>?:{|};./112321fadsfa1234","")]


-- >>> desugl [Atom "hello", Atom "goodbye"]
-- Compound (Atom "cons") [Atom "hello",Compound (Atom "cons") [Atom "goodbye",Atom "nil"]]

-- >>> desuglp [Atom "hello", Atom "goodbye"]
-- Compound (Atom "cons") [Atom "hello",Atom "goodbye"]

-- >>> runParser desuglist "[hello]"
-- [(Compound (Atom "cons") [Atom "hello",Atom "nil"],"")]
