-- Graziele Fagundes e João Vitor Farias

-- Definição das árvore sintática para representação dos programas:
data E = Num Int
      |Var String
      |Soma E E
      |Mult E E
      |Sub E E
   deriving(Eq,Show)

data B = TRUE
      | FALSE
      | Not B
      | And B B
      | Or  B B
      | Leq E E
      | Igual E E
   deriving(Eq,Show)

data C = While B C
    | If B C C
    | Seq C C
    | Atrib E E
    | Skip
    | Twice C 
    | RepeatUntil C B
    | ExecN C E
    | Assert B C
    | Swap E E
    | DAtrrib E E E E
   deriving(Eq,Show)   


-- Definição do estado da memória
type Memoria = [(String,Int)]

procuraVar :: Memoria -> String -> Int
procuraVar [] s = error ("Variavel " ++ s ++ " nao definida no estado")
procuraVar ((s,i):xs) v
  | s == v     = i
  | otherwise  = procuraVar xs v

mudaVar :: Memoria -> String -> Int -> Memoria
mudaVar [] v n = error ("Variavel " ++ v ++ " nao definida no estado")
mudaVar ((s,i):xs) v n
  | s == v     = ((s,n):xs)
  | otherwise  = (s,i): mudaVar xs v n



-- Semântica Operacional Small-Step para Expressões Aritméticas
smallStepE :: (E, Memoria) -> (E, Memoria)
smallStepE (Var x, s)                  = (Num (procuraVar s x), s)

smallStepE (Soma (Num n1) (Num n2), s) = (Num (n1 + n2), s)
smallStepE (Soma (Num n) e, s)         = let (el,sl) = smallStepE (e,s)
                                         in (Soma (Num n) el, sl)
smallStepE (Soma e1 e2,s)              = let (el,sl) = smallStepE (e1,s)
                                         in (Soma el e2,sl)

smallStepE (Mult (Num n1) (Num n2), s) = (Num (n1 * n2), s)
smallStepE (Mult (Num n) e, s)         = let (el,sl) = smallStepE (e,s)
                                         in (Mult (Num n) el, sl)
smallStepE (Mult e1 e2,s)              = let (el,sl) = smallStepE (e1,s)
                                         in (Mult el e2,sl)

smallStepE (Sub (Num n1) (Num n2), s) = (Num (n1 - n2), s)
smallStepE (Sub (Num n) e, s)         = let (el, sl) = smallStepE (e, s)
                                        in (Sub (Num n) el, sl)
smallStepE (Sub e1 e2, s)             = let (el, sl) = smallStepE (e1, s)
                                        in (Sub el e2, sl)

-- Semântica Operacional Small-Step para Expressões Booleanas
smallStepB :: (B,Memoria) -> (B, Memoria)
smallStepB (Not TRUE, s)     = (FALSE, s)
smallStepB (Not FALSE, s)    = (TRUE, s)
smallStepB (Not b,s)        = let (bl,sl) = smallStepB(b, s)
                              in (Not bl,sl)

smallStepB (And TRUE b, s)   = (b, s)
smallStepB (And FALSE b, s)  = (FALSE, s)
smallStepB (And b1 b2, s)    = let (bl, sl) = smallStepB (b1, s)
                                in (And bl b2, sl)

smallStepB (Or TRUE b, s)    = (TRUE, s)
smallStepB (Or FALSE b, s)   = (b, s)
smallStepB (Or b1 b2, s)     = let (bl, sl) = smallStepB (b1, s)
                                in (Or bl b2, sl)

smallStepB (Leq (Num n1) (Num n2), s) = (if n1 <= n2 then TRUE else FALSE, s)
                                              
smallStepB (Leq (Num n) e, s) = let (el, sl) = smallStepE (e, s)
                                in (Leq (Num n) el, sl)
smallStepB (Leq e1 e2, s)    = let (el, sl) = smallStepE (e1, s)
                                in (Leq el e2, sl)
                                
smallStepB (Igual (Num n1) (Num n2), s) = (if n1 == n2 then TRUE else FALSE, s)
smallStepB (Igual (Num n) e, s) = let (el, sl) = smallStepE (e, s)
                                  in (Igual (Num n) el, sl)
smallStepB (Igual e1 e2, s)  = let (el, sl) = smallStepE (e1, s)
                                  in (Igual el e2, sl)

-- Semântica Operacional Small-Step para Comandos
smallStepC :: (C,Memoria) -> (C,Memoria)
smallStepC (If TRUE c1 c2, s) = smallStepC (c1, s)
smallStepC (If FALSE c1 c2, s) = smallStepC (c2, s)
smallStepC (If b c1 c2, s) = let (bl, sl) = smallStepB (b, s)
                in (If bl c1 c2, sl)

smallStepC (Seq Skip c2, s) = (c2, s)
smallStepC (Seq c1 c2, s)   = let (c1', s') = smallStepC (c1, s)
                in (Seq c1' c2, s') 

smallStepC (Atrib (Var x) (Num n), s) = (Skip, mudaVar s x n)
smallStepC (Atrib (Var x) e,s) = let (e1, s1) = smallStepE (e, s)
                                  in (Atrib (Var x) e1, s1)

smallStepC (While b c, s) = (If b (Seq c (While b c)) Skip, s)

smallStepC (Skip, s) = (Skip, s)

smallStepC (Twice c, s) = (Seq c (Seq c Skip), s)

smallStepC (RepeatUntil c b, s) = (Seq c (If b Skip (RepeatUntil c b)), s)

smallStepC (ExecN c (Num 0), s) = (Skip, s)
smallStepC (ExecN c (Num n), s) = (Seq c (ExecN c (Num (n - 1))), s)
smallStepC (ExecN c e, s) = let (e', s') = smallStepE (e, s)
                            in (ExecN c e', s')

smallStepC (Assert FALSE c, s) = (Skip, s)
smallStepC (Assert TRUE c, s) = smallStepC (c, s)
smallStepC (Assert b c, s) = let (b', s') = smallStepB (b, s)
                             in (Assert b' c, s')

smallStepC (Swap (Var x) (Var y), s) = let n1 = procuraVar s x
                                           n2 = procuraVar s y
                                       in (Seq (Atrib (Var x) (Num n2)) (Atrib (Var y) (Num n1)), s)

smallStepC (DAtrrib (Var x1) (Var x2) (Num n1) (Num n2), s) = (Skip, mudaVar (mudaVar s x1 n1) x2 n2)
smallStepC (DAtrrib (Var x1) (Var x2) (Num n1) e2, s) = let (e2', s2) = smallStepE (e2, s)
                                                        in (DAtrrib (Var x1) (Var x2) (Num n1) e2', s)
smallStepC (DAtrrib (Var x1) (Var x2) e1 e2, s) = let (e1', s1) = smallStepE (e1, s)
                                                  in (DAtrrib (Var x1) (Var x2) e1' e2, s)

----------------------
--  INTERPRETADORES
----------------------

--- Interpretador para Expressões Aritméticas:
isFinalE :: E -> Bool
isFinalE (Num n) = True
isFinalE _       = False

interpretadorE :: (E,Memoria) -> (E, Memoria)
interpretadorE (e,s) = if (isFinalE e) then (e,s) else interpretadorE (smallStepE (e,s))

--- Interpretador para expressões booleanas
isFinalB :: B -> Bool
isFinalB TRUE    = True
isFinalB FALSE   = True
isFinalB _       = False

interpretadorB :: (B,Memoria) -> (B, Memoria)
interpretadorB (b,s) = if (isFinalB b) then (b,s) else interpretadorB (smallStepB (b,s))

-- Interpretador da Linguagem Imperativa
isFinalC :: C -> Bool
isFinalC Skip    = True
isFinalC _       = False

interpretadorC :: (C,Memoria) -> (C, Memoria)
interpretadorC (c,s) = if (isFinalC c) then (c,s) else interpretadorC (smallStepC (c,s))


----------------------
--  EXEMPLOS
----------------------

-- Como rodar: interpretadorC (fatorial, exSigma)

exSigma :: Memoria
exSigma = [ ("x", 10), ("temp",0), ("y",0)]

exSigma2 :: Memoria
exSigma2 = [("x",3), ("y",0), ("z",0)]


progExp1 :: E
progExp1 = Soma (Num 3) (Soma (Var "x") (Var "y"))

teste1 :: B
teste1 = (Leq (Soma (Num 3) (Num 3))  (Mult (Num 2) (Num 3)))

teste2 :: B
teste2 = (Leq (Soma (Var "x") (Num 3))  (Mult (Num 2) (Num 3)))

testec1 :: C
testec1 = (Seq (Seq (Atrib (Var "z") (Var "x")) (Atrib (Var "x") (Var "y"))) 
               (Atrib (Var "y") (Var "z")))


fatorial :: C
fatorial = (Seq (Atrib (Var "y") (Num 1))
                (While (Not (Igual (Var "x") (Num 1)))
                       (Seq (Atrib (Var "y") (Mult (Var "y") (Var "x")))
                            (Atrib (Var "x") (Sub (Var "x") (Num 1))))))


-- Programas criados para teste
progRepeatUntil :: C
progRepeatUntil = RepeatUntil (Atrib (Var "x") (Soma (Var "x") (Num 1))) 
                              (Leq (Num 10) (Var "x"))

progExecN :: C
progExecN = ExecN (Atrib (Var "x") (Soma (Var "x") (Num 1))) (Num 5)

progAssert :: C
progAssert = Assert (Leq (Var "x") (Num 10)) 
                    (Atrib (Var "x") (Mult (Var "x") (Num 2)))

progSwap :: C
progSwap = Swap (Var "x") (Var "y")

progDAtrrib :: C
progDAtrrib = DAtrrib (Var "x") (Var "y") (Soma (Var "x") (Num 1)) (Soma (Var "y") (Num 2))
