-- Graziele Fagundes Martins - 21201339
-- João Vitor Farias - 21201501

-- Tipos
data E = Num Int
      |Var String
      |Soma E E
      |Sub E E
      |Mult E E
      |Div E E
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
    | DoWhile B C
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


-- Memória
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


-- Semântica de Expressões Aritméticas
ebigStep :: (E,Memoria) -> Int
ebigStep (Var x,s) = procuraVar s x
ebigStep (Num n,s) = n
ebigStep (Soma e1 e2,s)  = ebigStep (e1,s) + ebigStep (e2,s)
ebigStep (Sub e1 e2,s)   = ebigStep (e1,s) - ebigStep (e2,s)
ebigStep (Mult e1 e2,s)  = ebigStep (e1,s) * ebigStep (e2,s)
ebigStep(Div e1 e2,s)    = ebigStep (e1,s) `div` ebigStep (e2,s)

-- Semântica de Expressões Booleanas
bbigStep :: (B,Memoria) -> Bool
bbigStep (TRUE,s)  = True
bbigStep (FALSE,s) = False
bbigStep (Not b,s) 
   | bbigStep (b,s) == True     = False
   | otherwise                  = True 
bbigStep (And b1 b2,s )
   | bbigStep(b1,s) == True     = bbigStep(b2,s)
   | otherwise                  = False
bbigStep (Or b1 b2,s )
   | bbigStep(b1,s) == True     = True
   | bbigStep(b1,s) == False    = bbigStep(b2,s)
bbigStep (Leq e1 e2,s) = ebigStep(e1,s) <= ebigStep(e2,s)
bbigStep (Igual e1 e2,s) = ebigStep(e1,s) == ebigStep(e2,s)

-- Semântica de Comandos
cbigStep :: (C,Memoria) -> (C,Memoria)
cbigStep (While b c,s) = 
   if bbigStep(b,s) == True then 
      let (c',s') = cbigStep(c,s) 
      in cbigStep(While b c,s') 
   else (Skip,s)
cbigStep (DoWhile b c,s) = 
   let (c',s') = cbigStep(c,s) 
   in if bbigStep(b,s') == True then cbigStep(DoWhile b c,s') else (Skip,s')
cbigStep (Skip,s) = (Skip,s)
cbigStep (If b c1 c2,s)
   | bbigStep(b,s) == True      = cbigStep(c1,s)
   | bbigStep(b,s) == False     = cbigStep(c2,s)           
cbigStep (Seq c1 c2,s) = 
   let (c1',s') = cbigStep(c1,s)
   in cbigStep(c2,s') 
cbigStep (Atrib (Var x) e,s) = (Skip, mudaVar s x (ebigStep(e,s)))
cbigStep (Twice c,s) =
   let (c',s') = cbigStep(c,s)
   in cbigStep(c,s')
cbigStep (RepeatUntil c b,s) =
   let (c',s') = cbigStep(c,s)
   in if bbigStep(b,s') == True then (Skip,s') else cbigStep(RepeatUntil c b,s')
cbigStep (ExecN c e,s) =
   if ebigStep(e,s) == 0 then (Skip,s) else let (c',s') = cbigStep(c,s) in cbigStep(ExecN c (Num (ebigStep(e,s)-1)),s')
cbigStep (Assert b c,s) =
   if bbigStep(b,s) == True then cbigStep(c,s) else (Skip, s)
cbigStep (Swap (Var x) (Var y),s) =
   let (valx, valy) = (procuraVar s x, procuraVar s y) in (Skip, mudaVar (mudaVar s x valy) y valx)
cbigStep (DAtrrib (Var x) (Var y) e1 e2,s) =
   (Skip, mudaVar (mudaVar s x (ebigStep(e1,s))) y (ebigStep(e2,s)))


-- Exemplos
exSigma :: Memoria
exSigma = [ ("x",4), ("temp",0), ("y",0)]
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

exemploLoop :: C
exemploLoop = (While (Leq (Var "x") (Num 10)) (Atrib (Var "x") (Soma (Var "x") (Num 1))))

exemploDuplaAtribuicao :: C
exemploDuplaAtribuicao = (DAtrrib (Var "x") (Var "y") (Num 3) (Num 4))

exemploDoWhile :: C
exemploDoWhile = (DoWhile (Leq (Var "x") (Num 10)) (Atrib (Var "x") (Soma (Var "x") (Num 1))))