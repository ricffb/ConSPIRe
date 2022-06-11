import Prelude (Maybe(..), Int, ($), snd, Show, id)

data L_MSG = Nil | Cons MSG L_MSG
    deriving(Show)

data MSG = Enc Int MSG | Nonce Int | Sq L_MSG
    deriving(Show)

data L_MSG_T = TNil | TCons MSG_T_CONT L_MSG_T
    deriving(Show)

data L_MSG_TT = TTNil | TTCons MSG_T_CONT L_MSG
    deriving(Show)

type MSG_T_CONT = ([(Int, MSG)], MSG)

data MSG_T = TEnc Int MSG_T_CONT | TNonce Int | TSq L_MSG_T
    deriving(Show)

dual = id


foldLT :: L_MSG_T -> (L_MSG_TT -> L_MSG) -> L_MSG
foldLT TNil f = f TTNil
foldLT (TCons msg ls) f = f (TTCons msg (foldLT ls f))

foldMSG :: MSG -> (MSG_T -> MSG_T_CONT) -> MSG_T_CONT
foldMSG (Nonce i) f = f $ TNonce i 
foldMSG (Enc i m) f = f $ TEnc i (foldMSG m f)
foldMSG (Sq ms)   f = f $ TSq msf
    where
        foldC (Cons m ls) = TCons (foldMSG m f) (foldC ls)
        foldC Nil         = TNil
        msf = foldC ms

caseSplitEnc :: MSG_T -> MSG_T_CONT
caseSplitEnc m = case m of 
    TEnc i (_, msg) -> ([(i, msg)], Enc i msg)
    TNonce i -> ([], Nonce i)
    TSq ms -> ([], Sq $ foldLT ms sndPick)

sndPick :: L_MSG_TT -> L_MSG
sndPick TTNil = Nil
sndPick (TTCons m ls) = Cons (snd m) ls

nonce = Nonce 1
sq = Sq (Cons (Enc 2 nonce) (Cons (Nonce 2) Nil))
e1 = Enc 1 sq


