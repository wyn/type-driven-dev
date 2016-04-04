module Printf

data Format = Number Format
            | DNumber Format
            | Str Format
            | CharFmt Format
            | Lit String Format
            | End
            
PrintfType : Format -> Type            
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (DNumber fmt) = (d : Double) -> PrintfType fmt
PrintfType (Str fmt) = (s : String) -> PrintfType fmt
PrintfType (CharFmt fmt) = (c : Char) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (DNumber fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (CharFmt fmt) acc = \c => printfFmt fmt (acc ++ show c)
printfFmt (Lit str fmt) acc = printfFmt fmt (acc ++ str)
printfFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 'f' :: chars) = DNumber (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = CharFmt (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             Lit lit chars' => Lit (strCons c lit) chars'
                             fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))  
printf fmt = printfFmt (toFormat (unpack fmt)) ""
