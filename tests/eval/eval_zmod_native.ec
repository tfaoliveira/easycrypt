(* The native operations of ZModRing clones (pragma Eval:native_zmod)
   agree with their definitions: the same checks with and without the
   pragma (expected values from Python's integers). *)
require import AllCore IntDiv ZModP.

clone ZModField as Fq with op p <- 8380417 proof prime_p by admit.
clone ZModRing as R12 with op p <= 12 proof ge2_p by done.

pragma +Eval:native_zmod.
theory TFqN.
import Fq.
check asint (inzmod (-3409203)) = 4971214.
check asint (inzmod (-15017935)) = 1742899.
check asint (inzmod (1354905)) = 1354905.
check asint (inzmod (18542222)) = 1781388.
check asint (inzmod (-21900804)) = 3240447.
check asint (inzmod (-20280135)) = 4861116.
check asint (inzmod (10796558) + inzmod (1220382)) = 3636523.
check asint (inzmod (10796558) * inzmod (1220382)) = 7166497.
check asint (- inzmod (10796558)) = 5964276.
check asint (inzmod (10796558) - inzmod (1220382)) = 1195759.
check asint (inzmod (-13602354) + inzmod (-4490351)) = 7048546.
check asint (inzmod (-13602354) * inzmod (-4490351)) = 7068057.
check asint (- inzmod (-13602354)) = 5221937.
check asint (inzmod (-13602354) - inzmod (-4490351)) = 7648831.
check asint (inzmod (2794286) + inzmod (-14814714)) = 4740406.
check asint (inzmod (2794286) * inzmod (-14814714)) = 5181105.
check asint (- inzmod (2794286)) = 5586131.
check asint (inzmod (2794286) - inzmod (-14814714)) = 848166.
check asint (inzmod (13763769) + inzmod (265883)) = 5649235.
check asint (inzmod (13763769) * inzmod (265883)) = 77884.
check asint (- inzmod (13763769)) = 2997065.
check asint (inzmod (13763769) - inzmod (265883)) = 5117469.
check asint (inzmod (-9556759) + inzmod (-15502689)) = 81803.
check asint (inzmod (-9556759) * inzmod (-15502689)) = 6358278.
check asint (- inzmod (-9556759)) = 1176342.
check asint (inzmod (-9556759) - inzmod (-15502689)) = 5945930.
check asint (inzmod (-13876924) + inzmod (-2210100)) = 673810.
check asint (inzmod (-13876924) * inzmod (-2210100)) = 5038767.
check asint (- inzmod (-13876924)) = 5496507.
check asint (inzmod (-13876924) - inzmod (-2210100)) = 5094010.
check asint zero = 0.
check asint one = 1.
check asint (ZModpRing.exp (inzmod 3507882) 0) = 1.
check asint (ZModpRing.exp (inzmod 585989) 1) = 585989.
check asint (ZModpRing.exp (inzmod 2018827) 2) = 5875902.
check asint (ZModpRing.exp (inzmod 760955) 17) = 7505983.
check asint (ZModpRing.exp (inzmod 4622519) 8380416) = 1.
check asint (ZModpRing.exp (inzmod 3561125) 25141256) = 4786596.
check asint (ZModpRing.exp (inzmod 495855) (-1)) = 6869253.
check asint (ZModpRing.exp (inzmod 6936139) (-5)) = 30180.
end TFqN.

theory TR12N.
import R12.
check asint (inzmod (-21)) = 3.
check asint (inzmod (-8)) = 4.
check asint (inzmod (-29)) = 7.
check asint (inzmod (14)) = 2.
check asint (inzmod (-30)) = 6.
check asint (inzmod (-8)) = 4.
check asint (inzmod (-22) + inzmod (11)) = 1.
check asint (inzmod (-22) * inzmod (11)) = 10.
check asint (- inzmod (-22)) = 10.
check asint (inzmod (-22) - inzmod (11)) = 3.
check asint (inzmod (-16) + inzmod (-6)) = 2.
check asint (inzmod (-16) * inzmod (-6)) = 0.
check asint (- inzmod (-16)) = 4.
check asint (inzmod (-16) - inzmod (-6)) = 2.
check asint (inzmod (2) + inzmod (-15)) = 11.
check asint (inzmod (2) * inzmod (-15)) = 6.
check asint (- inzmod (2)) = 10.
check asint (inzmod (2) - inzmod (-15)) = 5.
check asint (inzmod (10) + inzmod (-17)) = 5.
check asint (inzmod (10) * inzmod (-17)) = 10.
check asint (- inzmod (10)) = 2.
check asint (inzmod (10) - inzmod (-17)) = 3.
check asint (inzmod (12) + inzmod (-5)) = 7.
check asint (inzmod (12) * inzmod (-5)) = 0.
check asint (- inzmod (12)) = 0.
check asint (inzmod (12) - inzmod (-5)) = 5.
check asint (inzmod (11) + inzmod (19)) = 6.
check asint (inzmod (11) * inzmod (19)) = 5.
check asint (- inzmod (11)) = 1.
check asint (inzmod (11) - inzmod (19)) = 4.
check asint zero = 0.
check asint one = 1.
check asint (ZModpRing.exp (inzmod 2) 0) = 1.
check asint (ZModpRing.exp (inzmod 1) 1) = 1.
check asint (ZModpRing.exp (inzmod 9) 2) = 9.
check asint (ZModpRing.exp (inzmod 9) 17) = 9.
check asint (ZModpRing.exp (inzmod 10) 11) = 4.
check asint (ZModpRing.exp (inzmod 3) 41) = 3.
end TR12N.

pragma -Eval:native_zmod.
theory TFqR.
import Fq.
check asint (inzmod (-3409203)) = 4971214.
check asint (inzmod (-15017935)) = 1742899.
check asint (inzmod (1354905)) = 1354905.
check asint (inzmod (18542222)) = 1781388.
check asint (inzmod (-21900804)) = 3240447.
check asint (inzmod (-20280135)) = 4861116.
check asint (inzmod (10796558) + inzmod (1220382)) = 3636523.
check asint (inzmod (10796558) * inzmod (1220382)) = 7166497.
check asint (- inzmod (10796558)) = 5964276.
check asint (inzmod (10796558) - inzmod (1220382)) = 1195759.
check asint (inzmod (-13602354) + inzmod (-4490351)) = 7048546.
check asint (inzmod (-13602354) * inzmod (-4490351)) = 7068057.
check asint (- inzmod (-13602354)) = 5221937.
check asint (inzmod (-13602354) - inzmod (-4490351)) = 7648831.
check asint (inzmod (2794286) + inzmod (-14814714)) = 4740406.
check asint (inzmod (2794286) * inzmod (-14814714)) = 5181105.
check asint (- inzmod (2794286)) = 5586131.
check asint (inzmod (2794286) - inzmod (-14814714)) = 848166.
check asint (inzmod (13763769) + inzmod (265883)) = 5649235.
check asint (inzmod (13763769) * inzmod (265883)) = 77884.
check asint (- inzmod (13763769)) = 2997065.
check asint (inzmod (13763769) - inzmod (265883)) = 5117469.
check asint (inzmod (-9556759) + inzmod (-15502689)) = 81803.
check asint (inzmod (-9556759) * inzmod (-15502689)) = 6358278.
check asint (- inzmod (-9556759)) = 1176342.
check asint (inzmod (-9556759) - inzmod (-15502689)) = 5945930.
check asint (inzmod (-13876924) + inzmod (-2210100)) = 673810.
check asint (inzmod (-13876924) * inzmod (-2210100)) = 5038767.
check asint (- inzmod (-13876924)) = 5496507.
check asint (inzmod (-13876924) - inzmod (-2210100)) = 5094010.
check asint zero = 0.
check asint one = 1.
check asint (ZModpRing.exp (inzmod 3507882) 0) = 1.
check asint (ZModpRing.exp (inzmod 585989) 1) = 585989.
check asint (ZModpRing.exp (inzmod 2018827) 2) = 5875902.
check asint (ZModpRing.exp (inzmod 760955) 17) = 7505983.
check asint (ZModpRing.exp (inzmod 4622519) 8380416) = 1.
check asint (ZModpRing.exp (inzmod 3561125) 25141256) = 4786596.
check asint (ZModpRing.exp (inzmod 495855) (-1)) = 6869253.
check asint (ZModpRing.exp (inzmod 6936139) (-5)) = 30180.
end TFqR.

theory TR12R.
import R12.
check asint (inzmod (-21)) = 3.
check asint (inzmod (-8)) = 4.
check asint (inzmod (-29)) = 7.
check asint (inzmod (14)) = 2.
check asint (inzmod (-30)) = 6.
check asint (inzmod (-8)) = 4.
check asint (inzmod (-22) + inzmod (11)) = 1.
check asint (inzmod (-22) * inzmod (11)) = 10.
check asint (- inzmod (-22)) = 10.
check asint (inzmod (-22) - inzmod (11)) = 3.
check asint (inzmod (-16) + inzmod (-6)) = 2.
check asint (inzmod (-16) * inzmod (-6)) = 0.
check asint (- inzmod (-16)) = 4.
check asint (inzmod (-16) - inzmod (-6)) = 2.
check asint (inzmod (2) + inzmod (-15)) = 11.
check asint (inzmod (2) * inzmod (-15)) = 6.
check asint (- inzmod (2)) = 10.
check asint (inzmod (2) - inzmod (-15)) = 5.
check asint (inzmod (10) + inzmod (-17)) = 5.
check asint (inzmod (10) * inzmod (-17)) = 10.
check asint (- inzmod (10)) = 2.
check asint (inzmod (10) - inzmod (-17)) = 3.
check asint (inzmod (12) + inzmod (-5)) = 7.
check asint (inzmod (12) * inzmod (-5)) = 0.
check asint (- inzmod (12)) = 0.
check asint (inzmod (12) - inzmod (-5)) = 5.
check asint (inzmod (11) + inzmod (19)) = 6.
check asint (inzmod (11) * inzmod (19)) = 5.
check asint (- inzmod (11)) = 1.
check asint (inzmod (11) - inzmod (19)) = 4.
check asint zero = 0.
check asint one = 1.
check asint (ZModpRing.exp (inzmod 2) 0) = 1.
check asint (ZModpRing.exp (inzmod 1) 1) = 1.
check asint (ZModpRing.exp (inzmod 9) 2) = 9.
check asint (ZModpRing.exp (inzmod 9) 17) = 9.
check asint (ZModpRing.exp (inzmod 10) 11) = 4.
check asint (ZModpRing.exp (inzmod 3) 41) = 3.
end TR12R.
