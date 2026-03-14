int main1(){
  int xxl4, f0d, w9;
  xxl4=22;
  f0d=0;
  w9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f0d == 0 || f0d == 2 || f0d == 6 || f0d == 14;
  loop invariant (w9 == 0 ==> f0d == 0) &&
                    (w9 == 1 ==> f0d == 2) &&
                    (w9 == 2 ==> f0d == 6) &&
                    (w9 >= 3 ==> f0d == 14);
  loop invariant 0 <= w9 <= xxl4;
  loop invariant ((w9 == 0) ==> (f0d == 0)) &&
                 ((w9 == 1) ==> (f0d == 2)) &&
                 ((w9 == 2) ==> (f0d == 6)) &&
                 ((w9 >= 3) ==> (f0d == 14));
  loop invariant ((w9 == 0 && f0d == 0) ||
                  (w9 == 1 && f0d == 2) ||
                  (w9 == 2 && f0d == 6) ||
                  (w9 >= 3 && f0d == 14));
  loop assigns w9, f0d;
*/
while (w9<xxl4) {
      w9 += 1;
      f0d = (f0d+1)%8;
      f0d += f0d;
  }
}