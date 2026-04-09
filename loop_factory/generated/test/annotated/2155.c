int main1(int l){
  int g4p, pon, jg4, v3, sun;
  g4p=l+9;
  pon=0;
  jg4=0;
  v3=g4p;
  sun=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g4p == \at(l, Pre) + 9;
  loop invariant sun == \at(l, Pre);
  loop invariant (pon == 0) || (pon == g4p);
  loop invariant (pon == 0) ==> (jg4 == 0 && v3 == g4p && l == \at(l, Pre));
  loop invariant 0 <= pon;
  loop invariant (pon == g4p) ==> ((jg4 == 0 && v3 == g4p) || (jg4 == g4p && v3 == l));
  loop assigns l, jg4, v3, pon;
*/
while (pon < g4p) {
      l = l+g4p-pon;
      jg4 = (pon++, jg4 + v3);
      v3 += sun;
      pon = g4p;
  }
}