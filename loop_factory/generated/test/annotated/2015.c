int main1(){
  int oesp, ozu, ai0, m;
  oesp=1+3;
  ozu=0;
  ai0=0;
  m=ozu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ozu;
  loop invariant ozu <= oesp;
  loop invariant ai0 >= 0;
  loop invariant m - ai0 >= ozu;
  loop invariant oesp == 4;
  loop invariant (ozu <= oesp/2) ==> (ai0 == 0 && m == ozu);
  loop assigns ai0, m, ozu;
*/
while (ozu < oesp) {
      if (!(!(ozu >= oesp/2))) {
          ai0 = ai0 + m;
      }
      m += ai0;
      ozu += 1;
      m++;
  }
}