int main1(){
  int qf, sk, hs8, qwo, trp, wk;
  qf=1+12;
  sk=1;
  hs8=0;
  qwo=1;
  trp=1;
  wk=sk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant trp == 1 + 2*hs8;
  loop invariant qwo == (hs8 + 1) * (hs8 + 1);
  loop invariant wk  == (hs8 + 1) * (hs8 + 1);
  loop invariant hs8 >= 0;
  loop assigns hs8, trp, qwo, wk;
*/
while (1) {
      if (!(qwo<=qf)) {
          break;
      }
      hs8 += 1;
      trp += 2;
      qwo += trp;
      wk += trp;
  }
}