int main1(){
  int ik, c5, jdr, p, oo;
  ik=0;
  c5=(1%28)+8;
  jdr=(1%22)+5;
  p=0;
  oo=ik;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= oo < 6;
  loop invariant 0 <= p;
  loop invariant p <= 54;
  loop invariant 9 <= c5;
  loop invariant c5 <= 72;
  loop invariant ik == 0;
  loop invariant 0 <= jdr <= 6;
  loop invariant (
       (jdr == 6 && c5 == 9 && p == 0 && oo == 0) ||
       (jdr == 3 && c5 == 18 && p == 0 && oo == 3) ||
       (jdr == 1 && c5 == 36 && p == 18 && oo == 4) ||
       (jdr == 0 && c5 == 72 && p == 54 && oo == 4)
  );
  loop invariant (c5 % 9 == 0);
  loop assigns p, c5, jdr, oo;
*/
while (jdr!=0) {
      if (jdr%2==1) {
          p += c5;
          jdr = jdr - 1;
      }
      c5 = 2*c5;
      jdr = jdr/2;
      oo += jdr;
      oo = oo%6;
  }
}