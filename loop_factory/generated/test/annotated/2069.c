int main1(int b){
  int do2, c3e, kqt, rt;
  do2=19;
  c3e=0;
  kqt=0;
  rt=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (kqt == ((c3e * \at(b, Pre)) % do2));
  loop invariant (rt == (1 + (c3e * (c3e + 1)) / 2));
  loop invariant (0 <= c3e && c3e <= do2);
  loop invariant do2 == 19;
  loop invariant 2 * (rt - 1) == c3e * (c3e + 1);
  loop assigns kqt, c3e, rt;
*/
while (1) {
      if (!(c3e < do2)) {
          break;
      }
      kqt = (kqt + b) % do2;
      c3e += 1;
      rt = rt + c3e;
  }
}