int main1(){
  int e4, b, np0, ltzw, rt;
  e4=1;
  b=0;
  np0=0;
  ltzw=e4;
  rt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rt == 0;
  loop invariant np0 == 0;
  loop invariant 0 <= b;
  loop invariant b <= e4;
  loop invariant ltzw == 1 + (b*(b+1))/2;
  loop invariant ltzw == e4 + (b*(b+1))/2;
  loop assigns b, np0, rt, ltzw;
*/
while (1) {
      if (!(b < e4)) {
          break;
      }
      b += 1;
      np0 += rt;
      rt += np0;
      ltzw += b;
  }
}