int main1(){
  int k, h, odhw, mv, x550;
  k=28;
  h=0;
  odhw=h;
  mv=0;
  x550=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mv % k == 0;
  loop invariant odhw == 0;
  loop invariant 0 <= h;
  loop invariant x550 == 8;
  loop invariant mv >= 0;
  loop invariant k - h >= 0;
  loop assigns h, x550, mv;
*/
while (1) {
      if (!(h < k)) {
          break;
      }
      h += 1;
      x550 += odhw;
      mv = mv + k;
      mv = mv + mv;
  }
}