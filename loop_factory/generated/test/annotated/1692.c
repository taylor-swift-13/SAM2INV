int main1(){
  int kd, t6, ud, vi;
  kd=1+8;
  t6=3;
  ud=0;
  vi=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (t6 == 3) ==> (ud == 0);
  loop invariant vi == 6 + ((t6 + 2) * (t6 - 3)) / 2;
  loop invariant 3 <= t6 <= kd;
  loop invariant ud >= 0;
  loop invariant kd == 9;
  loop invariant ud <= vi;
  loop assigns ud, vi, t6;
*/
while (1) {
      if (t6<kd/2) {
          ud = ud + vi;
      }
      else {
          ud++;
      }
      vi += t6;
      t6 += 1;
      if (t6>=kd) {
          break;
      }
  }
}