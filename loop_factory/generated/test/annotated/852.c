int main1(int v){
  int pmj, t, rw1;
  pmj=72;
  t=0;
  rw1=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - \at(v,Pre) == 72 - pmj;
  loop invariant t == 0;
  loop invariant v == \at(v, Pre) + 72 * rw1;
  loop invariant 0 <= rw1;
  loop invariant rw1 <= 1;
  loop invariant (pmj == t) <==> (rw1 == 1);
  loop invariant pmj >= t;
  loop assigns rw1, v, pmj;
*/
while (t+1<=pmj) {
      rw1 = rw1 + 1;
      v = v + pmj;
      pmj = (t+1)-1;
  }
}