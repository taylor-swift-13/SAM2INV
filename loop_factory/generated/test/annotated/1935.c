int main1(){
  int rq, af99, sfq, wd9, zdv;
  rq=1+17;
  af99=0;
  sfq=0;
  wd9=rq;
  zdv=rq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= af99;
  loop invariant af99 <= rq;
  loop invariant zdv == rq;
  loop invariant sfq >= 0;
  loop invariant (wd9 - sfq) >= zdv;
  loop invariant wd9 >= (af99 + 1) * zdv;
  loop invariant rq > 0;
  loop assigns af99, sfq, wd9;
*/
while (af99 < rq) {
      sfq = sfq + wd9*zdv;
      af99++;
      wd9 += sfq;
  }
}