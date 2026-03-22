int main1(int p){
  int ky, agn4, tw, lq;
  ky=p;
  agn4=2;
  tw=0;
  lq=agn4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant ky == p;
  loop invariant (lq - 2) >= 0;
  loop invariant ((lq - 2) % 4) == 0;
  loop invariant 0 <= tw;
  loop invariant (ky > 0) ==> (tw < ky/2) ==> (lq == 2);
  loop invariant (ky > 0) ==> (tw >= ky/2) ==> (lq == 2 + 4*(tw - ky/2));
  loop assigns p, tw, lq;
*/
while (tw<ky) {
      if (!(!(tw>=ky/2))) {
          lq += 4;
      }
      tw++;
      p = p+tw-tw;
  }
}