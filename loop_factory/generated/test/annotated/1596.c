int main1(int a){
  int k, bb, ew, jm, tl, w6, nl7i, kad;
  k=75;
  bb=k;
  ew=16;
  jm=0;
  tl=1;
  w6=0;
  nl7i=a;
  kad=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= bb <= k;
  loop invariant w6 >= 0;
  loop invariant jm >= 0;
  loop invariant kad >= 0;
  loop invariant ew >= 0;
  loop invariant ew <= 16;
  loop invariant tl >= 1;
  loop invariant k == 75;
  loop invariant a - jm == \at(a,Pre);
  loop invariant tl - bb == 1 - k;
  loop invariant w6 <= ew;
  loop invariant w6 <= tl;
  loop assigns ew, bb, tl, w6, jm, kad, nl7i, a;
*/
while (ew>0&&bb<k) {
      if (ew<=tl) {
          w6 = ew;
      }
      else {
          w6 = tl;
      }
      ew = ew - w6;
      tl += 1;
      bb++;
      jm = jm + w6;
      if (kad*kad<=k+5) {
          kad = nl7i*nl7i;
      }
      nl7i += bb;
      a = a + w6;
      nl7i += bb;
  }
}