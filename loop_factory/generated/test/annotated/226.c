int main1(int p){
  int adp, s, t;
  adp=p+25;
  s=adp;
  t=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p,Pre) + adp * (t - \at(p,Pre));
  loop invariant t >= \at(p,Pre);
  loop invariant adp == \at(p,Pre) + 25;
  loop invariant s == adp;
  loop assigns t, p;
*/
while (s>3) {
      t += 1;
      p = p + adp;
  }
}