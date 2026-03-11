int main1(int x,int u){
  int j2e, lp, d, sl;
  j2e=(u%10)+10;
  lp=-1;
  d=0;
  sl=j2e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j2e == ((\at(u, Pre) % 10) + 10);
  loop invariant sl == j2e + (lp + 1) * (j2e + 1) - (lp * (lp + 1)) / 2;
  loop invariant -1 <= lp <= j2e;
  loop assigns d, lp, sl;
*/
while (lp<j2e) {
      d = j2e-lp;
      lp++;
      sl += d;
  }
}