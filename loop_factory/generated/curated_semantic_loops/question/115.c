int main1(int p,int q){
  int r, t, e, v;

  r=(q%6)+8;
  t=1;
  e=r;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (t<=r-1) {
      e = e+1;
      v = v-1;
      v = v+3;
      t = t+1;
  }
/*@
  assert !(t<=r-1) &&
         (p == \at(p, Pre) && q == \at(q, Pre) && r == (\at(q, Pre) % 6) + 8);
*/

}
