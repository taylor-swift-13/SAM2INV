int main1(int a,int k){
  int r, u, i, o, v;

  r=(k%8)+14;
  u=r;
  i=r;
  o=-5;
  v=3;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u>0) {
      i = i+2;
      o = o+i;
      u = u-1;
  }
/*@
  assert !(u>0) &&
         (i == 3*r - 2*u);
*/

}
