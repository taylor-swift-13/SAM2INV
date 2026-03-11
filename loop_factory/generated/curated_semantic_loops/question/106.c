int main1(int a,int k){
  int r, g, d;

  r=(k%14)+14;
  g=r;
  d=k;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (g>0) {
      d = d*2;
      d = d*d;
      g = g-1;
  }
/*@
  assert !(g>0) &&
         (r == (\at(k, Pre) % 14) + 14);
*/

}
