int main1(int a,int q){
  int c, j, t, e;

  c=20;
  j=0;
  t=3;
  e=q;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (1) {
      if (j>=c) {
          break;
      }
      t = t+3;
      j = j+1;
      t = t+1;
      e = e-1;
      if ((j%5)==0) {
          e = e+1;
      }
  }
/*@
  assert (t == 3 + 4*j);
*/

  int __aux_1=0;
  while (__aux_1 < 3) { __aux_1 = __aux_1 + 1; }
}
