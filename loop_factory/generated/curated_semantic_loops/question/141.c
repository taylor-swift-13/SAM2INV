int main1(int p,int q){
  int i, f, n;

  i=(q%7)+14;
  f=0;
  n=p;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (f<i) {
      n = n*2;
      n = n*n;
      f = f+1;
  }
/*@
  assert !(f<i) &&
         (i == ((\at(q, Pre) % 7) + 14));
*/

}
