int main1(int k,int q){
  int i, v, a, t;

  i=(k%6)+8;
  v=0;
  a=2;
  t=k;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v<=i-1) {
      a = a+2;
      t = t+a;
      t = t+t;
      v = v+1;
  }
/*@
  assert !(v<=i-1) &&
         (k == \at(k, Pre));
*/

}
