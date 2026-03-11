int main1(int a,int m){
  int r, k, v;

  r=10;
  k=3;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (k<=r-5) {
      v = v%9;
      v = v*v;
      k = k+5;
  }
/*@
  assert !(k<=r-5) &&
         (a == \at(a, Pre));
*/

}
