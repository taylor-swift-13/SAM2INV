int main1(int b,int k){
  int m, u, v, a;

  m=(k%34)+12;
  u=1;
  v=8;
  a=b;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u*2<=m) {
      v = v*v+v;
      v = v%9;
      a = a*v;
      v = v%7;
      u = u*2;
  }
/*@
  assert !(u*2<=m) &&
         (m == (k%34) + 12);
*/

}
