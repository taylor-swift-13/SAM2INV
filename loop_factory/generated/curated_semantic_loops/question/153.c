int main1(int b,int k,int m,int p){
  int h, u, v, e;

  h=p+22;
  u=0;
  v=p;
  e=m;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v<h) {
      if (v<h) {
          v = v+1;
      }
      v = v+1;
  }
/*@
  assert !(v<h) &&
         (h == p + 22);
*/

}
