int main1(int n,int p){
  int x, u, w;

  x=65;
  u=x;
  w=p;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (u>0) {
      w = w+3;
      if (u+2<=n+x) {
          w = w+5;
      }
  }
/*@
  assert !(u>0) &&
         (u == 65);
*/

}
