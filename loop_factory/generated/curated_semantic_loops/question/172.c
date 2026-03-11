int main1(int k,int m){
  int q, u, h, o;

  q=(k%10)+9;
  u=0;
  h=q;
  o=0;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (h!=0&&o!=0) {
      if (h>o) {
          h = h-o;
      }
      else {
          o = o-h;
      }
  }
/*@
  assert !(h!=0&&o!=0) &&
         (h >= 0);
*/

}
