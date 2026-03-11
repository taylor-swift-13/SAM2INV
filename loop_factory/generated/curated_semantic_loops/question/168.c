int main1(int n,int p){
  int w, y, v, r;

  w=n-10;
  y=0;
  v=4;
  r=y;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v!=0&&r!=0) {
      if (v>r) {
          v = v-r;
      }
      else {
          r = r-v;
      }
  }
/*@
  assert !(v!=0&&r!=0) &&
         (n == \at(n, Pre) && p == \at(p, Pre) && v >= 0);
*/

}
