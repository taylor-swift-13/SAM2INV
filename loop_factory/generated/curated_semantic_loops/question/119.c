int main1(int a,int n){
  int m, v, w, x;

  m=(a%11)+14;
  v=m+4;
  w=-2;
  x=2;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v>=m+1) {
      w = w*4;
      v = v-2;
  }
/*@
  assert !(v>=m+1) &&
         (m == (a % 11) + 14 && a == \at(a, Pre) && n == \at(n, Pre) && ((v - m) % 2 == 0) && (0 <= (v - m)) && ((v - m) <= 4) && (w <= -2));
*/

}
