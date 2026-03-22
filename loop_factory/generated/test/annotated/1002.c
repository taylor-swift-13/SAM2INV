int main1(int t,int p){
  int g, wz, l60k, l, o;
  g=18;
  wz=0;
  l60k=10;
  l=1;
  o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= l60k <= 10;
  loop invariant o == wz && (l60k > 0 ==> l <= g);
  loop invariant wz == l - 1;
  loop invariant l60k == 0 || l60k == 10 - ((l - 1) * l) / 2;
  loop assigns l60k, l, wz, o;
*/
while (1) {
      if (!(l60k>0&&l<=g)) {
          break;
      }
      if (l60k>l) {
          l60k -= l;
      }
      else {
          l60k = 0;
      }
      l = l + 1;
      wz++;
      o = o + 1;
  }
}