int main1(int l){
  int k, kc, ly;
  k=75;
  kc=0;
  ly=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ly == 0;
  loop invariant l == \at(l, Pre);
  loop invariant kc <= k;
  loop invariant 0 <= kc;
  loop invariant k == 75;
  loop assigns kc, ly, l;
*/
while (kc<k) {
      if (kc%2==0) {
          if (ly>0) {
              ly -= 1;
              ly++;
          }
      }
      else {
          if (ly>0) {
              ly -= 1;
              ly++;
          }
      }
      kc += 1;
      l = l + ly;
  }
}