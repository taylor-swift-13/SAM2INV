int main1(){
  int yg, lo, iz, t0w;
  yg=0;
  lo=0;
  iz=0;
  t0w=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t0w + iz == 6;
  loop invariant iz == lo;
  loop invariant t0w >= 0;
  loop invariant yg >= 0;
  loop assigns t0w, yg, iz, lo;
*/
while (t0w>0) {
      t0w -= 1;
      yg = yg+1*1;
      iz = iz+1*1;
      lo = lo+1*1;
      yg = yg*2+2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lo >= 0;
  loop invariant lo <= 6;
  loop invariant yg >= 0;
  loop assigns lo;
*/
for (; lo-1>=0; lo--) {
  }
}