int main1(){
  int ivfb, k, hy4l, zw, yhs;
  ivfb=185;
  k=0;
  hy4l=23;
  zw=1;
  yhs=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zw == (1 + k);
  loop invariant yhs == k;
  loop invariant (hy4l > 0) ==> (hy4l + (k*(k+1))/2 == 23);
  loop invariant (hy4l == 0) ==> (hy4l + (k*(k+1))/2 >= 23);
  loop invariant 0 <= hy4l <= 23;
  loop invariant 1 <= zw <= ivfb;
  loop invariant hy4l + zw <= 24;
  loop assigns hy4l, zw, k, yhs;
*/
while (hy4l>0&&zw<=ivfb) {
      if (hy4l>zw) {
          hy4l = hy4l - zw;
      }
      else {
          hy4l = 0;
      }
      zw++;
      k += 1;
      yhs++;
  }
}