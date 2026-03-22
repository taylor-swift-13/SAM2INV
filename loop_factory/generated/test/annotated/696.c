int main1(){
  int yf, s3, kh, f10, b;
  yf=0;
  s3=0;
  kh=0;
  f10=(1%18)+5;
  b=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s3 == yf;
  loop invariant b == -5 + s3*(s3+1)/2;
  loop invariant f10 == 6 - s3;
  loop invariant 0 <= s3;
  loop invariant s3 <= 6;
  loop invariant yf == kh;
  loop assigns yf, s3, kh, f10, b;
*/
while (f10>0) {
      s3 = s3+1*1;
      yf = yf+1*1;
      kh = kh+1*1;
      f10 -= 1;
      b += s3;
  }
}