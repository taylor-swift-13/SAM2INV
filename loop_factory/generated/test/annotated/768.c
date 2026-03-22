int main1(){
  int iv, xmu, ht, xsf, c;
  iv=(1%28)+8;
  xmu=(1%22)+5;
  ht=0;
  xsf=0;
  c=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iv > 0;
  loop invariant xsf == 0;
  loop invariant 0 <= xmu;
  loop invariant ht >= 0;
  loop invariant c >= 2;
  loop invariant c == 2*iv - 16;
  loop invariant xmu <= 6;
  loop invariant ht <= c - 2;
  loop assigns ht, xmu, iv, c, xsf;
*/
while (xmu!=0) {
      if (xmu%2==1) {
          ht = ht + iv;
          xmu -= 1;
      }
      xmu = xmu/2;
      iv = 2*iv;
      c = c + iv;
      xsf = xsf*3;
  }
}