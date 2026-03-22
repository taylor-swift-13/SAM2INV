int main1(int w,int i){
  int zrt, x4, a8, ji, hh, ufi;
  zrt=i;
  x4=0;
  a8=38;
  ji=0;
  hh=1;
  ufi=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a8 + ji == 38;
  loop invariant hh == x4 + 1;
  loop invariant 0 <= ji <= 38;
  loop invariant hh == x4 + 1 && 0 <= ji && ji <= 38 && 0 <= x4 && 0 <= a8 && (zrt >= 0) ==> (x4 <= zrt);
  loop invariant x4 >= 0;
  loop assigns a8, hh, ji, x4, ufi;
*/
while (1) {
      if (!(a8>0&&x4<zrt)) {
          break;
      }
      if (a8<=hh) {
          ufi = a8;
      }
      else {
          ufi = hh;
      }
      hh++;
      x4++;
      ji += ufi;
      a8 -= ufi;
  }
}