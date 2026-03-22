int main1(){
  int ds9, zc5, xcl, xi, n, pqa;
  ds9=0;
  zc5=(1%20)+1;
  xcl=(1%25)+1;
  xi=0;
  n=ds9;
  pqa=ds9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= xi;
  loop invariant zc5 % 2 == 0;
  loop invariant ds9 == 0;
  loop invariant zc5 > 0;
  loop invariant pqa >= 0;
  loop invariant 0 <= xcl <= 2;
  loop invariant 0 <= n;
  loop assigns xi, xcl, zc5, pqa, n;
*/
while (xcl!=0) {
      if (xcl%2==1) {
          xi += zc5;
          xcl--;
      }
      else {
      }
      zc5 = 2*zc5;
      xcl = xcl/2;
      pqa = ((xcl%3)+3)+(pqa*2);
      n = n+(zc5%8);
  }
}