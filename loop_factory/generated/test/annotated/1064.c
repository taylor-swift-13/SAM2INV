int main1(){
  int yp, fxf, yb, soe;
  yp=0;
  fxf=(1%18)+5;
  yb=(1%15)+3;
  soe=fxf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yp == 0;
  loop invariant soe == 6;
  loop invariant fxf >= 0;
  loop invariant yb == fxf - 2;
  loop assigns yb, soe, fxf;
*/
while (1) {
      if (!(fxf!=0)) {
          break;
      }
      yb--;
      soe = soe + yp;
      fxf--;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yb == -2;
  loop invariant fxf >= 0;
  loop invariant yp == -fxf*(fxf - 1);
  loop assigns yp, fxf;
*/
while (fxf-2>=0) {
      yp = yp+yb*fxf;
      fxf = fxf + 1;
  }
}