int main1(){
  int row, fv, g, wz;
  row=1+17;
  fv=0;
  g=0;
  wz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= fv;
  loop invariant fv <= row;
  loop invariant g == ((fv*(fv+1))/2) + (2 * wz * fv);
  loop invariant row == 1 + 17;
  loop invariant wz == 0;
  loop assigns fv, g;
*/
while (fv < row) {
      fv++;
      g += fv;
      g = g+wz+wz;
  }
}