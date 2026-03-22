int main1(int j){
  int tgk, yi, n5f, b7, fir;
  tgk=48;
  yi=0;
  n5f=1;
  b7=1;
  fir=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n5f == (yi + 1) * (yi + 1);
  loop invariant b7 == 2 * yi + 1;
  loop invariant j == \at(j, Pre) + yi;
  loop invariant fir == \at(j, Pre) + ((yi+1)*(yi+2)*(2*yi+3))/3 - 2;
  loop invariant tgk == 48;
  loop invariant yi >= 0;
  loop assigns yi, b7, n5f, fir, j;
*/
while (1) {
      if (!(n5f<=tgk)) {
          break;
      }
      yi++;
      b7 += 2;
      n5f = n5f + b7;
      fir = fir+n5f+n5f;
      j++;
  }
}