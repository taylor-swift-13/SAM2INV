int main1(int j,int s){
  int dk, y3, deie, y9, c, yh;
  dk=s-3;
  y3=0;
  deie=0;
  y9=0;
  c=(s%18)+5;
  yh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant deie >= 0;
  loop invariant y3 == j*j * (((\at(s, Pre) % 18) + 5) - c);
  loop invariant 0 <= y3;
  loop assigns c, y3, deie, y9, s;
*/
while (1) {
      if (!(c>0)) {
          break;
      }
      c--;
      y3 = y3+j*j;
      deie = deie+s*s;
      y9 = y9+j*s;
      s = s*2+(deie%4)+1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yh >= 0;
  loop invariant (dk < 0) || (0 <= yh && yh <= dk);
  loop assigns yh;
*/
while (1) {
      if (!(yh+1<=dk)) {
          break;
      }
      yh = yh + 1;
  }
}