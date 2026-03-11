int main1(int i,int d){
  int lnb, hr, g, uio, q1;
  lnb=67;
  hr=0;
  g=28;
  uio=1;
  q1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (q1 == (uio - 1));
  loop invariant (hr == q1);
  loop invariant ((-lnb) <= g && g <= 28);
  loop invariant (0 <= q1 && q1 <= lnb);
  loop invariant g <= lnb;
  loop assigns g, uio, hr, q1;
*/
while (g>0&&uio<=lnb) {
      if (!(g<=uio)) {
          g = 0;
      }
      else {
          g = g - uio;
      }
      uio = uio + 1;
      hr += 1;
      q1 = q1 + 1;
  }
}