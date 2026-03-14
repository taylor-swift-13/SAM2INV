int main1(){
  int c4, hhwd, im, pvy, x5;
  c4=61;
  hhwd=c4;
  im=1;
  pvy=0;
  x5=hhwd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c4 == 61;
  loop invariant 1 <= im;
  loop invariant im <= c4 + 1;
  loop invariant pvy == (im - 1) * (im - 1);
  loop invariant x5 == 60 + ((im * (im + 1)) / 2);
  loop assigns pvy, im, x5;
*/
while (im<=c4) {
      pvy = pvy+2*im-1;
      im++;
      x5 += im;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hhwd == 61;
  loop invariant pvy - hhwd * ((62 - im) / 5) == 3721;
  loop invariant im <= c4 + 1;
  loop invariant c4 == 61;
  loop invariant im % 5 == 2;
  loop assigns pvy, im;
*/
for (; im>4; im = im - 5) {
      pvy = pvy + hhwd;
  }
}