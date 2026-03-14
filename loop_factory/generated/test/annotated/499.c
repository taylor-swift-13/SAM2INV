int main1(){
  int oar, l, eqzv, hw5w, m1, fc5, ky;
  oar=1-5;
  l=oar;
  eqzv=0;
  hw5w=(1%28)+10;
  m1=-1;
  fc5=oar;
  ky=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fc5 - eqzv == -4;
  loop invariant eqzv >= 0;
  loop invariant ky - 3*eqzv == -4;
  loop invariant m1 - eqzv*(eqzv+1)/2 == -1;
  loop invariant hw5w == 11 - eqzv*(eqzv-1)/2;
  loop invariant eqzv <= 5;
  loop assigns hw5w, eqzv, m1, ky, fc5;
*/
while (hw5w>eqzv) {
      hw5w -= eqzv;
      eqzv++;
      m1 += eqzv;
      ky = (3)+(ky);
      fc5 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l <= -4;
  loop invariant -5 <= fc5 <= 5;
  loop invariant oar == -4;
  loop invariant fc5 > l;
  loop assigns fc5, l;
*/
while (1) {
      if (!(fc5>l)) {
          break;
      }
      fc5 -= l;
      l = l + 1;
      l = l*2;
      fc5 += l;
      fc5 = fc5%6;
  }
}