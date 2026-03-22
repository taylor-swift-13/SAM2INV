int main1(){
  int wev1, ducw, w1n, yc, m4, tcu, auk;
  wev1=1;
  ducw=0;
  w1n=0;
  yc=wev1;
  m4=wev1;
  tcu=0;
  auk=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w1n <= wev1;
  loop invariant tcu == 2*w1n;
  loop invariant m4 == 1 + w1n*w1n;
  loop invariant auk == -8 + w1n*(w1n+1)/2;
  loop invariant ducw == w1n;
  loop invariant yc == wev1;
  loop invariant tcu == (yc + 1) * w1n;
  loop invariant m4 == wev1 + w1n * w1n;
  loop invariant m4 == wev1 + (1 + yc) * w1n * (w1n - 1) / 2 + w1n;
  loop assigns tcu, ducw, w1n, m4, auk;
*/
while (w1n<wev1) {
      tcu += 1;
      ducw = ducw + 1;
      w1n += 1;
      m4 += tcu;
      auk += w1n;
      tcu += yc;
  }
}