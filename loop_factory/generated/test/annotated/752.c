int main1(){
  int za, j1jx, w5, af4, it3t, m3s, bg;
  za=1+19;
  j1jx=za+4;
  w5=(1%20)+1;
  af4=(1%25)+1;
  it3t=0;
  m3s=0;
  bg=j1jx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant af4 >= 0;
  loop invariant af4 <= 2;
  loop invariant w5 % 2 == 0;
  loop invariant za == 1 + 19;
  loop invariant j1jx == za + 4;
  loop invariant it3t >= 0;
  loop invariant m3s == j1jx * (2 - af4);
  loop invariant bg >= j1jx;
  loop invariant w5 >= 2;
  loop assigns af4, bg, it3t, m3s, w5;
*/
while (af4!=0) {
      if (af4%2==1) {
          it3t += w5;
          af4 = af4 - 1;
      }
      else {
      }
      w5 = 2*w5;
      af4 = af4/2;
      m3s = (j1jx)+(m3s);
      bg = bg + af4;
  }
}