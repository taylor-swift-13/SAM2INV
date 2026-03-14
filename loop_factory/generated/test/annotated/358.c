int main1(){
  int ka, v5, w8, hbf, lev;
  ka=1;
  v5=0;
  w8=(1%28)+10;
  hbf=ka;
  lev=1*4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ka == 1;
  loop invariant v5 >= 0;
  loop invariant w8 > 0;
  loop invariant hbf >= 1;
  loop invariant lev >= 1;
  loop invariant hbf % 3 == 1;
  loop assigns w8, v5, hbf, lev;
*/
while (w8>v5) {
      w8 = w8 - v5;
      v5 = v5 + 1;
      hbf = hbf + w8;
      hbf = hbf*3+1;
      lev = (1)+(lev*hbf);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ka == 1;
  loop invariant w8 >= 0;
  loop assigns w8;
*/
for (; w8-1>=0; w8 -= 1) {
  }
}