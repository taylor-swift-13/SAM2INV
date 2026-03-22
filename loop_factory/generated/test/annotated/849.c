int main1(int g){
  int mbtb, a, bw, q0, fc;
  mbtb=g+13;
  a=1;
  bw=a;
  q0=0;
  fc=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mbtb == g + 13;
  loop invariant q0 == 0;
  loop invariant (fc == g || fc == g + 2);
  loop invariant (a == 1 || a == mbtb);
  loop invariant ((a == 1 && q0 == 0 && bw == 1 && fc == g) ||
                    (a == mbtb && q0 == 0 && bw == 4 && fc == g + 2));
  loop invariant (bw == 1) || (bw == 4);
  loop assigns q0, bw, fc, a;
*/
while (a<mbtb) {
      q0 = q0/4;
      bw = bw*4;
      fc += 2;
      a = mbtb;
  }
}