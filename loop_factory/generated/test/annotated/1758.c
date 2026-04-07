int main1(int h){
  int gr, teu, d, yfdd, cgix;
  gr=77;
  teu=0;
  d=-5;
  yfdd=h;
  cgix=h+1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (teu < gr) ==> (teu == 0 && d == -5 && yfdd == h && cgix == h+1);
  loop invariant (teu == gr) ==> (yfdd == (2*h + 1) && cgix == (2*h + 1) && d == (4*h - 3));
  loop invariant 0 <= teu <= gr;
  loop assigns yfdd, cgix, d, teu;
*/
while (teu < gr) {
      yfdd = yfdd + cgix;
      cgix += h;
      d = d+yfdd+cgix;
      teu = gr;
  }
}