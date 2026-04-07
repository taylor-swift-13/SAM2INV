int main1(){
  int w, gb, mcnf, ild, hul;
  w=1;
  gb=0;
  mcnf=1;
  ild=6;
  hul=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= hul;
  loop invariant hul <= w + 1;
  loop invariant mcnf == hul*hul + 5*hul + 1;
  loop invariant ild == 6 + 2*hul;
  loop invariant gb == ((hul - 1) * hul * (2 * hul - 1)) / 6
                          + (5 * (hul - 1) * hul) / 2
                          + hul;
  loop invariant gb == (hul*hul*hul + 6*hul*hul - 4*hul) / 3;
  loop assigns gb, hul, mcnf, ild;
*/
while (1) {
      if (!(hul<=w)) {
          break;
      }
      gb += mcnf;
      hul += 1;
      mcnf = mcnf + ild;
      ild += 2;
  }
}