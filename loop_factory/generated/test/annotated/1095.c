int main1(int v){
  int an, bku, d7, mr, sh, y72, r;
  an=17;
  bku=0;
  d7=0;
  mr=0;
  sh=-6;
  y72=bku;
  r=an;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mr == d7*(d7-1)/2;
  loop invariant sh == -6 + an * d7;
  loop invariant r == an * (1 + d7*(d7+1)/2) - 6 * d7;
  loop invariant 0 <= d7 <= an;
  loop invariant y72 == d7 * (bku + an)
                       + (sh - (d7 - 1) * an) * (d7 * (d7 - 1) / 2)
                       + an * (d7 * (d7 - 1) * (d7 - 2) / 6);
  loop invariant y72 >= 0;
  loop invariant y72 == bku + d7*(an + bku) + an*(d7*(d7-1)*(d7+1))/6 - 3*d7*d7 + 3*d7;
  loop assigns mr, d7, sh, y72, r;
*/
while (d7<an) {
      mr = mr + d7;
      d7 += 1;
      sh = sh + an;
      y72 += r;
      r = r + sh;
      y72 += bku;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y72 >= 0;
  loop assigns y72;
*/
while (1) {
      y72++;
      if (y72>=an) {
          break;
      }
  }
}