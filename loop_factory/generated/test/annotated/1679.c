int main1(){
  int ofj, gj, rbz, g;
  ofj=32;
  gj=0;
  rbz=-6;
  g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gj >= 0;
  loop invariant gj <= ofj;
  loop invariant rbz == -6 + ofj * gj;
  loop invariant g == gj % 2;
  loop assigns gj, rbz, g;
*/
while (gj < ofj) {
      gj += 1;
      rbz = rbz + ofj;
      g = (1)+(-(g));
  }
}