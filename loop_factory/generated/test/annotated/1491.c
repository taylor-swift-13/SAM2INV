int main1(int b){
  int g2, n, zm, jxm;
  g2=50;
  n=0;
  zm=0;
  jxm=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= 0;
  loop invariant n <= g2;
  loop invariant zm * (b - 1) == b * (jxm - 1);
  loop assigns n, jxm, zm;
*/
while (n < g2) {
      jxm = jxm*b;
      n += 1;
      zm = zm + jxm;
  }
}