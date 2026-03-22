int main1(){
  int n, i, tw, g;
  n=1+23;
  i=0;
  tw=n;
  g=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= i;
  loop invariant i <= n;
  loop invariant i % 2 == 0;
  loop invariant g == n * (i/2 + 1);
  loop invariant tw == n;
  loop assigns i, g, tw;
*/
while (i<n) {
      i += 2;
      if (!(!(g<=tw))) {
          tw = g;
      }
      g += n;
  }
}