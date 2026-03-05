int main1(){
  int j0u, x2i, k;
  j0u=1+23;
  x2i=j0u;
  k=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x2i == j0u;
  loop invariant (k == 0) || (k == j0u + 1);
  loop invariant j0u == 24;
  loop assigns k;
*/
while (x2i>=1) {
      k = j0u-k;
      k += 1;
  }
}