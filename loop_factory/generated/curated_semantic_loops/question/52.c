int main1(int k){
  int u, q, j;

  u=(k%6)+4;
  q=u;
  j=q;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (q-2>=0) {
      j = j+1;
      if (q+6<=q+u) {
          j = j+1;
      }
      q = q-2;
  }
/*@
  assert (u == (\at(k, Pre) % 6) + 4) &&
         (q <= 1) &&
         ((q % 2) == (u % 2)) &&
         (j >= q);
*/

}
