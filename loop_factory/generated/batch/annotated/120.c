int main1(int k){
  int u, q, j;

  u=(k%6)+4;
  q=u;
  j=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == ((\at(k, Pre) % 6) + 4);
  loop invariant (q % 2) == (((\at(k, Pre) % 6) + 4) % 2);

  loop invariant (u >= 6) ==> j == 2*(\at(k, Pre) % 6 + 4) - q &&
                   (u < 6)  ==> j == (\at(k, Pre) % 6 + 4) + ((\at(k, Pre) % 6 + 4 - q)/2);

  loop invariant q <= \at(k, Pre) % 6 + 4;
  loop invariant j >= q;

  loop invariant u == (\at(k, Pre) % 6) + 4;
  loop invariant k == \at(k, Pre);

  loop assigns j, q;
*/
while (q-2>=0) {
      j = j+1;
      if (q+6<=q+u) {
          j = j+1;
      }
      q = q-2;
  }

}
