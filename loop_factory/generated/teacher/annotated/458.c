int main1(int m,int q){
  int j, k, x;

  j=(m%6)+19;
  k=1;
  x=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == (\at(m,Pre) % 6) + 19;
  loop invariant k == 1;
  loop invariant m == \at(m,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant 7 <= j;
  loop invariant j == (m % 6) + 19;
  loop invariant j == ((\at(m, Pre) % 6) + 19);
  loop invariant j >= 7;
  loop invariant (q + 18) * (x + 18) >= 0;

  loop invariant (q == -18) ==> (x == -18);
  loop assigns x;
*/
while (1) {
      x = x+3;
      x = x+6;
      if (k+7<=k+j) {
          x = x+x;
      }
  }

}
