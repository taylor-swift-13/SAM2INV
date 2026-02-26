int main1(int m,int q){
  int j, k, x;

  j=(m%6)+19;
  k=0;
  x=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == (m % 6) + 19;
  loop invariant x == q + 8*k;
  loop invariant 0 <= k;
  loop invariant k <= j;
  loop invariant x == \at(q, Pre) + 8*k;
  loop invariant j == \at(m, Pre) % 6 + 19;
  loop invariant x <= \at(q, Pre) + 8*j;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= k <= j;
  loop invariant x >= q;
  loop assigns x, k;
*/
while (k<j) {
      x = x+5;
      x = x+3;
      k = k+1;
  }

}
