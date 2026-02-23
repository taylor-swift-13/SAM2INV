int main1(int m,int q){
  int j, k, x;

  j=(m%6)+19;
  k=0;
  x=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(m, Pre) % 6 + 19;
  loop invariant 0 <= k;
  loop invariant k <= j;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant j == ((\at(m,Pre) % 6) + 19);

  loop invariant (k == 0) ==> x == \at(q, Pre);
  loop invariant j == (\at(m, Pre) % 6) + 19;
  loop assigns x, k;
*/
while (k<j) {
      x = x+1;
      x = x+x;
      k = k+1;
  }

}
