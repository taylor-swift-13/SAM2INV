int main1(int k,int q){
  int y, c, m, i;

  y=k-6;
  c=0;
  m=6;
  i=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((i == 8 && m == 6) || (i == m - 1));
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant y == \at(k, Pre) - 6;
  loop invariant m >= 6;
  loop invariant (m == i - 2) || (m == i + 1);
  loop invariant i >= m - 1;
  loop invariant i <= m + 2;
  loop invariant c == 0;
  loop invariant y == k - 6;
  loop invariant i != m;
  loop invariant i >= m - 2;
  loop assigns i, m;
*/
while (c+1<=y) {
      i = m;
      m = m+1;
  }

}
