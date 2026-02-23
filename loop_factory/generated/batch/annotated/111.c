int main1(int k){
  int q, p, c, v;

  q=59;
  p=2;
  c=q;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == p + 57;
  loop invariant p <= q;
  loop invariant k == \at(k, Pre);
  loop invariant c - p == 57;
  loop invariant p >= 2;
  loop invariant q == 59;
  loop invariant c - p == q - 2;
  loop invariant c >= q;
  loop assigns c, p;
*/
while (p<=q-1) {
      c = c+1;
      p = p+1;
  }

}
