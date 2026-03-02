int main1(int b,int q){
  int u, j, c;

  u=b+12;
  j=0;
  c=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant u == b + 12;
  loop invariant c >= q;
  loop invariant u == \at(b, Pre) + 12;
  loop invariant c >= \at(q, Pre);
  loop invariant q == \at(q, Pre) && b == \at(b, Pre) && u == b + 12;
  loop invariant c >= 0 || c == q;
  loop assigns c;
*/
while (1) {
      c = c+4;
      c = c*c+c;
  }

}
