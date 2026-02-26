int main1(int b,int p){
  int l, i, y, q;

  l=b+19;
  i=0;
  y=p;
  q=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (y == p + i);
  loop invariant (l == b + 19);
  loop invariant (b == \at(b, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant (q == b + 4*i);
  loop invariant (i >= 0);
  loop invariant q - 4*i == b;
  loop invariant y - i == p;
  loop invariant l == b + 19;
  loop invariant i >= 0;
  loop invariant y == p + i;
  loop invariant q == b + 4*i;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop assigns y, q, i;
*/
while (1) {
      y = y+1;
      q = q+4;
      i = i+1;
  }

}
