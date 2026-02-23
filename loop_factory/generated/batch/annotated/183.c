int main1(int k,int q){
  int b, i, v, y;

  b=k;
  i=0;
  v=4;
  y=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant b == \at(k, Pre);
  loop invariant y == \at(k, Pre);
  loop invariant 0 <= i && (i <= b || b < 0);
  loop invariant v == 4 + i*(2*y + 1);

  loop invariant i >= 0;

  loop invariant b == k;
  loop invariant y == k;
  loop invariant 0 <= i;
  loop assigns i, v;
*/
while (i<=b-1) {
      v = v+y+y;
      v = v+1;
      i = i+1;
  }

}
