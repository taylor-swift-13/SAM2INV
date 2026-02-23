int main1(int p,int q){
  int i, b, v;

  i=53;
  b=0;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 53;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre) && 0 <= b && b <= i && v >= 1;
  loop invariant (0 <= b) && (b <= i);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant b >= 0 && b <= i;

  loop invariant 0 <= b && b <= i;
  loop invariant 0 <= b;
  loop invariant b <= i;
  loop invariant v >= 1;
  loop invariant v >= 2*b;
  loop assigns b, v;
*/
while (b<i) {
      v = v+v;
      b = b+1;
  }

}
