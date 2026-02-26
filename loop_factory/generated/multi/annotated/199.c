int main1(int p,int q){
  int i, b, v;

  i=53;
  b=0;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (b <= i) && (0 <= b) && (v == -1 || v == 0);
  loop invariant (p == \at(p, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant b <= i;
  loop invariant v >= -1;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= b;
  loop invariant i == 53;
  loop invariant -1 <= v;
  loop assigns b, v;
*/
while (b<=i-1) {
      v = v*v+v;
      if (b+4<=v+i) {
          v = v*2;
      }
      b = b+1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant (p == \at(p, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant v <= i;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v >= -1;
  loop invariant i == 53;

  loop assigns v;
*/
while (v+1<=i) {
      v = v+1;
  }

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= v);
  loop invariant (v <= i);
  loop invariant (p == \at(p, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v >= 0;
  loop invariant v <= i;
  loop invariant i == 53;
  loop invariant 0 <= v;
  loop assigns v;
*/
while (v-1>=0) {
      v = v-1;
  }

}
