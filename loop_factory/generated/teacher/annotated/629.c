int main1(int p,int q){
  int e, l, j, v, y, m;

  e=13;
  l=1;
  j=-5;
  v=q;
  y=l;
  m=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j <= e;
  loop invariant j >= -5;
  loop invariant (q >= 1) ==> (v <= q);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant y == 1;

  loop invariant (q <= y) ==> (v == q);


  loop invariant e == 13;
  loop invariant v <= q;
  loop invariant 0 <= e - j;
  loop invariant v == q || v == 1;
  loop assigns v, j;
*/
while (1) {
      if (j>=e) {
          break;
      }
      if (y<=v) {
          v = y;
      }
      j = j+1;
  }

}
