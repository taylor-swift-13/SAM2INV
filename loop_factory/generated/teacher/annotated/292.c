int main1(int p,int q){
  int y, l, v;

  y=17;
  l=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= l;
  loop invariant l <= y;
  loop invariant 0 <= v;
  loop invariant v <= y - 6;
  loop invariant v <= l;
  loop invariant (y >= 6) ==> (v <= y - 6);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= l <= y;
  loop invariant y == 17;
  loop invariant (l <= y-6) ==> (v == l);
  loop invariant l >= v;
  loop assigns v, l;
*/
while (l<=y-1) {
      if (v+6<y) {
          v = v+1;
      }
      l = l+1;
  }

}
