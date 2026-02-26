int main1(int p,int q){
  int y, l, v;

  y=17;
  l=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 17;
  loop invariant 0 <= l;
  loop invariant l <= y;
  loop invariant v == 0;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant l >= 0;
  loop invariant 0 <= l <= y;
  loop assigns v, l;
*/
while (l<=y-1) {
      v = v*v+v;
      l = l+1;
  }

}
