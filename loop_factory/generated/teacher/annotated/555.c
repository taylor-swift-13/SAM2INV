int main1(int p,int q){
  int e, l, j, v;

  e=q+9;
  l=1;
  j=p;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == q + 9;
  loop invariant 1 <= l;

  loop invariant l >= 1 && (l <= e || e < 1);

  loop invariant j - v + 2*l == p - q + 2;

  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns j, v, l;
*/
while (l<e) {
      j = j+v;
      v = v+v;
      v = v+2;
      l = l+1;
  }

}
