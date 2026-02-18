int main1(int k,int m,int p,int q){
  int l, i, v, y;

  l=28;
  i=0;
  v=-1;
  y=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == -1 + 2*y*i;
    loop invariant i <= l;
    loop invariant l == 28;
    loop invariant y == 0;
    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop invariant 0 <= i <= l;
    loop invariant v == -1;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == -1 + 2*i*y;
    loop invariant 0 <= i && i <= l;
    loop assigns i, v;
    loop variant l - i;
  */
while (i<l) {
      v = v+y+y;
      i = i+1;
  }

}