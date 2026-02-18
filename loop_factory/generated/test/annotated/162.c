int main1(int b,int k,int p,int q){
  int l, i, v, a;

  l=(k%12)+15;
  i=0;
  v=p;
  a=q;

  /*>>> LOOP INVARIANT TO FILL <<<*/
    /*@
    loop invariant i <= l;
    loop invariant l == (k % 12) + 15;
    loop invariant v == p + 2*a*i;
    loop invariant a == q;
    loop invariant i >= 0;
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant l == (k%12) + 15;
    loop invariant 0 <= i && i <= l;
    loop assigns i, v;
  */
  while (i<l) {
      v = v+a+a;
      i = i+1;
  }

}