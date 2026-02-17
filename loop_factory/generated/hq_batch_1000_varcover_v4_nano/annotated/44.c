int main1(int b,int n,int p){
  int l, i, v, d, q, e;

  l=22;
  i=l;
  v=-8;
  d=l;
  q=p;
  e=n;

  
  /*@

    loop invariant v + d == -8 + l;

    loop invariant d == i;

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant p == \at(p,Pre);

    loop invariant n == \at(n,Pre);

    loop assigns v, d, i;

    loop variant i;

  */
while (i>0) {
      v = v+1;
      d = d-1;
      i = i-1;
  }

}