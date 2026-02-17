int main1(int n,int p,int q){
  int l, i, v, d, w, y, e;

  l=36;
  i=0;
  v=n;
  d=l;
  w=q;
  y=i;
  e=q;

  
  /*@

    loop invariant v == \at(n, Pre) + 2*i;

    loop invariant w == \at(q, Pre) + 4*i;

    loop invariant 0 <= i && i <= l;

    loop invariant l == 36;

    loop invariant n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop assigns v, w, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+2;
      w = w+4;
      i = i+1;
  }

}