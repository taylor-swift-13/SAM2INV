int main1(int k,int n,int q){
  int l, i, v, t, a, p, b;

  l=q-4;
  i=0;
  v=n;
  t=0;
  a=-2;
  p=i;
  b=l;

  
  /*@

    loop invariant i >= 0;

    loop invariant (l <= 0) || i <= l;

    loop invariant v == \at(n, Pre) + i*(i-1)/2;

    loop invariant t == 0;

    loop invariant k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre);

    loop assigns v, t, i;

  */
while (i<l) {
      v = v+i;
      t = t*t;
      i = i+1;
  }

}