int main1(int a,int k,int m,int q){
  int l, i, v, w, u;

  l=18;
  i=0;
  v=q;
  w=8;
  u=l;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant l == 18;

    loop invariant w == 8 && u == 18;

    loop invariant v == \at(q, Pre) + i * (w + u);

    loop invariant w == 8;

    loop invariant u == l;

    loop invariant v == q + 26*i;

    loop invariant 0 <= i <= l;

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && q == \at(q, Pre);

    loop invariant i >= 0;

    loop invariant v == q + i*(w+u);

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant v == \at(q, Pre) + i*(w + u);

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+w+u;
      i = i+1;
  }

}