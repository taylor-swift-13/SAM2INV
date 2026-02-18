int main1(int k,int n,int p,int q){
  int l, i, v, h, g;

  l=35;
  i=l;
  v=0;
  h=-6;
  g=p;

  
  /*@

    loop invariant v == 0;

    loop invariant h == -6;

    loop invariant 0 <= i;

    loop invariant i <= 35;

    loop invariant l == 35;

    loop invariant (i >= 0) && (i <= l);

    loop invariant (k == \at(k, Pre)) && (n == \at(n, Pre)) && (p == \at(p, Pre)) && (q == \at(q, Pre));

    loop invariant i >= 0;

    loop invariant (k == \at(k, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre));

    loop invariant i >= 0 && i <= 35;

    loop invariant p == \at(p, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre);

    loop invariant 0 <= i <= 35;

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns v, h, i;

  */
  while (i>0) {
      v = v*2;
      h = h+v;
      i = i-1;
  }

}