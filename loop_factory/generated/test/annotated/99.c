int main1(int a,int m,int p,int q){
  int l, i, v;

  l=23;
  i=0;
  v=3;

  
  /*@

    loop invariant l == 23;

    loop invariant 0 <= i && i <= l;

    loop invariant (i == 0) ==> (v == 3);

    loop invariant (i > 0) ==> (v == (l % 9));

    loop invariant a == \at(a, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant v >= 0;

    loop invariant v <= l % 9;

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant (i > 0) ==> (v == l % 9);

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant v == 3 || v == l % 9;

    loop invariant i >= 0;

    loop invariant ((i == 0 && v == 3) || (i > 0 && v == l % 9));

    loop assigns v, i;

  */
  while (i<l) {
      v = v+i;
      v = l%9;
      i = i+1;
  }

}