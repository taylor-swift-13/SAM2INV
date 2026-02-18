int main1(int b,int n,int p,int q){
  int l, i, v;

  l=p+4;
  i=0;
  v=l;

  
  /*@

    loop invariant l == p + 4 &&
                   i <= l &&
                   i >= 0 &&
                   (i == 0) ==> (v == l) &&
                   (i >= 1) ==> (v == 0);

    loop invariant i >= 0;


    loop invariant (i == 0) ==> (v == l);

    loop invariant (i > 0) ==> (v == 0);

    loop invariant l == \at(p, Pre) + 4;

    loop invariant l == p + 4;

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant (i == 0 && v == l) || (i > 0 && v == 0);


    loop invariant p == \at(p, Pre) && q == \at(q, Pre) && n == \at(n, Pre) && b == \at(b, Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v-v;
      i = i+1;
  }

}