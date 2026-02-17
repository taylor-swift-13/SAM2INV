int main1(int m,int n,int q){
  int l, i, v, f, d, b;

  l=18;
  i=0;
  v=8;
  f=n;
  d=i;
  b=n;

  
  /*@

    loop invariant l == 18;

    loop invariant 0 <= i && i <= l;

    loop invariant (i == 0 ==> v == 8) && (i > 0 ==> 0 <= v && v <= 4);

    loop invariant i > 0 ==> d == b + (i - 1);

    loop invariant m == \at(m,Pre) && n == \at(n,Pre) && q == \at(q,Pre);

    loop assigns b, v, d, i;

    loop variant l - i;

  */
while (i<l) {
      b = b*b+v;
      v = v%5;
      d = b+i;
      i = i+1;
  }

}