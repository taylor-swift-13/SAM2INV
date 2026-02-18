int main1(int a,int k,int n,int p){
  int l, i, v, f, t;

  l=32;
  i=0;
  v=a;
  f=a;
  t=1;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant (i == 0) ==> (v == a);

    loop invariant (i > 0) ==> (0 <= v && v <= 6);

    loop invariant l == 32;

    loop invariant i <= l;

    loop invariant 0 <= i;


    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant (i > 0) ==> (0 <= v <= 6);

    loop invariant a == \at(a, Pre);

    loop invariant i >= 0;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v*v+v;
      v = v%7;
      i = i+1;
  }

}