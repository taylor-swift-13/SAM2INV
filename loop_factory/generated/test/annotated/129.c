int main1(int a,int b,int k,int p){
  int l, i, v, u, o;

  l=77;
  i=1;
  v=l;
  u=i;
  o=p;

  
  /*@


    loop invariant v == 77 || v == 1 || v == 2;

    loop invariant a == \at(a, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant l == 77;

    loop invariant i <= 2*l;

    loop invariant 1 <= i;

    loop invariant i > 0;

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant v <= l;

    loop assigns i, v;

  */
  while (i<l) {
      v = v*v+v;
      v = v%5;
      i = i*2;
  }

}