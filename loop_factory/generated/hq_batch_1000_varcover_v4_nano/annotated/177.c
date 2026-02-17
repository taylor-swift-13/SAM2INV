int main1(int b,int n,int q){
  int l, i, v, e, o, s, j, w, d, m;

  l=(n%29)+18;
  i=0;
  v=-3;
  e=-6;
  o=0;
  s=q;
  j=-5;
  w=1;
  d=i;
  m=n;

  
  /*@

    loop invariant o == i;

    loop invariant 2*(e + 6) == i*(i - 1);

    loop invariant i*(i - 1)*(i - 2) == 6*(v + 3 + 6*i);

    loop invariant 0 <= i;

    loop invariant (l < 0) || i <= l;

    loop invariant n == \at(n,Pre) && q == \at(q,Pre) && b == \at(b,Pre);

    loop assigns v, e, o, i;

  */
while (i<l) {
      v = v+e;
      e = e+o;
      o = o+1;
      i = i+1;
  }

}