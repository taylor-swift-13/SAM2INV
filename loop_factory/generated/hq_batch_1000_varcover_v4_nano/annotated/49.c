int main1(int a,int m,int q){
  int l, i, v, o, u, h;

  l=46;
  i=0;
  v=0;
  o=m;
  u=-8;
  h=m;

  
  /*@

    loop invariant v == 0;

    loop invariant 0 <= i && i <= l;

    loop invariant l == 46;

    loop invariant a == \at(a, Pre) && m == \at(m, Pre) && q == \at(q, Pre);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v*3;
      i = i+1;
  }

}