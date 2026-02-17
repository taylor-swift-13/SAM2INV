int main1(int a,int b,int m){
  int l, i, v, u, o;

  l=68;
  i=0;
  v=i;
  u=-5;
  o=i;

  
  /*@

    loop invariant l == 68;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant u == -5;

    loop invariant o == 0;

    loop invariant v == 0;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop assigns u, o, i;

  */
  while (i<l) {
      u = u+o;
      o = o+v;
      o = o+v;
      i = i+1;
  }

}