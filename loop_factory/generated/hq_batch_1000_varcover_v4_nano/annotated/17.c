int main1(int a,int b,int m){
  int l, i, v, o, n, c, y;

  l=10;
  i=l;
  v=5;
  o=a;
  n=b;
  c=-8;
  y=i;

  
  /*@

    loop invariant v + i*o == 5 + l*o;

    loop invariant 0 <= i && i <= l;

    loop invariant o == a;

    loop invariant l == 10;

    loop invariant a == \at(a, Pre);

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v+o;
      i = i-1;
  }

}