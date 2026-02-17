int main1(int a,int n,int p){
  int l, i, v, c, b, e, s;

  l=38;
  i=0;
  v=a;
  c=n;
  b=p;
  e=p;
  s=-4;

  
  /*@

    loop invariant v == a + i;

    loop invariant s == -4 + i*(i - 1)/2;

    loop invariant 0 <= i && i <= l;

    loop invariant b == \at(p, Pre) && c == \at(n, Pre);

    loop invariant l == 38;

    loop invariant i == 0 ==> e == b;

    loop invariant i > 0 ==> e == v - 1 + c + b;

    loop assigns e, v, s, i;

    loop variant l - i;

  */
while (i<l) {
      e = v+c+b;
      v = v+1;
      s = s+i;
      i = i+1;
  }

}