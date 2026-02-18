int main1(int a,int b,int m,int p){
  int l, i, v, c;

  l=25;
  i=0;
  v=8;
  c=a;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == 8 + 2*i*c;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant v == 8 + 2 * a * i;

    loop invariant c == a;

    loop invariant l == 25;

    loop invariant i >= 0;

    loop invariant v == 8 + 2*c*i;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+c+c;
      i = i+1;
  }

}