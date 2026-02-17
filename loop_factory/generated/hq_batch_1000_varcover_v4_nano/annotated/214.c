int main1(int m,int n,int q){
  int l, i, v, g, d, w, h, k, c;

  l=m;
  i=0;
  v=i;
  g=i;
  d=-1;
  w=n;
  h=n;
  k=-1;
  c=q;

  
  /*@

    loop invariant l == \at(m,Pre);

    loop invariant 0 <= i;

    loop invariant l < 0 || i <= l;

    loop invariant v >= 0;

    loop invariant g >= 0;

    loop invariant v % 3 == 0 && g % 3 == 0;

    loop assigns v, g, i;

    loop variant l - i;

  */
while (i<l) {
      v = v*3+3;
      g = g*v+3;
      i = i+1;
  }

}