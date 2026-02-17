int main1(int b,int m,int p){
  int l, i, v, n, w, f, u, e;

  l=61;
  i=0;
  v=b;
  n=b;
  w=m;
  f=i;
  u=0;
  e=b;

  
  /*@

    loop invariant v == b + i*(i-1)/2;

    loop invariant 0 <= i && i <= l;

    loop invariant b == \at(b, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+i;
      i = i+1;
  }

}