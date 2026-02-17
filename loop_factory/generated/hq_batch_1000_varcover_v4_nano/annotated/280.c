int main1(int a,int k,int p,int q){
  int l, i, v, y, g, o;

  l=8;
  i=l;
  v=i;
  y=4;
  g=k;
  o=a;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant (y == v * v) || (i == l);

    loop invariant a == \at(a,Pre) && k == \at(k,Pre) && p == \at(p,Pre) && q == \at(q,Pre);

    loop assigns v, y, i;

    loop variant i;

  */
while (i>0) {
      v = v*4;
      y = y/4;
      y = v*v;
      i = i-1;
  }

}