int main1(int a,int b,int q){
  int l, i, v, y;

  l=80;
  i=l;
  v=l;
  y=3;

  
  /*@

    loop invariant v == 3*l - 2*i;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant y == 3;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && q == \at(q, Pre);

    loop invariant l == 80;

    loop assigns v, i, y;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      y = y-1;
      v = v+1;
      y = y+1;
      if (v+4<l) {
          y = y+i;
      }
      i = i-1;
  }

}